/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Fourier.WeightedMaximal.Doubling
public import CKMA.Analysis.Fourier.WeightedMaximal.MeasurableMaximal
public import TauCeti.MeasureTheory.Covering.Vitali
public import TauCeti.MeasureTheory.Integral.Marcinkiewicz.Basic

import Mathlib.Analysis.Normed.Group.Real

/-!
# Sufficiency of the Muckenhoupt condition

An `A_p` bound makes the weight and its dual double. The centred maximal operator of each
weighted measure is therefore weak type `(1,1)` on its own measure, and Marcinkiewicz
interpolation promotes that bound to strong type `(q,q)`. Lerner’s comparison then moves the
unweighted maximal function of `f` onto these two operators.

Source: GAPS 27.44. The comparison follows Lerner, Proc. Amer. Math. Soc. 136 (2008), with the
outer exponent `1/(p-1)` required by the ball form of the `A_p` characteristic.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Metric Set ENNReal Filter
open scoped ENNReal Topology

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

namespace ApWeight

variable {p : ℝ}

/-- Weak-`(1,1)` constant `W.A * ENNReal.ofReal ((5 : ℝ) ^ d) ^ p` of the weight.
The Vitali factor `(5 : ℝ) ^ d` is raised to the outer power `p`. -/
@[expose]
def weakConst (W : ApWeight (d := d) p) : ℝ≥0∞ :=
  W.A * ENNReal.ofReal ((5 : ℝ) ^ d) ^ p

/-- Weak-`(1,1)` constant of the dual weight. -/
@[expose]
def dualWeakConst (W : ApWeight (d := d) p) : ℝ≥0∞ :=
  W.A ^ (p - 1)⁻¹ * ENNReal.ofReal ((5 : ℝ) ^ d) ^ W.conj

/-- The weight weak constant is finite. -/
lemma weakConst_ne_top (W : ApWeight (d := d) p) : W.weakConst ≠ ∞ := by
  unfold weakConst
  exact mul_ne_top W.A_ne_top (rpow_ne_top_of_nonneg W.p_pos.le ENNReal.ofReal_ne_top)

/-- The dual weak constant is finite. -/
lemma dualWeakConst_ne_top (W : ApWeight (d := d) p) : W.dualWeakConst ≠ ∞ := by
  unfold dualWeakConst
  have hA : 0 < W.A := pos_iff_ne_zero.mpr W.A_ne_zero
  have hfive : 0 < ENNReal.ofReal ((5 : ℝ) ^ d) := ENNReal.ofReal_pos.mpr (by positivity)
  exact mul_ne_top (rpow_ne_top_of_nonneg' hA W.A_ne_top)
    (rpow_ne_top_of_nonneg' hfive ENNReal.ofReal_ne_top)

/-- Lebesgue measure weighted by the measurable dual representative. -/
@[expose]
def dualMeasureMk (W : ApWeight (d := d) p) : Measure E :=
  volume.withDensity W.dualMk

/-- The measurable dual representative defines the same measure as `dualDensity`. -/
lemma dualMeasure_eq_mk (W : ApWeight (d := d) p) :
    dualMeasure p W.w = W.dualMeasureMk :=
  withDensity_congr_ae W.dualDensity_ae_eq_dualMk

end ApWeight

/-- A doubling density makes its centred maximal operator weak type `(1,1)`. -/
private lemma mul_measure_maximal_of_doubling {ρ : E → ℝ≥0∞} {D : ℝ≥0∞} (hD : D ≠ ∞)
    (hdouble : ∀ (x : E) (r : ℝ), 0 < r → volume.withDensity ρ (ball x (5 * r)) ≤
      D * volume.withDensity ρ (ball x r))
    (g : E → ℝ≥0∞) (s : ℝ≥0∞) :
    s * volume.withDensity ρ {x | s < TauCeti.maximalFunction (volume.withDensity ρ) g x} ≤
      D * ∫⁻ y, g y ∂volume.withDensity ρ := by
  let ν : Measure E := volume.withDensity ρ
  by_cases hs0 : s = 0
  · simp [hs0]
  · by_cases hsTop : s = ∞
    · rw [hsTop]
      have hempty : {x | ∞ < TauCeti.maximalFunction (volume.withDensity ρ) g x} = ∅ := by
        ext x
        simp [not_top_lt]
      rw [hempty, measure_empty, mul_zero]
      exact zero_le
    · let Sn : ℕ → Set E := fun n =>
        {x | ∃ r ∈ Ioc (0 : ℝ) ((n : ℝ) + 1),
          s < ⨍⁻ y in ball x r, g y ∂ν}
      have hmono : Monotone Sn := by
        intro m n hmn x hx
        obtain ⟨r, hr⟩ := hx
        obtain ⟨hrI, hlt⟩ := hr
        refine ⟨r, ⟨hrI.1, hrI.2.trans ?_⟩, hlt⟩
        have hcast : (m : ℝ) ≤ n := by exact_mod_cast hmn
        linarith
      have hunion : ⋃ n, Sn n = {x | s < TauCeti.maximalFunction ν g x} := by
        ext x
        constructor
        · intro hx
          rw [mem_iUnion] at hx
          obtain ⟨n, hx⟩ := hx
          obtain ⟨r, hr⟩ := hx
          obtain ⟨hrI, hlt⟩ := hr
          exact hlt.trans_le (TauCeti.setLAverage_le_maximalFunction ν g x hrI.1)
        · intro hx
          obtain ⟨r, hr, hlt⟩ := TauCeti.lt_maximalFunction_iff.mp hx
          refine mem_iUnion.mpr ⟨Nat.ceil r, r, ⟨hr, ?_⟩, hlt⟩
          exact (Nat.le_ceil r).trans (le_add_of_nonneg_right zero_le_one)
      have hcover : ∀ n, ∀ x ∈ Sn n, ∃ r ∈ Ioc (0 : ℝ) ((n : ℝ) + 1),
          s * ν (closedBall x (4 * r)) ≤ ∫⁻ y in ball x r, D * g y ∂ν := by
        intro n x hx
        obtain ⟨r, hr⟩ := hx
        obtain ⟨hrI, hlt⟩ := hr
        refine ⟨r, hrI, ?_⟩
        have havg : s * ν (ball x r) ≤ ∫⁻ y in ball x r, g y ∂ν := by
          rw [setLAverage_eq] at hlt
          exact (ENNReal.mul_lt_of_lt_div hlt).le
        have hclosed : ν (closedBall x (4 * r)) ≤ D * ν (ball x r) :=
          (measure_mono (closedBall_subset_concentric_five hrI.1)).trans (hdouble x r hrI.1)
        calc s * ν (closedBall x (4 * r))
            ≤ s * (D * ν (ball x r)) := mul_le_mul_right hclosed s
          _ = D * (s * ν (ball x r)) := by rw [← mul_assoc, mul_comm s, mul_assoc]
          _ ≤ D * ∫⁻ y in ball x r, g y ∂ν := mul_le_mul_right havg D
          _ = ∫⁻ y in ball x r, D * g y ∂ν :=
              (lintegral_const_mul' D (fun y => g y) hD).symm
      have hslice : ∀ n, s * ν (Sn n) ≤ D * ∫⁻ y, g y ∂ν := by
        intro n
        have hvitali :=
          TauCeti.mul_measure_le_lintegral_of_forall_exists_ball (μ := ν) (ν := ν)
            (t := s) (R := (n : ℝ) + 1) (g := fun y => D * g y) (hcover n)
        simpa [lintegral_const_mul' D g hD] using hvitali
      calc s * ν {x | s < TauCeti.maximalFunction ν g x}
          = s * ν (⋃ n, Sn n) := by rw [hunion]
        _ = s * ⨆ n, ν (Sn n) := by rw [hmono.measure_iUnion]
        _ = ⨆ n, s * ν (Sn n) := ENNReal.mul_iSup s fun n => ν (Sn n)
        _ ≤ D * ∫⁻ y, g y ∂ν := iSup_le hslice

namespace ApWeight

variable {p : ℝ}

/-- The centred weight maximal operator is weak type `(1,1)`. -/
lemma mul_measure_maximalFunction_weight (W : ApWeight (d := d) p) (g : E → ℝ≥0∞)
    (s : ℝ≥0∞) :
    s * weightMeasure W.w {x | s < TauCeti.maximalFunction (weightMeasure W.w) g x} ≤
      W.weakConst * ∫⁻ y, g y ∂weightMeasure W.w := by
  refine mul_measure_maximal_of_doubling W.weakConst_ne_top (fun x r hr => ?_) g s
  have hdoub := W.weight_doubling (c := (5 : ℝ)) (by norm_num) x hr
  unfold weakConst
  exact hdoub

/-- The centred dual maximal operator is weak type `(1,1)`. -/
lemma mul_measure_maximalFunction_dual (W : ApWeight (d := d) p) (g : E → ℝ≥0∞) (s : ℝ≥0∞) :
    s * W.dualMeasureMk {x | s < TauCeti.maximalFunction W.dualMeasureMk g x} ≤
      W.dualWeakConst * ∫⁻ y, g y ∂W.dualMeasureMk := by
  refine mul_measure_maximal_of_doubling W.dualWeakConst_ne_top (fun x r hr => ?_) g s
  have hdoub := W.dual_doubling (c := (5 : ℝ)) (by norm_num) x hr
  rw [W.dualMeasure_eq_mk] at hdoub
  unfold dualWeakConst
  exact hdoub

/-- Marcinkiewicz factor for the splitting `c = d = 1/2` and an `L^∞` constant `1`. -/
@[expose]
def marcFactor (t : ℝ) (D : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (t * (1 / 2) ^ (1 - t) / (t - 1)) * (ENNReal.ofReal (1 / 2)⁻¹ * D)

/-- The centred maximal operator is strong type `(t,t)` on a doubling weighted measure. -/
private lemma lintegral_rpow_maximal_of_doubling {ρ : E → ℝ≥0∞} {D : ℝ≥0∞} {t : ℝ}
    (ht : 1 < t) (hρ : Measurable ρ)
    (hpos : ∀ (x : E) (r : ℝ), 0 < r → volume.withDensity ρ (ball x r) ≠ 0)
    (hfin : ∀ (x : E) (r : ℝ), 0 < r → volume.withDensity ρ (ball x r) ≠ ∞)
    (hweak : ∀ (g : E → ℝ≥0∞) (s : ℝ≥0∞),
      s * volume.withDensity ρ {x | s < TauCeti.maximalFunction (volume.withDensity ρ) g x} ≤
        D * ∫⁻ y, g y ∂volume.withDensity ρ)
    {v : E → ℝ≥0∞} (hv : AEMeasurable v (volume.withDensity ρ)) :
    ∫⁻ y, TauCeti.maximalFunction (volume.withDensity ρ) v y ^ t ∂volume.withDensity ρ ≤
      marcFactor t D * ∫⁻ y, v y ^ t ∂volume.withDensity ρ := by
  let ν : Measure E := volume.withDensity ρ
  have hTv : AEMeasurable (fun x => TauCeti.maximalFunction ν v x) ν :=
    (measurable_maximalFunction_withDensity hρ hv hpos hfin).aemeasurable
  have hconst : marcFactor t D =
      ENNReal.ofReal (t * (1 / 2) ^ (1 - t) / (t - 1)) *
        (ENNReal.ofReal (1 / 2)⁻¹ * D) := rfl
  rw [hconst]
  refine TauCeti.lintegral_rpow_le_of_mul_meas_lt_le_of_le_eLpNormEssSup
      (T := fun g => TauCeti.maximalFunction ν g) (v := v) (p := t) (b := 1) (c := 1 / 2)
      (d := 1 / 2) (A := D) (μ := ν) (ν := ν) hv hTv ht
      (by norm_num) (by norm_num) (by norm_num) (by norm_num : (1 : ℝ) * (1 / 2) + 1 / 2 ≤ 1)
      ?hadd ?hweak ?hinfty
  · intro g₁ g₂ hg₁ hg₂
    have hnorm : AEMeasurable (fun y => ‖g₁ y‖ₑ) ν := by simpa using hg₁
    exact ae_of_all ν fun x => TauCeti.maximalFunction_add_le hnorm x
  · intro g _hg s
    simpa using hweak g s
  · intro g _hg
    refine ae_of_all ν fun x => ?_
    rw [ENNReal.ofReal_one, one_mul]
    exact TauCeti.maximalFunction_le_eLpNormEssSup ν g x

/-- The weight maximal operator is strong type `(q,q)` for the conjugate exponent. -/
lemma lintegral_rpow_maximal_weight (W : ApWeight (d := d) p) {v : E → ℝ≥0∞}
    (hv : AEMeasurable v (weightMeasure W.w)) :
    ∫⁻ y, TauCeti.maximalFunction (weightMeasure W.w) v y ^ W.conj ∂weightMeasure W.w ≤
      marcFactor W.conj W.weakConst * ∫⁻ y, v y ^ W.conj ∂weightMeasure W.w := by
  refine lintegral_rpow_maximal_of_doubling W.one_lt_conj W.measurable_weightDensity
      (fun x r hr => ?_) (fun x r _ => ?_)
      (fun g s => W.mul_measure_maximalFunction_weight g s) hv
  · rw [withDensity_apply _ measurableSet_ball]
    exact W.weight_ball_ne_zero x hr
  · rw [withDensity_apply _ measurableSet_ball]
    exact W.weight_ball_ne_top x r

/-- The dual maximal operator is strong type `(p,p)`. -/
lemma lintegral_rpow_maximal_dual (W : ApWeight (d := d) p) {v : E → ℝ≥0∞}
    (hv : AEMeasurable v W.dualMeasureMk) :
    ∫⁻ y, TauCeti.maximalFunction W.dualMeasureMk v y ^ p ∂W.dualMeasureMk ≤
      marcFactor p W.dualWeakConst * ∫⁻ y, v y ^ p ∂W.dualMeasureMk := by
  refine lintegral_rpow_maximal_of_doubling W.hp W.measurable_dualMk
      (fun x r hr => ?_) (fun x r hr => ?_)
      (fun g s => W.mul_measure_maximalFunction_dual g s) hv
  · rw [withDensity_apply _ measurableSet_ball]
    have hint : ∫⁻ y in ball x r, W.dualMk y ∂volume =
        ∫⁻ y in ball x r, dualDensity p W.w y ∂volume := by
      refine (setLIntegral_congr_fun_ae measurableSet_ball ?_).symm
      filter_upwards [W.dualDensity_ae_eq_dualMk] with y hy
      exact fun _ => hy
    rw [hint]
    exact W.dual_ball_ne_zero x hr
  · rw [withDensity_apply _ measurableSet_ball]
    have hint : ∫⁻ y in ball x r, W.dualMk y ∂volume =
        ∫⁻ y in ball x r, dualDensity p W.w y ∂volume := by
      refine (setLIntegral_congr_fun_ae measurableSet_ball ?_).symm
      filter_upwards [W.dualDensity_ae_eq_dualMk] with y hy
      exact fun _ => hy
    rw [hint]
    exact W.dual_ball_ne_top x hr

end ApWeight

end CKMA
