/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Slope
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.MetricSpace.Bounded

/-!
# One-sided limits of interval integrals and slopes

Facts about vector-valued functions of one real variable near an endpoint: averages
`h⁻¹ • ∫₀ʰ g` of a function continuous on `[0, h]`, the right derivative at `0` of
`u ↦ ∫₀ᵘ g`, short integrals tending to `0`, and one-sided slopes written through forward and
backward difference quotients.

## Main results

* `CKMA.norm_inv_smul_intervalIntegral_sub_le`: an average of values within `η` of `v` is
  within `η` of `v`.
* `CKMA.hasDerivWithinAt_intervalIntegral_zero_of_continuousOn`: the indefinite integral has
  right derivative `g 0` at `0`.
* `CKMA.tendsto_intervalIntegral_zero_nhdsGT_zero`,
  `CKMA.tendsto_inv_smul_intervalIntegral_nhdsGT_zero`,
  `CKMA.tendsto_intervalIntegral_sub_left_nhdsGT_zero`: short integrals tend to `0` and right
  averages tend to `g 0`.
* `CKMA.tendsto_slope_nhdsGT_of_tendsto`, `CKMA.tendsto_slope_nhdsLT_of_tendsto`: one-sided
  slopes from forward and backward difference quotients.
-/

public section

namespace CKMA

open MeasureTheory Filter Topology intervalIntegral
open scoped Interval

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The average `h⁻¹ • ∫₀ʰ g` of a function continuous on `[0, h]` with values within `η` of `v`
is within `η` of `v`. -/
theorem norm_inv_smul_intervalIntegral_sub_le [CompleteSpace X] {g : ℝ → X} {v : X} {h η : ℝ}
    (hh : 0 < h) (hg : ContinuousOn g (Set.Icc 0 h)) (hclose : ∀ r ∈ Set.Icc 0 h, ‖g r - v‖ ≤ η) :
    ‖h⁻¹ • (∫ r in (0 : ℝ)..h, g r) - v‖ ≤ η := by
  have hintg : IntervalIntegrable g volume 0 h := hg.intervalIntegrable_of_Icc hh.le
  have hintv : IntervalIntegrable (fun _ : ℝ => v) volume 0 h :=
    continuousOn_const.intervalIntegrable_of_Icc hh.le
  have hsub : ∫ r in (0 : ℝ)..h, (g r - v) = (∫ r in (0 : ℝ)..h, g r) - h • v := by
    rw [integral_sub hintg hintv, intervalIntegral.integral_const]
    simp only [sub_zero]
  have hsmul : h⁻¹ • (∫ r in (0 : ℝ)..h, g r) - v =
      h⁻¹ • ∫ r in (0 : ℝ)..h, (g r - v) := by
    rw [hsub, smul_sub, smul_smul, inv_mul_cancel₀ hh.ne', one_smul]
  rw [hsmul]
  have hnorm : ‖∫ r in (0 : ℝ)..h, (g r - v)‖ ≤ η * h := by
    have hbound := norm_integral_le_of_norm_le_const fun r hr =>
      hclose r (by
        rw [Set.uIoc_of_le hh.le] at hr
        exact ⟨hr.1.le, hr.2⟩)
    simpa only [sub_zero, abs_of_pos hh] using hbound
  calc ‖h⁻¹ • ∫ r in (0 : ℝ)..h, (g r - v)‖
      = h⁻¹ * ‖∫ r in (0 : ℝ)..h, (g r - v)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hh.le)]
    _ ≤ h⁻¹ * (η * h) := mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hh.le)
    _ = η := by rw [mul_comm η h, ← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul]

/-- The indefinite integral of a function continuous on `[0, b]` has right derivative `g 0`
at `0`. -/
theorem hasDerivWithinAt_intervalIntegral_zero_of_continuousOn [CompleteSpace X] {b : ℝ} {g : ℝ → X}
    (hb : 0 < b) (hg : ContinuousOn g (Set.Icc 0 b)) :
    HasDerivWithinAt (fun u => ∫ r in (0 : ℝ)..u, g r) (g 0) (Set.Ici 0) 0 := by
  have hint : IntervalIntegrable g volume 0 0 :=
    (hg.mono (Set.Icc_subset_Icc_right hb.le)).intervalIntegrable_of_Icc le_rfl
  have hmeas : StronglyMeasurableAtFilter g (nhdsWithin 0 (Set.Ioi 0)) := by
    refine ⟨Set.Ioo 0 b, ?_, ?_⟩
    · rw [mem_nhdsWithin]
      refine ⟨Set.Iio b, isOpen_Iio, hb, ?_⟩
      intro y hy
      exact ⟨hy.2, hy.1⟩
    · refine (hg.mono ?_).aestronglyMeasurable (μ := volume) measurableSet_Ioo
      intro y hy
      exact ⟨hy.1.le, hy.2.le⟩
  have hcont : ContinuousWithinAt g (Set.Ioi 0) 0 := by
    refine (hg 0 ⟨le_rfl, hb.le⟩).mono_of_mem_nhdsWithin ?_
    rw [mem_nhdsWithin]
    refine ⟨Set.Iio b, isOpen_Iio, hb, ?_⟩
    intro y hy
    exact ⟨le_of_lt hy.2, hy.1.le⟩
  exact integral_hasDerivWithinAt_right (s := Set.Ici 0) (t := Set.Ioi 0) hint hmeas hcont

/-- Short integrals of a function continuous at `0` from the right tend to `0`. -/
theorem tendsto_intervalIntegral_zero_nhdsGT_zero [CompleteSpace X] {b : ℝ} {g : ℝ → X} (hb : 0 < b)
    (hg : ContinuousOn g (Set.Icc 0 b)) :
    Tendsto (fun h : ℝ => ∫ u in (0 : ℝ)..h, g u) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have htend := (hasDerivWithinAt_intervalIntegral_zero_of_continuousOn hb
    hg).continuousWithinAt.tendsto.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)
  rw [integral_same] at htend
  exact htend

/-- The right average of a function continuous on `[0, b]` tends to its value at `0`. -/
theorem tendsto_inv_smul_intervalIntegral_nhdsGT_zero [CompleteSpace X] {b : ℝ} {g : ℝ → X}
    (hb : 0 < b) (hg : ContinuousOn g (Set.Icc 0 b)) :
    Tendsto (fun h : ℝ => h⁻¹ • ∫ u in (0 : ℝ)..h, g u) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (g 0)) := by
  have hprim := hasDerivWithinAt_intervalIntegral_zero_of_continuousOn hb hg
  rw [hasDerivWithinAt_iff_tendsto_slope] at hprim
  have hset : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
    ext r
    rw [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_Ici, Set.mem_Ioi]
    constructor
    · rintro ⟨hr, hne⟩
      exact lt_of_le_of_ne hr (Ne.symm hne)
    · intro hr
      exact ⟨hr.le, hr.ne'⟩
  rw [hset] at hprim
  refine hprim.congr fun h => ?_
  rw [slope_def_module, sub_zero, integral_same, sub_zero]

/-- If `h⁻¹ • (g (t + h) - g t) → L` as `h → 0⁺`, then the slope of `g` at `t` tends to `L`
from the right. -/
theorem tendsto_slope_nhdsGT_of_tendsto {g : ℝ → X} {t : ℝ} {L : X}
    (h : Tendsto (fun h : ℝ => h⁻¹ • (g (t + h) - g t)) (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    Tendsto (slope g t) (nhdsWithin t (Set.Ioi t)) (nhds L) := by
  have hshift : Tendsto (fun y : ℝ => y - t) (nhdsWithin t (Set.Ioi t))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [Metric.tendsto_nhdsWithin_nhdsWithin]
    intro ε hε
    refine ⟨ε, hε, fun y hy hdist => ?_⟩
    refine ⟨sub_pos.mpr hy, ?_⟩
    simpa [Real.dist_eq, sub_zero, abs_of_pos (sub_pos.mpr hy)] using hdist
  refine (h.comp hshift).congr fun y => ?_
  dsimp only [Function.comp_apply]
  rw [slope_def_module]
  have hyt : t + (y - t) = y := by ring
  rw [hyt]

/-- If `k⁻¹ • (g t - g (t - k)) → L` as `k → 0⁺`, then the slope of `g` at `t` tends to `L`
from the left. -/
theorem tendsto_slope_nhdsLT_of_tendsto {g : ℝ → X} {t : ℝ} {L : X}
    (h : Tendsto (fun k : ℝ => k⁻¹ • (g t - g (t - k))) (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    Tendsto (slope g t) (nhdsWithin t (Set.Iio t)) (nhds L) := by
  have hshift : Tendsto (fun y : ℝ => t - y) (nhdsWithin t (Set.Iio t))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [Metric.tendsto_nhdsWithin_nhdsWithin]
    intro ε hε
    refine ⟨ε, hε, fun y hy hdist => ?_⟩
    refine ⟨sub_pos.mpr hy, ?_⟩
    simpa [Real.dist_eq, sub_zero, abs_sub_comm] using hdist
  refine (h.comp hshift).congr fun y => ?_
  dsimp only [Function.comp_apply]
  rw [slope_def_module]
  have hneg : y - t = -(t - y) := by ring
  have hsub : g y - g t = -(g t - g y) := by abel
  have hback : t - (t - y) = y := by ring
  rw [hback, hneg, hsub, inv_neg, neg_smul, smul_neg, neg_neg]

/-- For `g` continuous on `[0, b]`, the integral `∫_{b-k}^b g` tends to `0` as `k → 0⁺`. -/
theorem tendsto_intervalIntegral_sub_left_nhdsGT_zero {b : ℝ} {g : ℝ → X} (hb : 0 < b)
    (hg : ContinuousOn g (Set.Icc 0 b)) :
    Tendsto (fun k : ℝ => ∫ u in (b - k)..b, g u) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (g 0)) (hM 0 ⟨le_rfl, hb.le⟩)
  have hden : 0 < M + 1 := by linarith
  refine ⟨min (ε / (M + 1)) b, lt_min (div_pos hε hden) hb, fun k hk hdist => ?_⟩
  have hk0 : 0 < k := hk
  have hmin := lt_min_iff.mp ((by rwa [Real.dist_eq, sub_zero, abs_of_pos hk0] at hdist))
  have hlow : 0 ≤ b - k := by linarith [hmin.2]
  have hup : b - k ≤ b := by linarith
  have hpoint : ∀ u ∈ Ι (b - k) b, ‖g u‖ ≤ M := by
    intro u hu
    rw [Set.uIoc_of_le hup] at hu
    exact hM u ⟨hlow.trans hu.1.le, hu.2⟩
  have hnorm := norm_integral_le_of_norm_le_const hpoint
  rw [dist_eq_norm, sub_zero]
  have hlen : b - (b - k) = k := by ring
  rw [hlen, abs_of_pos hk0] at hnorm
  have hmk : M * k ≤ M * (ε / (M + 1)) :=
    mul_le_mul_of_nonneg_left (le_of_lt hmin.1) hM0
  have hrew : M * (ε / (M + 1)) = ε * (M / (M + 1)) := by
    rw [mul_div_assoc', mul_comm M ε, ← mul_div_assoc]
  have hfrac : M / (M + 1) < 1 := (div_lt_one hden).mpr (by linarith)
  have hstrict : M * (ε / (M + 1)) < ε := by
    rw [hrew]
    exact (mul_lt_mul_of_pos_left hfrac hε).trans_eq (mul_one ε)
  exact lt_of_le_of_lt (le_trans hnorm hmk) hstrict

end CKMA
