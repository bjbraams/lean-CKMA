/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Real.RectangularDifferentiation.Base

import Mathlib.Topology.UrysohnsLemma
import CKMA.Analysis.Real.RectangularDifferentiation.Approximate
import CKMA.Analysis.Real.RectangularDifferentiation.Step
import CKMA.Analysis.Real.RectangularDifferentiation.Iteration

/-!
# Rectangular differentiation of the local endpoint class

A continuous compactly supported cutoff reduces a function of local class `L(log⁺L)^{d-1}` to the
global class already differentiated by the strong maximal inequality. The cutoff equals one on a
ball about almost every point, so the rectangular averages of the original function agree with
those of the cutoff product.

## Main results

* `CKMA.exists_compactCutoff`: existence of a continuous compactly supported cutoff preserving the
  local `L(log⁺ L)^{d-1}` class.
* `CKMA.rectanglesDifferentiateAt_of_cutoff`: a cutoff equal to one near a point transfers
  rectangular differentiation; with the above it gives `CKMA.ae_rectanglesDifferentiateAt`.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Set Metric
open scoped ENNReal NNReal

/-- A continuous cutoff, equal to one on a closed ball, preserves the local endpoint class. -/
theorem exists_compactCutoff {d : ℕ} {f : (Fin d → ℝ) → ℝ} (hm : Measurable f)
    (hf : IsLocallyLLog d f) (R : ℝ) :
    ∃ φ : (Fin d → ℝ) → ℝ, Continuous φ ∧ HasCompactSupport φ ∧
      EqOn φ 1 (closedBall 0 R) ∧
      Integrable (fun x ↦ strongMaximalGrowth d |f x * φ x|) := by
  have hdisj : Disjoint (closedBall (0 : Fin d → ℝ) R) (ball 0 (R + 1))ᶜ :=
    disjoint_compl_right_iff_subset.mpr (closedBall_subset_ball (lt_add_one R))
  obtain ⟨φ, hφ1, -, hφsupp, hφrange⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_closedBall 0 R) isOpen_ball.isClosed_compl hdisj
  let ψ : (Fin d → ℝ) → ℝ := fun x ↦ φ x
  have hψ : Continuous ψ := φ.continuous
  have hsupp : HasCompactSupport ψ := hφsupp
  have hone : EqOn ψ 1 (closedBall 0 R) := fun x hx ↦ hφ1 hx
  have h01 : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1 := by
    intro x
    simpa [ψ, mem_Icc] using hφrange x
  have hmeasK : MeasurableSet (tsupport ψ) := (isClosed_tsupport ψ).measurableSet
  have hOn : IntegrableOn (fun x ↦ strongMaximalGrowth d |f x|) (tsupport ψ) :=
    hf (tsupport ψ) hsupp
  set bound : (Fin d → ℝ) → ℝ :=
    (tsupport ψ).indicator fun x ↦ strongMaximalGrowth d |f x|
  have hInd : Integrable bound := hOn.integrable_indicator hmeasK
  have hpt : ∀ x, strongMaximalGrowth d |f x * ψ x| ≤ bound x := by
    intro x
    by_cases hx : x ∈ tsupport ψ
    · unfold bound
      rw [indicator_of_mem hx]
      have habs : |f x * ψ x| ≤ |f x| := by
        rw [abs_mul, abs_of_nonneg (h01 x).1]
        exact mul_le_of_le_one_right (abs_nonneg _) (h01 x).2
      exact strongMaximalGrowth_mono (abs_nonneg _) habs
    · unfold bound
      rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
      simp [strongMaximalGrowth_zero, mul_zero]
  have hmψ : Measurable ψ := hψ.measurable
  have hmabs : Measurable fun x ↦ |f x * ψ x| := by
    simpa [ψ, Real.norm_eq_abs] using (hm.mul hmψ).norm
  have hGi : Integrable (fun x ↦ strongMaximalGrowth d |f x * ψ x|) :=
    hInd.mono' ((measurable_strongMaximalGrowth d).comp hmabs).aestronglyMeasurable
      (ae_of_all _ fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (strongMaximalGrowth_nonneg (abs_nonneg _))]
        exact hpt x)
  exact ⟨ψ, hψ, hsupp, hone, hGi⟩

/-- A cutoff equal to one on a ball about `x` transfers rectangular differentiation. -/
theorem rectanglesDifferentiateAt_of_cutoff {d : ℕ} (hd : 0 < d) {f φ : (Fin d → ℝ) → ℝ}
    {x : Fin d → ℝ} {R : ℝ} (hx : ‖x‖ < R) (hφ : EqOn φ 1 (closedBall 0 R))
    (hdiff : RectanglesDifferentiateAt (fun y ↦ f y * φ y) x) :
    RectanglesDifferentiateAt f x := by
  intro ε hε
  obtain ⟨δ, hδ, hδR⟩ := hdiff ε hε
  have hgap : 0 < R - ‖x‖ := sub_pos.2 hx
  refine ⟨min δ (R - ‖x‖), lt_min hδ hgap, fun S hxS hwidth ↦ ?_⟩
  have hagree : EqOn f (fun y ↦ f y * φ y) S.carrier := by
    intro y hy
    have hdist : dist y x < R - ‖x‖ :=
      (S.dist_lt_totalWidth hd hxS hy).trans (hwidth.trans_le (min_le_right _ _))
    have hynorm : ‖y‖ < R := by
      have htri : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
        simpa [sub_add_cancel] using norm_add_le (y - x) x
      rw [← dist_eq_norm] at htri
      linarith
    have hyball : y ∈ closedBall (0 : Fin d → ℝ) R := by
      rw [mem_closedBall, dist_eq_norm, sub_zero]
      exact hynorm.le
    show f y = f y * φ y
    rw [hφ hyball, Pi.one_apply, mul_one]
  have hxball : x ∈ closedBall (0 : Fin d → ℝ) R := by
    rw [mem_closedBall, dist_eq_norm, sub_zero]
    exact hx.le
  have havg : S.average f = S.average (fun y ↦ f y * φ y) := by
    unfold OpenRectangle.average
    congr 1
    exact setIntegral_congr_fun S.measurableSet_carrier hagree
  have hval : f x = f x * φ x := by
    rw [hφ hxball, Pi.one_apply, mul_one]
  rw [havg, hval]
  exact hδR S hxS (hwidth.trans_le (min_le_left _ _))

end CKMA
