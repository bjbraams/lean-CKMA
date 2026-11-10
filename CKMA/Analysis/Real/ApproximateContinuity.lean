/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Covering.DensityTheorem

/-!
# Approximate continuity by shrinking-ball densities

Relative densities in shrinking closed balls and approximate continuity of metric-valued
functions. Finite small-ball masses are recorded explicitly so extended-real division
does not turn infinite mass into zero density. The almost-everywhere statement is for finite
measurable real functions on a second-countable Borel space carrying a locally finite
uniformly locally doubling measure; Euclidean volume is included.
Source: GAPS 05.30. The almost-everywhere proof uses Mathlib's Vitali-family density theorem
for the complements of preimages of rational intervals, followed by countable intersection.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology
open scoped ENNReal

variable {E F : Type*} [MetricSpace E] [MeasurableSpace E] [MetricSpace F]

/-- Density zero in shrinking closed balls with eventually finite mass.
Zero-mass balls use the extended-real ratio convention `0 / 0 = 0`. -/
def HasDensityZeroAt (μ : Measure E) (s : Set E) (x : E) : Prop :=
  (∀ᶠ r : ℝ in 𝓝[>] 0, μ (Metric.closedBall x r) < ∞) ∧
    Tendsto (fun r : ℝ ↦ μ (s ∩ Metric.closedBall x r) / μ (Metric.closedBall x r))
      (𝓝[>] 0) (𝓝 0)

/-- For a locally finite measure, the finite-ball guard is automatic and density zero is
characterized by the limit of relative ball masses. -/
theorem hasDensityZeroAt_iff_of_isLocallyFiniteMeasure (μ : Measure E)
    [IsLocallyFiniteMeasure μ] (s : Set E) (x : E) :
    HasDensityZeroAt μ s x ↔ Tendsto
      (fun r : ℝ ↦ μ (s ∩ Metric.closedBall x r) / μ (Metric.closedBall x r))
      (𝓝[>] 0) (𝓝 0) := by
  refine ⟨And.right, fun h ↦ ⟨?_, h⟩⟩
  obtain ⟨U, hxU, hU, hfin⟩ := μ.exists_isOpen_measure_lt_top x
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hxU
  filter_upwards [nhdsWithin_le_nhds (gt_mem_nhds hε)] with r hr
  apply lt_of_le_of_lt (measure_mono ?_) hfin
  intro y hy
  apply hball
  exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hy).trans_lt hr)

/-- Every subset of a set of density zero also has density zero. -/
theorem HasDensityZeroAt.mono {μ : Measure E} {s t : Set E} {x : E}
    (ht : HasDensityZeroAt μ t x) (hst : s ⊆ t) : HasDensityZeroAt μ s x := by
  refine ⟨ht.1, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht.2
    (fun _ ↦ bot_le) (fun r ↦ ?_)⟩
  exact ENNReal.div_le_div_right (measure_mono (Set.inter_subset_inter_left _ hst)) _

/-- Almost every point outside a measurable set is a density-zero point of that set. -/
theorem ae_hasDensityZeroAt_of_not_mem [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure E) [IsLocallyFiniteMeasure μ] [IsUnifLocDoublingMeasure μ]
    {s : Set E} (hs : MeasurableSet s) : ∀ᵐ x ∂μ, x ∉ s → HasDensityZeroAt μ s x := by
  filter_upwards [VitaliFamily.ae_tendsto_measure_inter_div_of_measurableSet
    (IsUnifLocDoublingMeasure.vitaliFamily μ 1) hs] with x hx hxs
  rw [hasDensityZeroAt_iff_of_isLocallyFiniteMeasure]
  have hballs := IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt μ
    (fun _ : ℝ ↦ x) id (tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝[>] 0) (𝓝[>] 0))
    (K := 1) (by
      filter_upwards [self_mem_nhdsWithin] with r hr
      simpa only [one_mul, id_eq] using Metric.mem_closedBall_self (le_of_lt hr))
  simpa only [Set.indicator_of_notMem hxs, Function.comp_def, id_eq] using hx.comp hballs

/-- Approximate continuity with respect to `μ`, using closed-ball density. -/
def ApproximatelyContinuousAt (μ : Measure E) (f : E → F) (x : E) : Prop :=
  ∀ ε : ℝ, 0 < ε → HasDensityZeroAt μ {y | ε < dist (f y) (f x)} x

/-- A finite measurable real function is approximately continuous almost everywhere for a
locally finite, uniformly locally doubling measure on a second-countable Borel space. -/
theorem ae_approximatelyContinuousAt [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure E) [IsLocallyFiniteMeasure μ] [IsUnifLocDoublingMeasure μ]
    {f : E → ℝ} (hf : Measurable f) :
    ∀ᵐ x ∂μ, ApproximatelyContinuousAt μ f x := by
  have hzero (p q : ℚ) : ∀ᵐ x ∂μ,
      x ∉ f ⁻¹' (Set.Ioo (p : ℝ) q)ᶜ →
        HasDensityZeroAt μ (f ⁻¹' (Set.Ioo (p : ℝ) q)ᶜ) x :=
    ae_hasDensityZeroAt_of_not_mem μ ((measurableSet_Ioo.compl).preimage hf)
  have hall : ∀ᵐ x ∂μ, ∀ p q : ℚ,
      x ∉ f ⁻¹' (Set.Ioo (p : ℝ) q)ᶜ →
        HasDensityZeroAt μ (f ⁻¹' (Set.Ioo (p : ℝ) q)ᶜ) x :=
    ae_all_iff.2 fun p ↦ ae_all_iff.2 fun q ↦ hzero p q
  filter_upwards [hall] with x hx ε hε
  obtain ⟨p, hp₁, hp₂⟩ := exists_rat_btwn (show f x - ε / 2 < f x by linarith)
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show f x < f x + ε / 2 by linarith)
  have hxmem : x ∉ f ⁻¹' (Set.Ioo (p : ℝ) q)ᶜ := by
    simpa only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Ioo, not_not] using ⟨hp₂, hq₁⟩
  apply (hx p q hxmem).mono
  intro y hy
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Ioo]
  intro hfy
  have hdist : dist (f y) (f x) < ε := by
    rw [Real.dist_eq]
    exact abs_lt.2 ⟨by linarith [hfy.1], by linarith [hfy.2]⟩
  exact (not_lt_of_ge hdist.le) hy

end CKMA
