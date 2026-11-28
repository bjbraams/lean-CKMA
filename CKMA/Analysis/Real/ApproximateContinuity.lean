/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Doubling
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

import Mathlib.MeasureTheory.Covering.DensityTheorem

/-!
# Approximate continuity by shrinking-ball densities

Relative densities in shrinking closed balls and approximate continuity of metric-valued
functions. Finite small-ball masses are recorded explicitly so extended-real division
does not turn infinite mass into zero density. The almost-everywhere statement is for
almost-everywhere measurable functions into a second-countable metric space, on a
second-countable Borel space carrying a locally finite uniformly locally doubling measure;
finite measurable real functions on Euclidean space with Lebesgue measure are included.
Source: GAPS 05.30. The almost-everywhere proof uses Mathlib's Vitali-family density theorem
for the complements of preimages of the open sets of a countable basis, followed by countable
intersection.

## Main definitions

* `CKMA.HasDensityZeroAt`: density zero of a set at a point in shrinking closed balls.
* `CKMA.ApproximatelyContinuousAt`: approximate continuity of a function at a point.

## Main results

* `CKMA.hasDensityZeroAt_iff`, `CKMA.approximatelyContinuousAt_iff`: the defining
  conditions.
* `CKMA.HasDensityZeroAt.mono_ae`: density zero passes to almost-everywhere subsets.
* `CKMA.hasDensityZeroAt_iff_of_isLocallyFiniteMeasure`: for a locally finite measure, density
  zero is the vanishing limit of relative ball masses.
* `CKMA.ae_hasDensityZeroAt_of_notMem`: almost every point outside a measurable set is a
  density-zero point of that set.
* `CKMA.ae_approximatelyContinuousAt_of_measurable`, `CKMA.ae_approximatelyContinuousAt`
  (**05.30**): Lusin–Denjoy theorem that every
  almost-everywhere measurable function into a second-countable metric space is approximately
  continuous almost everywhere.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology
open scoped ENNReal

variable {E F : Type*} [MetricSpace E] [MeasurableSpace E] [MetricSpace F]

/-- Density zero in shrinking closed balls with eventually finite mass.
Zero-mass balls use the extended-real ratio convention `0 / 0 = 0`. -/
@[expose]
def HasDensityZeroAt (μ : Measure E) (s : Set E) (x : E) : Prop :=
  (∀ᶠ r : ℝ in 𝓝[>] 0, μ (Metric.closedBall x r) < ∞) ∧
    Tendsto (fun r : ℝ ↦ μ (s ∩ Metric.closedBall x r) / μ (Metric.closedBall x r))
      (𝓝[>] 0) (𝓝 0)

/-- The defining condition of density zero: eventually finite small-ball masses and relative
masses tending to zero. -/
theorem hasDensityZeroAt_iff {μ : Measure E} {s : Set E} {x : E} :
    HasDensityZeroAt μ s x ↔ (∀ᶠ r : ℝ in 𝓝[>] 0, μ (Metric.closedBall x r) < ∞) ∧
      Tendsto (fun r : ℝ ↦ μ (s ∩ Metric.closedBall x r) / μ (Metric.closedBall x r))
        (𝓝[>] 0) (𝓝 0) :=
  Iff.rfl

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

/-- Every almost-everywhere subset of a set of density zero also has density zero. -/
theorem HasDensityZeroAt.mono_ae {μ : Measure E} {s t : Set E} {x : E}
    (ht : HasDensityZeroAt μ t x) (hst : s ≤ᵐ[μ] t) : HasDensityZeroAt μ s x := by
  refine ⟨ht.1, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht.2
    (fun _ ↦ bot_le) (fun r ↦ ?_)⟩
  exact ENNReal.div_le_div_right
    (measure_mono_ae (ae_subset_inter hst (ae_subset.2 (by simp)))) _

/-- Every subset of a set of density zero also has density zero. -/
theorem HasDensityZeroAt.mono {μ : Measure E} {s t : Set E} {x : E}
    (ht : HasDensityZeroAt μ t x) (hst : s ⊆ t) : HasDensityZeroAt μ s x :=
  ht.mono_ae (Eventually.of_forall hst)

/-- Almost every point outside a measurable set is a density-zero point of that set. -/
theorem ae_hasDensityZeroAt_of_notMem [BorelSpace E] [SecondCountableTopology E]
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
@[expose]
def ApproximatelyContinuousAt (μ : Measure E) (f : E → F) (x : E) : Prop :=
  ∀ ε : ℝ, 0 < ε → HasDensityZeroAt μ {y | ε < dist (f y) (f x)} x

/-- Approximate continuity at `x`: for every `ε > 0`, the set where `f` is more than `ε` away
from `f x` has density zero at `x`. -/
theorem approximatelyContinuousAt_iff {μ : Measure E} {f : E → F} {x : E} :
    ApproximatelyContinuousAt μ f x ↔
      ∀ ε : ℝ, 0 < ε → HasDensityZeroAt μ {y | ε < dist (f y) (f x)} x :=
  Iff.rfl

/-- Approximate continuity at `x` depends only on the almost-everywhere class of `f`, provided
the value at `x` agrees. -/
theorem ApproximatelyContinuousAt.congr_ae {μ : Measure E} {f g : E → F} {x : E}
    (hg : ApproximatelyContinuousAt μ g x) (hfg : f =ᵐ[μ] g) (hx : f x = g x) :
    ApproximatelyContinuousAt μ f x := fun ε hε ↦
  (hg ε hε).mono_ae (hfg.mono fun y hy hlt ↦ by
    simpa only [Set.mem_ofPred_eq, hy, hx] using hlt)

/-- A measurable function into a second-countable metric space is approximately continuous
almost everywhere for a locally finite, uniformly locally doubling measure on a second-countable
Borel space. -/
theorem ae_approximatelyContinuousAt_of_measurable [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace F] [OpensMeasurableSpace F] [SecondCountableTopology F]
    (μ : Measure E) [IsLocallyFiniteMeasure μ] [IsUnifLocDoublingMeasure μ]
    {f : E → F} (hf : Measurable f) :
    ∀ᵐ x ∂μ, ApproximatelyContinuousAt μ f x := by
  have hall : ∀ᵐ x ∂μ, ∀ U ∈ TopologicalSpace.countableBasis F,
      x ∉ f ⁻¹' Uᶜ → HasDensityZeroAt μ (f ⁻¹' Uᶜ) x :=
    (ae_ball_iff (TopologicalSpace.countable_countableBasis F)).2 fun U hU ↦
      ae_hasDensityZeroAt_of_notMem μ
        ((TopologicalSpace.isOpen_of_mem_countableBasis hU).measurableSet.compl.preimage hf)
  filter_upwards [hall] with x hx ε hε
  obtain ⟨U, hU, hxU, hUball⟩ := (TopologicalSpace.isBasis_countableBasis F).mem_nhds_iff.1
    (Metric.ball_mem_nhds (f x) hε)
  refine (hx U hU (by simpa using hxU)).mono fun y hy hyU ↦ ?_
  exact (not_lt_of_ge (Metric.mem_ball.1 (hUball hyU)).le) hy

/-- **05.30**: an almost-everywhere measurable function into a second-countable metric space is
approximately continuous almost everywhere for a locally finite, uniformly locally doubling
measure on a second-countable Borel space. This includes finite measurable real functions on
Euclidean space with Lebesgue measure. -/
theorem ae_approximatelyContinuousAt [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace F] [OpensMeasurableSpace F] [SecondCountableTopology F]
    (μ : Measure E) [IsLocallyFiniteMeasure μ] [IsUnifLocDoublingMeasure μ]
    {f : E → F} (hf : AEMeasurable f μ) :
    ∀ᵐ x ∂μ, ApproximatelyContinuousAt μ f x := by
  filter_upwards [ae_approximatelyContinuousAt_of_measurable μ hf.measurable_mk, hf.ae_eq_mk]
    with x hx hfx
  exact hx.congr_ae hf.ae_eq_mk hfx

end CKMA
