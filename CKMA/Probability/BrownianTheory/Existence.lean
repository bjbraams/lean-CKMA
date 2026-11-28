/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.BrownianTheory.HolderPath
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# Wiener measure

Kolmogorov extension supplies a coordinate pre-Brownian process on `ℝ≥0 → ℝ`.
The dyadic-floor modification pushes forward to a probability on `C(ℝ≥0, ℝ)`
whose coordinate process is Brownian.

## Main definitions

* `CKMA.Brownian.coordinatePreBrownian`: coordinate projections of a process indexed by
  nonnegative time.
* `CKMA.Brownian.wienerOfPreBrownian`: law of the continuous modification pushed forward to path
  space.

## Main results

* `CKMA.Brownian.coordinatePreBrownian_isPreBrownian`: the coordinate process of a projective
  limit of Brownian finite-dimensional laws is pre-Brownian.
* `CKMA.Brownian.wienerOfPreBrownian_isBrownian`: the coordinate process on path space is Brownian
  under the pushed-forward law. `CKMA.exists_brownianMeasure` (**08.1**) combines these.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Brownian

/-- Coordinate projections of a process indexed by nonnegative time. -/
@[expose]
def coordinatePreBrownian (t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ := ω t

/-- Defining equation of `coordinatePreBrownian`. -/
@[simp]
theorem coordinatePreBrownian_apply (t : ℝ≥0) (ω : ℝ≥0 → ℝ) : coordinatePreBrownian t ω = ω t :=
  rfl

/-- The coordinate process of the Brownian projective limit is pre-Brownian. -/
lemma coordinatePreBrownian_isPreBrownian (μ : Measure (ℝ≥0 → ℝ))
    (hμ : IsProjectiveLimit μ BrownianReal.projectiveFamily) :
    IsPreBrownianReal coordinatePreBrownian μ where
  hasLaw I := {
    aemeasurable := (Finset.measurable_restrict I).aemeasurable
    map_eq := hμ I
  }

/-- The continuous modification, packaged as a continuous path. -/
@[expose]
def holderToPath {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (ω : Ω) : C(ℝ≥0, ℝ) :=
  ⟨fun t => holderPath hB t ω, continuous_holderPath hB ω⟩

/-- Evaluation of `holderToPath` is the continuous modification `holderPath`. -/
@[simp]
theorem holderToPath_apply {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (ω : Ω) (t : ℝ≥0) :
    holderToPath hB ω t = holderPath hB t ω :=
  rfl

/-- The path map is measurable for the compact-open Borel structure. -/
private lemma measurable_holderToPath {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) :
    Measurable (holderToPath hB) := by
  rw [ContinuousMap.measurable_iff_eval]
  intro t
  simpa [holderToPath] using measurable_holderPath hB t

/-- Law of the continuous modification pushed forward to path space. -/
@[expose]
def wienerOfPreBrownian {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) :
    Measure C(ℝ≥0, ℝ) :=
  μ.map (holderToPath hB)

/-- Defining equation of `wienerOfPreBrownian`. -/
theorem wienerOfPreBrownian_def {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) :
    wienerOfPreBrownian hB = μ.map (holderToPath hB) :=
  rfl

/-- The pushed-forward modification is a probability measure. -/
lemma isProbabilityMeasure_wienerOfPreBrownian {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B μ) : IsProbabilityMeasure (wienerOfPreBrownian hB) := by
  unfold wienerOfPreBrownian
  infer_instance

/-- Finite coordinate projections of a continuous path are measurable. -/
private lemma measurable_restrict_continuous (I : Finset ℝ≥0) :
    Measurable (fun f : C(ℝ≥0, ℝ) => I.restrict (fun x => f x)) :=
  Measurable.of_eval fun i =>
    ContinuousMap.measurable_iff_eval.mp measurable_id (i : ℝ≥0)

/-- Coordinates of the pushed-forward modification are Brownian. -/
lemma wienerOfPreBrownian_isBrownian {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) :
    IsBrownianReal (fun t ω => ω t) (wienerOfPreBrownian hB) where
  hasLaw I := {
    aemeasurable := (measurable_restrict_continuous I).aemeasurable
    map_eq := by
      rw [wienerOfPreBrownian,
        Measure.map_map (measurable_restrict_continuous I) (measurable_holderToPath hB)]
      exact ((holderPath_isBrownian hB).hasLaw I).map_eq
  }
  cont := Filter.Eventually.of_forall fun ω => ω.continuous

end Brownian

end CKMA
