/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Frostman measures and planar projections

Ball-growth bounds, Frostman probabilities supported on compact sets, Hausdorff dimension
of planar projections, and pure one-unrectifiability tested against Lipschitz curves.
The projection statements use Lebesgue-almost every angle and include positive length
when the source has dimension greater than one. Hausdorff measures and dimension are
Mathlib's; source measurability and finite length are explicit where required.
Sources: GAPS 37.4, 37.8 and 37.21.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology
open scoped ENNReal NNReal MeasureTheory

/-- Frostman ball growth. Finiteness of the measure and positivity of the exponent
and constant are separate hypotheses of the existence theorem. -/
def HasFrostmanBound {E : Type*} [MetricSpace E] [MeasurableSpace E]
    (μ : Measure E) (s C : ℝ) : Prop :=
  ∀ (x : E) (r : ℝ), 0 < r → μ (Metric.ball x r) ≤ ENNReal.ofReal (C * r ^ s)

/-- **37.4**: positivity of Hausdorff measure on a compact Euclidean set is equivalent to
an actually supported probability with a finite Frostman constant. At positive exponent this
positivity is equivalent to positivity of Hausdorff content. -/
theorem frostman_compact {d : ℕ} {s : ℝ} (hs : 0 < s)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsCompact K) :
    0 < Measure.hausdorffMeasure s K ↔
      ∃ μ : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure μ ∧ μ Kᶜ = 0 ∧
        ∃ C : ℝ, 0 < C ∧ HasFrostmanBound μ s C := by
  sorry

/-- Orthogonal scalar coordinate projection of the Euclidean plane at angle theta. -/
def planarProjection (θ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Real.cos θ * x 0 + Real.sin θ * x 1

/-- **37.8**, planar Marstrand projection, including positive length above dimension one. -/
theorem planar_projection_dimension {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A) :
    ∀ᵐ θ ∂volume, dimH (planarProjection θ '' A) = min 1 (dimH A) ∧
      (1 < dimH A → 0 < volume (planarProjection θ '' A)) := by
  sorry

/-- Pure one-unrectifiability in the plane, tested against all Lipschitz curves. -/
def IsPurelyOneUnrectifiable (A : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ (L : ℝ≥0) (f : ℝ → EuclideanSpace ℝ (Fin 2)), LipschitzWith L f →
    Measure.hausdorffMeasure 1 (A ∩ Set.range f) = 0

/-- **37.21**, planar Besicovitch–Federer for Borel sets of finite length. -/
theorem planar_besicovitch_federer {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : MeasurableSet A) (hfin : Measure.hausdorffMeasure 1 A < ∞) :
    IsPurelyOneUnrectifiable A ↔ ∀ᵐ θ ∂volume, volume (planarProjection θ '' A) = 0 := by
  sorry

end CKMA
