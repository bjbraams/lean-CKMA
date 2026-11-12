/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.BrownianTheory.Existence
public import CKMA.Probability.BrownianTheory.Reflection.Bound
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Topology.MetricSpace.Holder

/-!
# Brownian laws, modifications, strong Markov and reflection (08.1, 08.3, 08.4)

The canonical law is a probability measure on `C(ℝ≥0, ℝ)` with its compact-open Borel
sigma-algebra. Its coordinate process has continuous paths by construction. A separate
modification theorem starts from an arbitrary pre-Brownian process and gives every
positive local Hölder exponent below one half.

`brownianShift` describes increments after a finite-valued stopping time. The strong
Markov interface uses the raw natural filtration and finite-dimensional independence;
the reflection principle uses a strictly positive level and includes time zero.
The target statements correspond to the indicated entries of `GAPS.md`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- **08.1**: a canonical Brownian law on the Borel space of continuous real paths.
The coordinate process is continuous for every sample path. -/
theorem exists_brownianMeasure : ∃ μ : Measure C(ℝ≥0, ℝ),
    IsProbabilityMeasure μ ∧ IsBrownianReal (fun t ω ↦ ω t) μ := by
  exact exists_wienerMeasure

/-- A pre-Brownian process has a continuous modification with every subcritical local Holder
  exponent. -/
theorem exists_holder_brownianModification {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B μ) :
    ∃ C : ℝ≥0 → Ω → ℝ, IsBrownianReal C μ ∧
      (∀ t, C t =ᵐ[μ] B t) ∧ ∀ᵐ ω ∂μ, ∀ α : ℝ≥0, 0 < α → α < 1 / 2 →
        ∀ T : ℝ≥0, ∃ K : ℝ≥0, HolderOnWith K α (fun t ↦ C t ω) (Set.Icc 0 T) := by
  obtain ⟨C, _, _, hBr, hmod, hH⟩ := exists_continuous_holder_modification hB
  exact ⟨C, hBr, hmod, hH⟩

/-- The shifted process after a finite-valued stopping time. -/
def brownianShift {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : ℝ := B (T ω + t) ω - B (T ω) ω

/-- **08.3**, raw-natural-filtration version: the shifted process is Brownian and its
finite-dimensional laws are independent of the sigma-algebra at the stopping time.
The completed right-continuous augmentation is a separate interface. -/
theorem brownian_strongMarkov {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t)) (hB : IsBrownianReal B μ) (T : Ω → ℝ≥0)
    (hT : IsStoppingTime (Filtration.natural B (fun t ↦ (hm t).stronglyMeasurable))
      (fun ω ↦ (T ω : WithTop ℝ≥0))) :
    IsBrownianReal (brownianShift B T) μ ∧
      ∀ A : Set Ω, MeasurableSet[hT.measurableSpace] A →
      ∀ (n : ℕ) (t : Fin n → ℝ≥0) (S : Set (Fin n → ℝ)), MeasurableSet S →
        μ (A ∩ {ω | (fun i ↦ brownianShift B T (t i) ω) ∈ S}) =
          μ A * μ {ω | (fun i ↦ B (t i) ω) ∈ S} := by
  sorry

/-- **08.4**: the Brownian reflection principle for a strictly positive level, including time zero.
  -/
theorem brownian_reflection {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B μ) {a : ℝ} (ha : 0 < a) (t : ℝ≥0) :
    μ {ω | ∃ s : ℝ≥0, s ≤ t ∧ a ≤ B s ω} = 2 * μ {ω | a ≤ B t ω} := by
  exact reflection_principle μ hB ha t

end CKMA
