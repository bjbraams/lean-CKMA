/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.InfinitelyDivisible.Basic
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Sequences

/-!
# Probability measures from convergent characteristic functions

Pointwise convergence of characteristic functions to a limit continuous at the origin produces a
probability measure with that characteristic function, by tightness, Prokhorov compactness, and
Lévy's continuity theorem along a weakly convergent subsequence.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

/-- A pointwise limit of characteristic functions, continuous at `0`, is a characteristic
function. -/
lemma exists_isProbabilityMeasure_of_tendsto_charFun {μ : ℕ → Measure ℝ}
    [∀ n, IsProbabilityMeasure (μ n)] {f : ℝ → ℂ} (hf : ContinuousAt f 0)
    (h : ∀ t, Tendsto (fun n => charFun (μ n) t) atTop (𝓝 (f t))) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ charFun ν = f := by
  have htight : IsTightMeasureSet (Set.range μ) :=
    isTightMeasureSet_of_tendsto_charFun hf h
  let P : ℕ → ProbabilityMeasure ℝ := fun n => ⟨μ n, inferInstance⟩
  have hcompact : IsCompact (closure (Set.range P)) := by
    apply isCompact_closure_of_isTightMeasureSet
    convert htight using 1
    ext m
    constructor
    · rintro ⟨p, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨P n, ⟨n, rfl⟩, rfl⟩
  obtain ⟨ν, -, φ, hφ, hlim⟩ :=
    hcompact.tendsto_subseq fun n => subset_closure (mem_range_self n)
  have hsub := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hlim
  have hchar : ∀ t, charFun (ν : Measure ℝ) t = f t := fun t =>
    tendsto_nhds_unique (hsub t) ((h t).comp hφ.tendsto_atTop)
  exact ⟨(ν : Measure ℝ), ν.prop, funext hchar⟩

end CKMA
