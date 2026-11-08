/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.AbsolutelySumming
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Pietsch domination on the weak-star dual ball

The absolutely summing gauge is TauCeti's `ContinuousLinearMap.summingENorm`. For finite
exponents at least one, Pietsch domination represents its bound by integration against a regular
Borel probability measure on the dual unit ball. The ball carries the weak-star subspace
topology, rather than the operator norm topology; no completeness assumption on the original
normed spaces is imposed. Source: GAPS 17.54.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The dual unit ball with its weak-star subspace topology, not its operator norm topology. -/
abbrev WeakStarDualBall (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  {ℓ : WeakDual ℝ E // ‖WeakDual.toStrongDual ℓ‖ ≤ 1}

/-- **17.54**, Pietsch domination, reusing TauCeti's exact extended summing norm.
The measure is a regular Borel probability on the weak-star dual ball. -/
theorem pietsch_domination {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p < ∞)
    (T : E →L[ℝ] F) {C : ℝ} (hC : 0 ≤ C) :
    letI : MeasurableSpace (WeakStarDualBall E) := borel (WeakStarDualBall E)
    T.summingENorm p ≤ ENNReal.ofReal C ↔
      ∃ μ : Measure (WeakStarDualBall E),
        IsProbabilityMeasure μ ∧ μ.InnerRegular ∧
        ∀ x : E, ‖T x‖ ≤ C *
          (∫ ℓ : WeakStarDualBall E, |ℓ.1 x| ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
  sorry

end CKMA
