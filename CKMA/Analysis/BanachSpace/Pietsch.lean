/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.AbsolutelySumming.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Analysis.Normed.Operator.AbsolutelySumming.Pietsch

/-!
# Pietsch domination on the weak-star dual ball

The absolutely summing gauge is TauCeti's `ContinuousLinearMap.summingENorm`. For finite
exponents at least one, Pietsch domination represents its bound by integration against a regular
Borel probability measure on the dual unit ball. The ball carries the weak-star subspace
topology, rather than the operator norm topology; no completeness assumption on the original
normed spaces is imposed. Source: GAPS 17.54.

The domination bound and its converse use TauCeti's Pietsch theorem, with the
dual ball identified by its norm inequality and its induced Borel structure.

## Main definitions

* `CKMA.WeakStarDualBall`: the unit ball of the continuous dual equipped with the weak-star
  subspace topology.

## Main results

* `CKMA.pietsch_domination`: Pietsch's domination theorem for `p`-summing operators.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped ENNReal

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The dual unit ball with its weak-star subspace topology, not its operator norm topology. -/
@[expose]
abbrev WeakStarDualBall (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] :=
  {ℓ : WeakDual 𝕜 E // ‖WeakDual.toStrongDual ℓ‖ ≤ 1}

/-- **17.54**, Pietsch domination, reusing TauCeti's exact extended summing norm.
The measure is a regular Borel probability on the weak-star dual ball. -/
theorem pietsch_domination {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p < ∞)
    (T : E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C) :
    letI : MeasurableSpace (WeakStarDualBall 𝕜 E) := borel (WeakStarDualBall 𝕜 E)
    T.summingENorm p ≤ ENNReal.ofReal C ↔
      ∃ μ : Measure (WeakStarDualBall 𝕜 E),
        IsProbabilityMeasure μ ∧ μ.InnerRegular ∧
        ∀ x : E, ‖T x‖ ≤ C *
          (∫ ℓ : WeakStarDualBall 𝕜 E, ‖ℓ.1 x‖ ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
  let _ : MeasurableSpace (WeakDual 𝕜 E) := borel _
  let _ : BorelSpace (WeakDual 𝕜 E) := ⟨rfl⟩
  let ball := WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 E) 1
  have hdomination (S : Set (WeakDual 𝕜 E)) (m : MeasurableSpace S) (hS : S = ball)
      (hm : m = (borel (WeakDual 𝕜 E)).comap (Subtype.val : S → WeakDual 𝕜 E)) :
      letI : MeasurableSpace S := m
      T.summingENorm p ≤ ENNReal.ofReal C ↔ ∃ μ : Measure S,
        IsProbabilityMeasure μ ∧ μ.InnerRegular ∧ ∀ x : E,
          ‖T x‖ ≤ C * (∫ ℓ, ‖ℓ.1 x‖ ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
    subst S
    subst m
    constructor
    · intro hT
      obtain ⟨μ, hμ, hregular, hbound⟩ :=
        ContinuousLinearMap.exists_isProbabilityMeasure_of_summingENorm_le_ofReal hp.ne hC hT
      exact ⟨μ, hμ, inferInstance, hbound⟩
    · rintro ⟨μ, hμ, -, hbound⟩
      exact ContinuousLinearMap.summingENorm_le_ofReal_of_norm_le_integral hp.ne hC μ hbound
  exact hdomination {ℓ | ‖WeakDual.toStrongDual ℓ‖ ≤ 1} (borel _)
    (Set.ext fun _ ↦ by simp [ball, Metric.mem_closedBall]) borel_comap

end CKMA
