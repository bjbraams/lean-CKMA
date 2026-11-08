/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Full large deviation bounds and bounded Varadhan (06.62)

`HasLargeDeviationPrinciple` combines lower bounds on open sets and upper bounds on
closed sets at speed `n + 1`. `logProbabilityRate` uses an extended logarithm so that
zero probabilities retain value minus infinity. `IsGoodRateFunction` separately records
lower semicontinuity and compact finite sublevels.

`varadhan` states the Laplace principle for bounded continuous test functions under the
full LDP. Goodness is not required for this bounded form. Both the rate function and
the variational supremum retain their extended values.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped NNReal ENNReal


open MeasureTheory Filter Topology

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- A good rate function has compact finite sublevels and is lower semicontinuous. -/
def IsGoodRateFunction (I : X → ℝ≥0∞) : Prop :=
  LowerSemicontinuous I ∧ ∀ a : ℝ≥0, IsCompact {x | I x ≤ a}

/-- Logarithmic probability at speed `n + 1`. Extended logarithms retain zero probabilities. -/
def logProbabilityRate (P : ℕ → Measure X) (s : Set X) (n : ℕ) : EReal :=
  (((n + 1 : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (P n s)

/-- The open lower and closed upper bounds of a large deviation principle at speed `n + 1`. -/
def HasLargeDeviationPrinciple (P : ℕ → Measure X) (I : X → ℝ≥0∞) : Prop :=
  (∀ s, IsOpen s → -(⨅ x ∈ s, (I x : EReal)) ≤
    liminf (logProbabilityRate P s) atTop) ∧
  (∀ s, IsClosed s → limsup (logProbabilityRate P s) atTop ≤
    -(⨅ x ∈ s, (I x : EReal)))

/-- **06.62**: Varadhan's integral lemma for bounded continuous functions.
The real logarithm on the left is legitimate because each integral is strictly positive.
The extended supremum on the right includes points where `I = ∞`. -/
theorem varadhan [BorelSpace X] (P : ℕ → Measure X)
    [∀ n, IsProbabilityMeasure (P n)] {I : X → ℝ≥0∞}
    (hP : HasLargeDeviationPrinciple P I)
    {f : X → ℝ} (hf : Continuous f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M) :
    Tendsto (fun n : ℕ ↦ (((n + 1 : ℝ)⁻¹ *
      Real.log (∫ x, Real.exp ((n + 1 : ℝ) * f x) ∂P n) : ℝ) : EReal))
      atTop (𝓝 (⨆ x, (f x : EReal) - (I x : EReal))) := by
  sorry

end CKMA
