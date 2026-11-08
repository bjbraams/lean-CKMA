/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Convex.Proximal
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Ekeland's variational principle

The objective is extended-real valued, lower semicontinuous, and bounded below by a real
constant on a complete metric space. A finite approximate minimizer and positive error and
distance scales determine a nearby finite point satisfying a strict penalized variational
inequality. The real lower bound and finite initial value already imply properness.
Source: GAPS 12.45.
-/

@[expose] public section

noncomputable section

namespace CKMA

/-- Ekeland's strict variational inequality at a selected point. -/
def IsEkelandPoint {X : Type*} [MetricSpace X] (f : X → EReal) (a : ℝ) (x : X) : Prop :=
  f x ≠ ⊥ ∧ f x ≠ ⊤ ∧ ∀ y, y ≠ x → f x - (a * dist y x : ℝ) < f y

/-- **12.45**: Ekeland's variational principle with explicit positive error and distance scales.
Properness, a finite initial value and a real lower bound prevent arithmetic with `-∞`. -/
theorem exists_ekelandPoint {X : Type*} [MetricSpace X] [CompleteSpace X]
    (f : X → EReal) (hl : LowerSemicontinuous f)
    (hbelow : ∃ b : ℝ, ∀ x, (b : EReal) ≤ f x)
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) {x₀ : X}
    (hfinite : f x₀ ≠ ⊤) (happrox : f x₀ ≤ (⨅ x, f x) + (ε : ℝ)) :
    ∃ x, dist x x₀ ≤ r ∧ f x ≤ f x₀ ∧ IsEkelandPoint f (ε / r) x := by
  sorry

end CKMA
