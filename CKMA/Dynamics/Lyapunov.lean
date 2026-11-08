/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.Flow
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Dynamics.OmegaLimit
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Lyapunov stability and LaSalle invariance (31.24, 31.26)

The derivative `lyapunovDerivative` is evaluated along an explicit generator of an
existing global flow. The local positive-definite criteria imply metric stability and,
for a strictly decreasing function, local attraction. Finite dimension supplies the
compactness needed for these local criteria.

LaSalle's principle uses a compact positively invariant set and the largest full-flow
invariant subset of the zero-derivative locus. It makes no finiteness assumption on the
rest set. Common flow, stability and invariant-subset definitions are in `CKMA.Dynamics.Flow`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Derivative of `V` along the vector field. -/
def lyapunovDerivative (F : E → E) (V : E → ℝ) (x : E) : ℝ := fderiv ℝ V x (F x)

/-- **31.24**: the non-strict Lyapunov criterion, stated for an existing flow.
Local ODE construction and continuation are not conclusions of this interface. -/
theorem isLyapunovStable_of_lyapunov [FiniteDimensional ℝ E]
    (ϕ : Flow ℝ E) (F : E → E) (V : E → ℝ) (x₀ : E)
    (hflow : FlowHasGenerator ϕ F)
    (heq : ∀ t, ϕ t x₀ = x₀) {r : ℝ} (hr : 0 < r)
    (hV : ContDiffOn ℝ 1 V (Metric.ball x₀ r)) (hV₀ : V x₀ = 0)
    (hpos : ∀ x ∈ Metric.ball x₀ r, x ≠ x₀ → 0 < V x)
    (hdec : ∀ x ∈ Metric.ball x₀ r, lyapunovDerivative F V x ≤ 0) :
    IsLyapunovStable ϕ x₀ := by
  sorry

/-- The strict Lyapunov criterion implies local asymptotic stability. -/
theorem isLocallyAttracting_of_strict_lyapunov [FiniteDimensional ℝ E]
    (ϕ : Flow ℝ E) (F : E → E) (V : E → ℝ) (x₀ : E)
    (hflow : FlowHasGenerator ϕ F)
    (heq : ∀ t, ϕ t x₀ = x₀) {r : ℝ} (hr : 0 < r)
    (hF : ContinuousOn F (Metric.ball x₀ r))
    (hV : ContDiffOn ℝ 1 V (Metric.ball x₀ r)) (hV₀ : V x₀ = 0)
    (hpos : ∀ x ∈ Metric.ball x₀ r, x ≠ x₀ → 0 < V x)
    (hdec : ∀ x ∈ Metric.ball x₀ r, x ≠ x₀ → lyapunovDerivative F V x < 0) :
    IsLyapunovStable ϕ x₀ ∧ IsLocallyAttracting ϕ x₀ := by
  sorry

/-- **31.26**: LaSalle on a compact positively invariant set, without a finite-rest-set hypothesis.
  -/
theorem lasalle (ϕ : Flow ℝ E) (F : E → E) (V : E → ℝ)
    (hflow : FlowHasGenerator ϕ F)
    (hF : Continuous F) (hV : ContDiff ℝ 1 V)
    (K : Set E) (hK : IsCompact K) (hinv : ∀ t : ℝ, 0 ≤ t → Set.MapsTo (ϕ t) K K)
    (hdec : ∀ x ∈ K, lyapunovDerivative F V x ≤ 0) {x : E} (hx : x ∈ K) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop,
      ∃ y ∈ largestInvariantSubset ϕ {z ∈ K | lyapunovDerivative F V z = 0},
        dist (ϕ t x) y < ε := by
  sorry

end CKMA
