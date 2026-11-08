/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Data.EReal.Operations
public import Mathlib.Order.LiminfLimsup

/-!
# Clarke directional derivatives and generalized gradients

The generalized directional derivative takes a joint limsup as the base point approaches the
given point and the positive step tends to zero. It takes values in the extended reals.
The generalized gradient consists of continuous linear functionals bounded above by this
directional derivative in every direction.

For a finite-dimensional real space and a function Lipschitz on a neighborhood, the gradient is
the closed convex hull of limits of ordinary derivatives. Its support function is the generalized
directional derivative. Source: GAPS 12.50.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Clarke's generalized directional derivative, with a joint limit in base point and
positive step size. Extended reals avoid totalizing an unbounded real limsup. -/
def clarkeDirectionalDerivative (f : E → ℝ) (x d : E) : EReal :=
  limsup (fun p : E × ℝ ↦ (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal))
    (𝓝[Set.univ ×ˢ Set.Ioi 0] (x, 0))

/-- The Clarke generalized gradient in the continuous dual. -/
def clarkeSubdifferential (f : E → ℝ) (x : E) : Set (StrongDual ℝ E) :=
  {u | ∀ d : E, (u d : EReal) ≤ clarkeDirectionalDerivative f x d}

/-- Limits of ordinary derivatives at differentiability points approaching `x`. -/
def reachableDerivatives (f : E → ℝ) (x : E) : Set (StrongDual ℝ E) :=
  {u | ∃ y : ℕ → E, Tendsto y atTop (𝓝 x) ∧
    (∀ n, DifferentiableAt ℝ f (y n)) ∧
    Tendsto (fun n ↦ fderiv ℝ f (y n)) atTop (𝓝 u)}

/-- **12.50**: the finite-dimensional Clarke gradient is the closed convex hull of
reachable derivatives and is nonempty compact convex. Local Lipschitz control is
stated on one neighbourhood, not assumed globally. -/
theorem clarkeSubdifferential_representation [FiniteDimensional ℝ E]
    {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Metric.ball x r)) :
    (clarkeSubdifferential f x).Nonempty ∧ IsCompact (clarkeSubdifferential f x) ∧
      Convex ℝ (clarkeSubdifferential f x) ∧
      clarkeSubdifferential f x = closure (convexHull ℝ (reachableDerivatives f x)) := by
  sorry

/-- The support function of the generalized gradient is the generalized directional derivative. -/
theorem sSup_clarkeSubdifferential_eq [FiniteDimensional ℝ E]
    {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Metric.ball x r)) (d : E) :
    ((sSup ((fun u ↦ u d) '' clarkeSubdifferential f x) : ℝ) : EReal) =
      clarkeDirectionalDerivative f x d := by
  sorry

end CKMA
