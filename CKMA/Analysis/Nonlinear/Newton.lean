/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Newton iteration and Kantorovich convergence

The Newton step uses the totalized inverse of the Fréchet derivative. Convergence statements
supply invertibility on the relevant iterates rather than assuming the totalized inverse always
behaves as an inverse.

The Kantorovich radius includes the affine `L=0` limit. The scalar field is real or complex.
The semilocal statement uses a normalized derivative Lipschitz bound and differentiability on an
open neighborhood of the majorant ball; the local statement gives quadratic convergence near a
regular zero. The initial step length is controlled by a norm bound. Source: GAPS 35.9.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped NNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The majorant root, including the affine `L=0` limit. -/
def kantorovichRadius (L η : ℝ) : ℝ :=
  if L = 0 then η else (1 - Real.sqrt (1 - 2 * L * η)) / L

/-- One Newton step, using Mathlib's totalized operator inverse. Results assert invertibility
on the relevant region; the definition does not invent an inverse when one is unavailable. -/
def newtonStep (F : E → E) (x : E) : E := x - (fderiv 𝕜 F x).inverse (F x)

/-- Newton iterates starting at `x₀`, indexed with the initial guess at zero.
The scalar is supplied explicitly because it does not appear in the iteration type. -/
def newtonIterate (F : E → E) (x₀ : E) (n : ℕ) : E := (newtonStep (𝕜 := 𝕜) F)^[n] x₀

/-- The zeroth iterate is the initial point. -/
@[simp]
theorem newtonIterate_zero (F : E → E) (x₀ : E) : newtonIterate (𝕜 := 𝕜) F x₀ 0 = x₀ := rfl

/-- The successor iterate takes one further Newton step. -/
theorem newtonIterate_succ (F : E → E) (x₀ : E) (n : ℕ) :
    newtonIterate (𝕜 := 𝕜) F x₀ (n + 1) =
      newtonStep (𝕜 := 𝕜) F (newtonIterate (𝕜 := 𝕜) F x₀ n) := by
  exact Function.iterate_succ_apply' _ _ _

/-- **35.9**: Kantorovich convergence under the normalized derivative Lipschitz bound.
Differentiability is at all points of an open neighbourhood of the majorant ball. -/
theorem newton_kantorovich [CompleteSpace E] {F : E → E} (x₀ : E) (S : E ≃L[𝕜] E)
    (hS : fderiv 𝕜 F x₀ = S.toContinuousLinearMap)
    {L η r : ℝ} (hL : 0 ≤ L) (hsmall : L * η < 1 / 2)
    (hr : kantorovichRadius L η ≤ r) (hrpos : 0 < r)
    (hfirst : ‖S.symm (F x₀)‖ ≤ η)
    {U : Set E} (hU : IsOpen U) (hsub : Metric.closedBall x₀ r ⊆ U)
    (hF : DifferentiableOn 𝕜 F U)
    (hLip : ∀ x ∈ Metric.closedBall x₀ r, ∀ y ∈ Metric.closedBall x₀ r,
      ‖S.symm.toContinuousLinearMap.comp (fderiv 𝕜 F x - fderiv 𝕜 F y)‖ ≤ L * ‖x - y‖) :
    ∃ z ∈ Metric.closedBall x₀ (kantorovichRadius L η), F z = 0 ∧
      Tendsto (newtonIterate (𝕜 := 𝕜) F x₀) atTop (𝓝 z) ∧
      ∀ n, (fderiv 𝕜 F (newtonIterate (𝕜 := 𝕜) F x₀ n)).IsInvertible := by
  sorry

/-- Local quadratic convergence near a regular zero with Lipschitz derivative. -/
theorem newton_quadratic [CompleteSpace E] {F : E → E} {z : E} (hz : F z = 0)
    (S : E ≃L[𝕜] E) (hS : fderiv 𝕜 F z = S.toContinuousLinearMap)
    {r : ℝ} (hr : 0 < r) (hF : DifferentiableOn 𝕜 F (Metric.ball z r))
    {L : ℝ≥0} (hLip : LipschitzOnWith L (fderiv 𝕜 F) (Metric.ball z r)) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ x₀ ∈ Metric.ball z δ,
      Tendsto (newtonIterate (𝕜 := 𝕜) F x₀) atTop (𝓝 z) ∧
      ∀ n, ‖newtonIterate (𝕜 := 𝕜) F x₀ (n + 1) - z‖ ≤
        C * ‖newtonIterate (𝕜 := 𝕜) F x₀ n - z‖ ^ 2 := by
  sorry

end CKMA
