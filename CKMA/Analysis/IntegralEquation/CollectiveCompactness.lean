/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Compactness.Compact

/-!
# Collectively compact approximation

Collectively compact operator approximations combine strong convergence with compact closure of
the union of unit-ball images. The scalar field is real or complex. The statements control
inverses of `1 - Kₙ` and convergence of solutions.
Source: GAPS 25.47.
-/

@[expose] public section

namespace CKMA

open Filter Topology

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- Collective compactness of a sequence of operators. -/
def IsCollectivelyCompact (K : ℕ → E →L[𝕜] E) : Prop :=
  IsCompact (closure (⋃ n, K n '' Metric.closedBall 0 1))

/-- **25.47**: strong collectively compact approximations have uniformly bounded inverses
near an invertible limit. The equivalences witness both bijectivity and bounded inverses. -/
theorem collectivelyCompact_eventually_inverse (K : ℕ → E →L[𝕜] E) (T : E →L[𝕜] E)
    (hc : IsCollectivelyCompact K) (hconv : ∀ x, Tendsto (fun n ↦ K n x) atTop (𝓝 (T x)))
    (S : E ≃L[𝕜] E) (hS : S.toContinuousLinearMap = 1 - T) :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∃ Sₙ : E ≃L[𝕜] E,
      Sₙ.toContinuousLinearMap = 1 - K n ∧ ‖Sₙ.symm.toContinuousLinearMap‖ ≤ C := by
  sorry

/-- Solutions for convergent right-hand sides converge under collectively compact approximation. -/
theorem collectivelyCompact_solution_tendsto (K : ℕ → E →L[𝕜] E) (T : E →L[𝕜] E)
    (hc : IsCollectivelyCompact K) (hconv : ∀ x, Tendsto (fun n ↦ K n x) atTop (𝓝 (T x)))
    (S : E ≃L[𝕜] E) (hS : S.toContinuousLinearMap = 1 - T)
    (f u : ℕ → E) (f₀ : E) (hf : Tendsto f atTop (𝓝 f₀))
    (hu : ∀ᶠ n in atTop, u n - K n (u n) = f n) :
    Tendsto u atTop (𝓝 (S.symm f₀)) := by
  sorry

end CKMA
