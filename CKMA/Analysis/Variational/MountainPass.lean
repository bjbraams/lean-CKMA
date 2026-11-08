/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Order.Filter.Basic
public import Mathlib.Tactic

/-!
# Palais–Smale compactness and mountain-pass critical points

Continuous paths from zero to a second well define the mountain-pass minimax level.
Positive energy on a separating sphere and negative endpoint energy give a positive
barrier. A C¹ functional on a real Banach space has a critical point at this level
when the Palais–Smale subsequence condition holds there. Compact paths, derivatives
and filter convergence use Mathlib. Source: GAPS 36.35.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Palais–Smale condition at a real energy level, with strong convergence of a subsequence. -/
def HasPalaisSmaleAt (I : E → ℝ) (c : ℝ) : Prop :=
  ∀ u : ℕ → E, Tendsto (fun n ↦ I (u n)) atTop (𝓝 c) →
    Tendsto (fun n ↦ fderiv ℝ I (u n)) atTop (𝓝 0) →
    ∃ (φ : ℕ → ℕ) (x : E), StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x)

/-- Continuous paths joining zero to the second well, parameterized on `[0,1]`. -/
def mountainPassPaths (e : E) : Set C(Set.Icc (0 : ℝ) 1, E) :=
  {γ | γ ⟨0, by norm_num⟩ = 0 ∧ γ ⟨1, by norm_num⟩ = e}

/-- The real supremum of energy along a compact path. When the energy functional
is continuous, as in the mountain-pass theorem, this is its attained maximum. -/
def pathMaxEnergy (I : E → ℝ) (γ : C(Set.Icc (0 : ℝ) 1, E)) : ℝ :=
  sSup (Set.range (fun t ↦ I (γ t)))

/-- The mountain-pass minimax level. Under the theorem's hypotheses the infimum is finite
and every path crosses the positive-energy sphere. -/
def mountainPassLevel (I : E → ℝ) (e : E) : ℝ :=
  sInf (pathMaxEnergy I '' mountainPassPaths e)

/-- **36.35**: mountain-pass geometry and Palais–Smale compactness produce a critical point
at the minimax level. The Palais–Smale condition is needed only at that level. -/
theorem exists_mountainPass_criticalPoint [CompleteSpace E] (I : E → ℝ)
    (hI : ContDiff ℝ 1 I) (hzero : I 0 = 0) {r α : ℝ} (hr : 0 < r) (hα : 0 < α)
    (hbarrier : ∀ x : E, ‖x‖ = r → α ≤ I x) {e : E} (he : r < ‖e‖)
    (hIe : I e < 0) (hPS : HasPalaisSmaleAt I (mountainPassLevel I e)) :
    α ≤ mountainPassLevel I e ∧ ∃ x, I x = mountainPassLevel I e ∧ fderiv ℝ I x = 0 := by
  sorry

end CKMA
