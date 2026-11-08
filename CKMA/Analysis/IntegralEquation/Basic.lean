/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Volterra equations, fractional integrals, and compact approximation

Volterra equations use continuous complex-valued data on a compact real interval and a
continuous triangular kernel, with arbitrary complex coupling. Real Riemann–Liouville integrals
carry the Gamma normalization; positive-order semigroup and inverse statements are a.e. identities
on the open interval. The range criterion uses an absolutely continuous representative vanishing
at the left endpoint.

Collectively compact operator approximations combine strong convergence with compact closure of
the union of unit-ball images to control inverses and solutions. Sources: GAPS 25.18, 25.23, and
  25.47.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology

/-- The scalar Volterra integral of a kernel and a function. -/
def volterraIntegral (k : ℝ → ℝ → ℂ) (u : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..t, k t s * u s

/-- **25.18**: a continuous triangular kernel gives a unique continuous solution at every
complex coupling. The series and data-dependence clauses are separate targets. -/
theorem existsUnique_volterra {T : ℝ} (hT : 0 ≤ T) (k : ℝ → ℝ → ℂ)
    (hk : ContinuousOn (fun p : ℝ × ℝ ↦ k p.1 p.2)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}) (c : ℂ) (f : C(Set.Icc 0 T, ℂ)) :
    ∃! u : C(Set.Icc 0 T, ℂ), ∀ t : Set.Icc 0 T,
      u t = f t + c * ∫ s in (0 : ℝ)..t.1,
        k t.1 s * (if hs : s ∈ Set.Icc 0 T then u ⟨s, hs⟩ else 0) := by
  sorry

/-- Riemann–Liouville fractional integration, with the Gamma normalization. -/
def fractionalIntegral (α : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  (Real.Gamma α)⁻¹ * ∫ s in (0 : ℝ)..t, (t - s) ^ (α - 1) * u s

/-- The positive-order fractional integral semigroup, as an a.e. identity. -/
theorem fractionalIntegral_add {T α β : ℝ} (hT : 0 < T) (hα : 0 < α) (hβ : 0 < β)
    {u : ℝ → ℝ} (hu : IntegrableOn u (Set.Ioo 0 T)) :
    fractionalIntegral α (fractionalIntegral β u) =ᵐ[volume.restrict (Set.Ioo 0 T)]
      fractionalIntegral (α + β) u := by
  sorry

/-- **25.23**: the range of `I^α` on `L¹(0,T)` is characterized by an absolutely continuous
representative of `I^(1-α) f` vanishing at zero. -/
theorem mem_range_fractionalIntegral_iff {T α : ℝ} (hT : 0 < T)
    (hα : 0 < α) (hα1 : α < 1) {f : ℝ → ℝ} (hf : IntegrableOn f (Set.Ioo 0 T)) :
    (∃ u : ℝ → ℝ, IntegrableOn u (Set.Ioo 0 T) ∧
      fractionalIntegral α u =ᵐ[volume.restrict (Set.Ioo 0 T)] f) ↔
    ∃ g : ℝ → ℝ, AbsolutelyContinuousOnInterval g 0 T ∧ g 0 = 0 ∧
      g =ᵐ[volume.restrict (Set.Ioo 0 T)] fractionalIntegral (1 - α) f := by
  sorry

/-- Differentiating that absolutely continuous representative gives the inverse. -/
theorem fractionalIntegral_deriv_inverse {T α : ℝ} (hT : 0 < T)
    (hα : 0 < α) (hα1 : α < 1) {f g : ℝ → ℝ}
    (hf : IntegrableOn f (Set.Ioo 0 T)) (hg : AbsolutelyContinuousOnInterval g 0 T)
    (hg0 : g 0 = 0)
    (heq : g =ᵐ[volume.restrict (Set.Ioo 0 T)] fractionalIntegral (1 - α) f) :
    fractionalIntegral α (deriv g) =ᵐ[volume.restrict (Set.Ioo 0 T)] f := by
  sorry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Collective compactness of a sequence of operators. -/
def IsCollectivelyCompact (K : ℕ → E →L[ℂ] E) : Prop :=
  IsCompact (closure (⋃ n, K n '' Metric.closedBall 0 1))

/-- **25.47**: strong collectively compact approximations have uniformly bounded inverses
near an invertible limit. The equivalences witness both bijectivity and bounded inverses. -/
theorem collectivelyCompact_eventually_inverse (K : ℕ → E →L[ℂ] E) (T : E →L[ℂ] E)
    (hc : IsCollectivelyCompact K) (hconv : ∀ x, Tendsto (fun n ↦ K n x) atTop (𝓝 (T x)))
    (S : E ≃L[ℂ] E) (hS : S.toContinuousLinearMap = 1 - T) :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∃ Sₙ : E ≃L[ℂ] E,
      Sₙ.toContinuousLinearMap = 1 - K n ∧ ‖Sₙ.symm.toContinuousLinearMap‖ ≤ C := by
  sorry

/-- Solutions for convergent right-hand sides converge under collectively compact approximation. -/
theorem collectivelyCompact_solution_tendsto (K : ℕ → E →L[ℂ] E) (T : E →L[ℂ] E)
    (hc : IsCollectivelyCompact K) (hconv : ∀ x, Tendsto (fun n ↦ K n x) atTop (𝓝 (T x)))
    (S : E ≃L[ℂ] E) (hS : S.toContinuousLinearMap = 1 - T)
    (f u : ℕ → E) (f₀ : E) (hf : Tendsto f atTop (𝓝 f₀))
    (hu : ∀ᶠ n in atTop, u n - K n (u n) = f n) :
    Tendsto u atTop (𝓝 (S.symm f₀)) := by
  sorry

end CKMA
