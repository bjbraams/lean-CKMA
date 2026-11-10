/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Volterra equations and fractional integrals

Volterra equations use continuous complex-valued data on a compact real interval and a
continuous triangular kernel, with arbitrary complex coupling. Real Riemann–Liouville integrals
carry the Gamma normalization; positive-order semigroup and inverse statements are a.e. identities
on the open interval. The range criterion uses an absolutely continuous representative vanishing
at the left endpoint. Sources: GAPS 25.18 and 25.23.
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

end CKMA
