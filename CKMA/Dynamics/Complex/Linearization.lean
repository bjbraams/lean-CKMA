/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Koenigs and Böttcher local conjugacies (46.10, 46.11)

`IsKoenigsCoordinate` and `IsBoettcherCoordinate` express analytic conjugacies near a
fixed point at zero. The Koenigs interface uses a nonzero multiplier off the unit circle;
the Böttcher interface uses the exact superattracting order and a compatible leading root.

Existence and uniqueness are statements about germs: equality is eventual near zero,
with the root-of-unity ambiguity specified in the superattracting case. Global
conjugacies or convergence on the entire basin are not assumed.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology

/-- A normalized Koenigs coordinate at a fixed point placed at the origin. -/
def IsKoenigsCoordinate (f : ℂ → ℂ) (c : ℂ) (φ : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ f 0 ∧ f 0 = 0 ∧ AnalyticAt ℂ φ 0 ∧ φ 0 = 0 ∧ deriv φ 0 = 1 ∧
    ∀ᶠ z in 𝓝 (0 : ℂ), φ (f z) = c * φ z

/-- **46.10**: local analytic linearization at an attracting or repelling nonzero multiplier.
The derivative-one normalization guarantees a local analytic inverse. -/
theorem exists_koenigsCoordinate {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hf₀ : f 0 = 0) (hc : deriv f 0 ≠ 0) (hunit : ‖deriv f 0‖ ≠ 1) :
    ∃ φ, IsKoenigsCoordinate f (deriv f 0) φ := by
  sorry

/-- Uniqueness means equality as germs, since the coordinate away from zero is arbitrary. -/
theorem koenigsCoordinate_eventuallyEq {f φ ψ : ℂ → ℂ} {c : ℂ}
    (hc : c ≠ 0) (hunit : ‖c‖ ≠ 1)
    (hφ : IsKoenigsCoordinate f c φ) (hψ : IsKoenigsCoordinate f c ψ) :
    φ =ᶠ[𝓝 (0 : ℂ)] ψ := by
  sorry

/-- A local analytic Böttcher coordinate, without a derivative normalization. -/
def IsBoettcherCoordinate (f : ℂ → ℂ) (k : ℕ) (φ : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ f 0 ∧ f 0 = 0 ∧ AnalyticAt ℂ φ 0 ∧ φ 0 = 0 ∧ deriv φ 0 ≠ 0 ∧
    ∀ᶠ z in 𝓝 (0 : ℂ), φ (f z) = φ z ^ k

/-- **46.11**: existence with a prescribed compatible leading coefficient.
The factorization hypothesis expresses exact order `k`, including its nonzero leading term. -/
theorem exists_boettcherCoordinate {f g : ℂ → ℂ} {k : ℕ} (hk : 2 ≤ k)
    (hg : AnalyticAt ℂ g 0) (hg₀ : g 0 ≠ 0)
    (hf : ∀ᶠ z in 𝓝 (0 : ℂ), f z = z ^ k * g z)
    {c : ℂ} (hc : c ^ (k - 1) = g 0) :
    ∃ φ, IsBoettcherCoordinate f k φ ∧ deriv φ 0 = c := by
  sorry

/-- Böttcher coordinates differ by a `(k-1)`st root of unity. -/
theorem boettcherCoordinate_unique_up_to_root {f φ ψ : ℂ → ℂ} {k : ℕ} (hk : 2 ≤ k)
    (hφ : IsBoettcherCoordinate f k φ) (hψ : IsBoettcherCoordinate f k ψ) :
    ∃ ζ : ℂ, ζ ^ (k - 1) = 1 ∧ ∀ᶠ z in 𝓝 (0 : ℂ), ψ z = ζ * φ z := by
  sorry

end CKMA
