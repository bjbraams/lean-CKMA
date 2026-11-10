/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Laurent series on annuli

Contour integrals on positively oriented circles define Laurent coefficients.
Holomorphic functions on annuli have bilateral expansions, independent of the chosen
intermediate circle, and normal convergence on compact subsets.

Source: GAPS 40.25. Circle integration reuses Mathlib's Cauchy integral API.
Normal summability is the predicate from `CKMA.Analysis.Complex.Basic`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped BigOperators

/-- The open annulus with finite real inner and outer radii. -/
def complexAnnulus (a : ℂ) (r R : ℝ) : Set ℂ := {z | r < ‖z - a‖ ∧ ‖z - a‖ < R}

/-- Laurent coefficient computed on the positively oriented circle of radius `ρ`. -/
def laurentCoefficient (f : ℂ → ℂ) (a : ℂ) (ρ : ℝ) (n : ℤ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * ∮ z in C(a, ρ), (z - a) ^ (-n - 1) * f z

/-- **40.25**: Laurent expansion at each point of an annulus. -/
theorem hasSum_laurentSeries {f : ℂ → ℂ} {a : ℂ} {r R ρ : ℝ}
    (hr : 0 ≤ r) (hf : DifferentiableOn ℂ f (complexAnnulus a r R))
    (hρ : r < ρ) (hρR : ρ < R) {z : ℂ} (hz : z ∈ complexAnnulus a r R) :
    HasSum (fun n : ℤ ↦ laurentCoefficient f a ρ n * (z - a) ^ n) (f z) := by
  sorry

/-- The Laurent expansion is normal on compact subannuli. -/
theorem normallySummableOn_laurentSeries {f : ℂ → ℂ} {a : ℂ} {r R ρ : ℝ}
    (hr : 0 ≤ r) (hf : DifferentiableOn ℂ f (complexAnnulus a r R))
    (hρ : r < ρ) (hρR : ρ < R) :
    NormallySummableOn (fun n : ℤ ↦ fun z ↦ laurentCoefficient f a ρ n * (z - a) ^ n)
      (complexAnnulus a r R) := by
  sorry

/-- The contour coefficient is independent of the intervening circle. -/
theorem laurentCoefficient_eq {f : ℂ → ℂ} {a : ℂ} {r R ρ σ : ℝ}
    (hr : 0 ≤ r) (hf : DifferentiableOn ℂ f (complexAnnulus a r R))
    (hρ : r < ρ) (hρR : ρ < R) (hσ : r < σ) (hσR : σ < R) :
    laurentCoefficient f a ρ = laurentCoefficient f a σ := by
  sorry

/-- A normally converging Laurent representation has exactly the contour coefficients. -/
theorem eq_laurentCoefficient {f : ℂ → ℂ} {a : ℂ} {r R ρ : ℝ} (c : ℤ → ℂ)
    (hr : 0 ≤ r) (hρ : r < ρ) (hρR : ρ < R)
    (hn : NormallySummableOn (fun n : ℤ ↦ fun z ↦ c n * (z - a) ^ n)
      (complexAnnulus a r R))
    (hs : ∀ z ∈ complexAnnulus a r R, HasSum (fun n : ℤ ↦ c n * (z - a) ^ n) (f z)) :
    c = laurentCoefficient f a ρ := by
  sorry

end CKMA
