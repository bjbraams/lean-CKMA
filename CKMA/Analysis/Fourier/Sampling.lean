/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Bandlimited representatives and Shannon sampling

Inverse Fourier integration over `[-B,B]` gives a continuous representative from any
L² frequency datum. Shannon summands use samples at `k/(2B)` and the normalized sinc
`sin(πt)/(πt)`. Reconstruction converges pointwise, uniformly and in L², and the
representative satisfies an exact sampling Parseval identity. These statements depend
only on the datum inside the integration band.

Source: GAPS 29.58.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory FourierTransform Filter Topology
open scoped BigOperators ENNReal FourierTransform

/-- The continuous representative of inverse Fourier data supported in `[-B,B]`.
For `L²` data on this finite interval the integral is well-defined. -/
def bandlimitedRepresentative (B : ℝ) (u : Lp ℂ 2 (volume : Measure ℝ)) (t : ℝ) : ℂ :=
  ∫ ξ in Set.Icc (-B) B, Complex.exp (2 * Real.pi * Complex.I * t * ξ) * u ξ

/-- The normalized sinc in the sampling convention; Mathlib's `Real.sinc` is unnormalized. -/
def normalizedSinc (t : ℝ) : ℝ := Real.sinc (Real.pi * t)

/-- The `k`th Shannon summand at bandwidth `B`. -/
def shannonTerm (B : ℝ) (f : ℝ → ℂ) (k : ℤ) (t : ℝ) : ℂ :=
  f (k / (2 * B)) * normalizedSinc (2 * B * t - k)

/-- **29.58**: Shannon reconstruction for the integral representative, both pointwise and uniformly.
  -/
theorem shannon_sampling {B : ℝ} (hB : 0 < B)
    (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (∀ t, HasSum (fun k : ℤ ↦ shannonTerm B (bandlimitedRepresentative B u) k t)
      (bandlimitedRepresentative B u t)) ∧
    TendstoUniformly
      (fun s : Finset ℤ ↦ fun t ↦ ∑ k ∈ s, shannonTerm B (bandlimitedRepresentative B u) k t)
      (bandlimitedRepresentative B u) atTop := by
  sorry

/-- The same sampling sums converge in `L²`. -/
theorem shannon_sampling_L2 {B : ℝ} (hB : 0 < B)
    (u : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun s : Finset ℤ ↦ eLpNorm
      (fun t ↦ (∑ k ∈ s, shannonTerm B (bandlimitedRepresentative B u) k t) -
        bandlimitedRepresentative B u t) 2 volume) atTop (𝓝 0) := by
  sorry

/-- Exact sampling Parseval identity. -/
theorem shannon_norm_identity {B : ℝ} (hB : 0 < B)
    (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫⁻ t, ENNReal.ofReal (‖bandlimitedRepresentative B u t‖ ^ 2)) =
      ENNReal.ofReal ((2 * B)⁻¹) * ∑' k : ℤ,
        ENNReal.ofReal (‖bandlimitedRepresentative B u (k / (2 * B))‖ ^ 2) := by
  sorry

end CKMA
