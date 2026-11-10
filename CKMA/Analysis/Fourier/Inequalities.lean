/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Hausdorff–Young and coordinate uncertainty

At Mathlib's `exp(-2πi x·ξ)` normalization, the Fourier integral satisfies
Hausdorff–Young on `L¹ ∩ Lᵖ` for `1 ≤ p ≤ 2`; no analogous bound above two holds in
positive dimension even on Schwartz functions. Coordinate uncertainty for unit-norm
L² data bounds the product of the physical and Fourier-side second moments by `1/(4π)`.

Sources: GAPS 27.4 and 27.13.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform

/-- **27.4**: Hausdorff–Young on the dense intersection `L¹ ∩ Lᵖ`, with the `p=1` endpoint.
This formulation uses the Fourier integral; extension to all of `Lᵖ` needs a bounded-map
  construction. -/
theorem hausdorff_young {d : ℕ} {p q : ℝ≥0∞} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hpq : p⁻¹ + q⁻¹ = 1) {f : EuclideanSpace ℝ (Fin d) → ℂ}
    (hf1 : Integrable f volume) (hfp : MemLp f p volume) :
    eLpNorm (𝓕 f) q volume ≤ eLpNorm f p volume := by
  sorry

/-- No Hausdorff–Young bound exists above exponent two in positive Euclidean dimension,
already when tested on Schwartz functions. -/
theorem not_hausdorff_young {d : ℕ} (hd : 0 < d) {p q : ℝ≥0∞}
    (hp : 2 < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    ¬ ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ,
      eLpNorm (𝓕 (f : EuclideanSpace ℝ (Fin d) → ℂ)) q volume ≤
        C * eLpNorm f p volume := by
  sorry

/-- **27.13**: coordinate uncertainty at Mathlib's `exp(-2πix·ξ)` normalization.
The input and Fourier-side second moments are explicit, and the input has unit `L²` norm. -/
theorem heisenberg_uncertainty {d : ℕ} (j : Fin d)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hf : ‖f‖ = 1)
    (hx : MemLp (fun x ↦ (x j : ℂ) * f x) 2 volume)
    (hξ : MemLp (fun ξ ↦ (ξ j : ℂ) * (𝓕 f) ξ) 2 volume) :
    (1 / (4 * Real.pi) : ℝ) ≤
      (eLpNorm (fun x ↦ (x j : ℂ) * f x) 2 volume).toReal *
      (eLpNorm (fun ξ ↦ (ξ j : ℂ) * (𝓕 f) ξ) 2 volume).toReal := by
  sorry

end CKMA
