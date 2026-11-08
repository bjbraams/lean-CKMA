/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Basic

/-!
# Principal-value Hilbert transforms

Symmetric small-distance truncations use the kernel `1/(π(x-y))`. Their principal
value exists almost everywhere for every finite `p ≥ 1`, obeys a weak (1,1) estimate,
and on L² is the Fourier multiplier `-i sign` at Mathlib's Fourier normalization.
The multiplier identity uses the bundled L² Fourier unitary.

Source: GAPS 27.35.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology FourierTransform
open scoped ENNReal FourierTransform

/-- The symmetric small-distance truncation of the Hilbert transform.
For positive epsilon the tail integral is absolutely integrable on Lp, 1<=p<infinity. -/
def truncatedHilbertTransform (ε : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Real.pi : ℂ)⁻¹ * ∫ y in {y : ℝ | ε < |x - y|}, f y / (x - y : ℂ)

/-- The totalized principal-value limit; convergence is supplied separately. -/
def hilbertPrincipalValue (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  Filter.limUnder (𝓝[>] (0 : ℝ)) (fun ε ↦ truncatedHilbertTransform ε f x)

/-- **27.35**: the principal value exists almost everywhere for every finite p>=1. -/
theorem ae_tendsto_truncatedHilbertTransform {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p < ∞)
    {f : ℝ → ℂ} (hf : MemLp f p volume) :
    ∀ᵐ x ∂volume, Tendsto (fun ε ↦ truncatedHilbertTransform ε f x)
      (𝓝[>] 0) (𝓝 (hilbertPrincipalValue f x)) := by
  sorry

/-- The principal value is the L2 multiplier `-i sign`, in Mathlib's Fourier convention. -/
theorem existsUnique_hilbertTransform_L2 (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∃! Hf : Lp ℂ 2 (volume : Measure ℝ),
      Hf =ᵐ[volume] hilbertPrincipalValue f ∧
      (Lp.fourierTransformₗᵢ ℝ ℂ Hf : ℝ → ℂ) =ᵐ[volume]
        (fun ξ ↦ -(Complex.I * (SignType.sign ξ : ℂ)) * (𝓕 f) ξ) := by
  sorry

/-- Weak (1,1) control of the actual principal-value function. -/
theorem hilbertPrincipalValue_weakType : ∃ C : ℝ≥0∞, C ≠ ∞ ∧
    ∀ f : ℝ → ℂ, Integrable f volume → ∀ a : ℝ, 0 < a →
      ENNReal.ofReal a * volume {x | ENNReal.ofReal a < ‖hilbertPrincipalValue f x‖ₑ} ≤
        C * ∫⁻ x, ‖f x‖ₑ := by
  sorry

end CKMA
