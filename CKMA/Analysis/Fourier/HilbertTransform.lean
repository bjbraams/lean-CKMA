/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import TauCeti.Analysis.Fourier.RieszTransform.Basic

/-!
# Principal-value Hilbert transforms

Symmetric small-distance truncations use the kernel `1/(π(x-y))`. Their principal
value exists almost everywhere for every finite `p ≥ 1`, obeys a weak (1,1) estimate,
and on `L²` agrees a.e. with TauCeti's one-dimensional Riesz transform
`TauCeti.rieszTransform ℂ (1 : ℝ)`, the `L²` Fourier multiplier with symbol
`-i ξ / |ξ| = -i sign ξ` at Mathlib's Fourier normalization. TauCeti proves the weak `(1, 1)`
bound for its Riesz transforms (`TauCeti.exists_mul_volume_lt_enorm_rieszTransform_le`); with
the a.e. existence of the principal value it gives the weak-type estimate stated here.

Source: GAPS 27.35.

## Main definitions

* `CKMA.truncatedHilbertTransform`: symmetric small-distance truncation of the Hilbert transform.
* `CKMA.hilbertPrincipalValue`: principal-value limit as `ε → 0⁺`.

## Main results

* `CKMA.ae_tendsto_truncatedHilbertTransform`: almost-everywhere existence of the principal-value
  Hilbert transform on `Lᵖ` for `1 ≤ p < ∞` (**27.35**).
* `CKMA.rieszTransform_ae_eq_hilbertPrincipalValue`: on `L²` the principal value is TauCeti's
  Riesz transform, the Fourier multiplier `-i sign ξ`.
* `CKMA.hilbertPrincipalValue_weakType`: weak `(1, 1)` estimate for `hilbertPrincipalValue`.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology FourierTransform
open scoped ENNReal FourierTransform

/-- The symmetric small-distance truncation `π⁻¹ ∫_{|x - y| > ε} f y / (x - y) dy` of the
Hilbert transform. For `ε > 0` and `f ∈ Lᵖ`, `1 ≤ p < ∞`, the integrand is integrable. -/
@[expose]
def truncatedHilbertTransform (ε : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Real.pi : ℂ)⁻¹ * ∫ y in {y : ℝ | ε < |x - y|}, f y / (x - y : ℂ)

/-- Unfolding the truncated Hilbert transform. -/
theorem truncatedHilbertTransform_def (ε : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    truncatedHilbertTransform ε f x =
      (Real.pi : ℂ)⁻¹ * ∫ y in {y : ℝ | ε < |x - y|}, f y / (x - y : ℂ) := rfl

/-- The principal-value limit as `ε → 0⁺`, as `Filter.limUnder`; where the limit does not exist
the value is the junk value of `limUnder`. -/
@[expose]
def hilbertPrincipalValue (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  Filter.limUnder (𝓝[>] (0 : ℝ)) (fun ε ↦ truncatedHilbertTransform ε f x)

/-- Unfolding the principal value. -/
theorem hilbertPrincipalValue_def (f : ℝ → ℂ) (x : ℝ) :
    hilbertPrincipalValue f x =
      Filter.limUnder (𝓝[>] (0 : ℝ)) (fun ε ↦ truncatedHilbertTransform ε f x) := rfl

/-- Where the truncations converge, the principal value is their limit. -/
theorem hilbertPrincipalValue_eq_of_tendsto {f : ℝ → ℂ} {x : ℝ} {c : ℂ}
    (h : Tendsto (fun ε ↦ truncatedHilbertTransform ε f x) (𝓝[>] 0) (𝓝 c)) :
    hilbertPrincipalValue f x = c :=
  h.limUnder_eq

/-- **27.35**: for `f ∈ Lᵖ`, `1 ≤ p < ∞`, the truncations converge almost everywhere, so the
principal value exists a.e. -/
theorem ae_tendsto_truncatedHilbertTransform {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p < ∞)
    {f : ℝ → ℂ} (hf : MemLp f p volume) :
    ∀ᵐ x ∂volume, Tendsto (fun ε ↦ truncatedHilbertTransform ε f x)
      (𝓝[>] 0) (𝓝 (hilbertPrincipalValue f x)) := by
  sorry

/-- On `L²` the principal value is a.e. TauCeti's one-dimensional Riesz transform, the Fourier
multiplier with symbol `-i ξ / |ξ| = -i sign ξ` in Mathlib's Fourier convention. -/
theorem rieszTransform_ae_eq_hilbertPrincipalValue (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (TauCeti.rieszTransform ℂ (1 : ℝ) f : ℝ → ℂ) =ᵐ[volume] hilbertPrincipalValue f := by
  sorry

/-- Weak `(1, 1)` estimate for the principal value: `a · |{|Hf| > a}| ≤ C ‖f‖₁`. -/
theorem hilbertPrincipalValue_weakType : ∃ C : ℝ≥0∞, C ≠ ∞ ∧
    ∀ f : ℝ → ℂ, Integrable f volume → ∀ a : ℝ, 0 < a →
      ENNReal.ofReal a * volume {x | ENNReal.ofReal a < ‖hilbertPrincipalValue f x‖ₑ} ≤
        C * ∫⁻ x, ‖f x‖ₑ := by
  sorry

end CKMA
