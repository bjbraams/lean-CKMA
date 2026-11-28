/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Weak Euler–Lagrange first variation

Integral actions `∫ L(x, u(x), U(x)) dμ` with a supplied derivative field `U`, and their first
variation along `(u, U) + t (φ, Dφ)`. Under a local domination hypothesis on the derivative of
the Lagrangian along the variation, the action is differentiable in `t` (Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`), and at a local minimizer the integral of
the first-variation integrand vanishes. Source: GAPS 36.1.

## Main definitions

* `CKMA.variationalAction`: integral action functional `∫ L(x, u(x), U(x)) dμ`.
* `CKMA.firstVariationIntegrand`: directional derivative of the Lagrangian with respect to `(u, U)`
  in direction `(φ, Dφ)`.

## Main results

* `CKMA.hasDerivAt_variationalAction`: differentiation of the action along the variation under
  the integral sign.
* `CKMA.integral_firstVariation_eq_zero`: at a local minimizer the first-variation integrand is
  integrable and its integral vanishes (**36.1**).

## Implementation notes

The direction of the derivative variable is `fderiv ℝ φ`, which is the derivative of `φ` when
`φ` is differentiable and `0` elsewhere; the statements hold for every `φ`.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The integral action with a supplied weak derivative field. -/
@[expose]
def variationalAction [MeasurableSpace E] (μ : Measure E) (L : E → ℝ → (E →L[ℝ] ℝ) → ℝ)
    (u : E → ℝ) (U : E → E →L[ℝ] ℝ) : ℝ := ∫ x, L x (u x) (U x) ∂μ

/-- Defining equation of `variationalAction`. -/
theorem variationalAction_def [MeasurableSpace E] (μ : Measure E) (L : E → ℝ → (E →L[ℝ] ℝ) → ℝ)
    (u : E → ℝ) (U : E → E →L[ℝ] ℝ) :
    variationalAction μ L u U = ∫ x, L x (u x) (U x) ∂μ := rfl

/-- The first variation integrand, differentiating the value and derivative variables together. -/
@[expose]
def firstVariationIntegrand (L : E → ℝ → (E →L[ℝ] ℝ) → ℝ)
    (u : E → ℝ) (U : E → E →L[ℝ] ℝ) (φ : E → ℝ) (x : E) : ℝ :=
  fderiv ℝ (fun p : ℝ × (E →L[ℝ] ℝ) ↦ L x p.1 p.2) (u x, U x)
    (φ x, fderiv ℝ φ x)

/-- Defining equation of `firstVariationIntegrand`. -/
theorem firstVariationIntegrand_def (L : E → ℝ → (E →L[ℝ] ℝ) → ℝ)
    (u : E → ℝ) (U : E → E →L[ℝ] ℝ) (φ : E → ℝ) (x : E) :
    firstVariationIntegrand L u U φ x =
      fderiv ℝ (fun p : ℝ × (E →L[ℝ] ℝ) ↦ L x p.1 p.2) (u x, U x) (φ x, fderiv ℝ φ x) := rfl

/-- The first-variation integrand of the varied pair `(u + t φ, U + t Dφ)` is the derivative in
`t` of the Lagrangian along the variation. -/
theorem hasDerivAt_lagrangian_variation {L : E → ℝ → (E →L[ℝ] ℝ) → ℝ}
    {u : E → ℝ} {U : E → E →L[ℝ] ℝ} {φ : E → ℝ} {x : E}
    (hL : Differentiable ℝ (fun p : ℝ × (E →L[ℝ] ℝ) ↦ L x p.1 p.2)) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ L x (u x + s * φ x) (U x + s • fderiv ℝ φ x))
      (firstVariationIntegrand L (fun y ↦ u y + t * φ y) (fun y ↦ U y + t • fderiv ℝ φ y) φ x)
      t := by
  have hcurve : HasDerivAt (fun s : ℝ ↦ (u x + s * φ x, U x + s • fderiv ℝ φ x))
      (φ x, fderiv ℝ φ x) t := by
    refine HasDerivAt.prodMk ?_ ?_
    · simpa using ((hasDerivAt_id t).mul_const (φ x)).const_add (u x)
    · simpa using ((hasDerivAt_id t).smul_const (fderiv ℝ φ x)).const_add (U x)
  exact (hL _).hasFDerivAt.comp_hasDerivAt t hcurve

/-- **Differentiation of the action under the integral sign.** If the Lagrangian is
differentiable in `(u, U)` for every `x`, the integrands of the varied actions are
a.e. strongly measurable, the unvaried integrand is integrable, and the first-variation
integrands of the varied pairs `(u + t φ, U + t Dφ)`, `t` in a neighbourhood `s` of `0`, are
dominated by an integrable `bound`, then the first-variation integrand is integrable and the
action is differentiable at `t = 0` with derivative its integral. -/
theorem hasDerivAt_variationalAction [MeasurableSpace E] {μ : Measure E}
    {L : E → ℝ → (E →L[ℝ] ℝ) → ℝ}
    {u : E → ℝ} {U : E → E →L[ℝ] ℝ} {φ : E → ℝ} {s : Set ℝ} {bound : E → ℝ}
    (hL : ∀ x, Differentiable ℝ (fun p : ℝ × (E →L[ℝ] ℝ) ↦ L x p.1 p.2))
    (hmeas : ∀ t : ℝ, AEStronglyMeasurable
      (fun x ↦ L x (u x + t * φ x) (U x + t • fderiv ℝ φ x)) μ)
    (hint : Integrable (fun x ↦ L x (u x) (U x)) μ) (hs : s ∈ 𝓝 0)
    (hbound : ∀ᵐ x ∂μ, ∀ t ∈ s, ‖firstVariationIntegrand L (fun y ↦ u y + t * φ y)
      (fun y ↦ U y + t • fderiv ℝ φ y) φ x‖ ≤ bound x)
    (hbound_int : Integrable bound μ) :
    Integrable (firstVariationIntegrand L u U φ) μ ∧
      HasDerivAt (fun t : ℝ ↦ variationalAction μ L
        (fun x ↦ u x + t * φ x) (fun x ↦ U x + t • fderiv ℝ φ x))
        (∫ x, firstVariationIntegrand L u U φ x ∂μ) 0 := by
  set F : ℝ → E → ℝ := fun t x ↦ L x (u x + t * φ x) (U x + t • fderiv ℝ φ x) with hF
  have h0 : firstVariationIntegrand L (fun y ↦ u y + 0 * φ y)
      (fun y ↦ U y + (0 : ℝ) • fderiv ℝ φ y) φ = firstVariationIntegrand L u U φ := by
    funext x; simp
  have hderiv (x : E) : HasDerivAt (F · x) (firstVariationIntegrand L u U φ x) 0 := by
    simpa [h0] using hasDerivAt_lagrangian_variation (u := u) (U := U) (φ := φ) (hL x) 0
  -- The first-variation integrand is the pointwise limit of difference quotients.
  have hF'_meas : AEStronglyMeasurable (firstVariationIntegrand L u U φ) μ := by
    have hseq : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun n ↦ Set.mem_compl_singleton_iff.2 (by positivity)⟩
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun (n : ℕ) x ↦ slope (F · x) 0 (1 / ((n : ℝ) + 1)))
      (fun n ↦ ?_) (ae_of_all _ fun x ↦ (hderiv x).tendsto_slope.comp hseq)
    simp only [slope, vsub_eq_sub, sub_zero, smul_eq_mul]
    exact ((hmeas _).sub (hmeas 0)).const_mul _
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (x₀ := 0) hs
    (Eventually.of_forall hmeas) (by simpa [hF] using hint) (by rwa [h0])
    (F' := fun t ↦ firstVariationIntegrand L (fun y ↦ u y + t * φ y)
      (fun y ↦ U y + t • fderiv ℝ φ y) φ) hbound hbound_int
    (ae_of_all _ fun x t _ ↦ hasDerivAt_lagrangian_variation (hL x) t)
  simp only [h0] at h
  exact ⟨h.1, by simpa [variationalAction_def, hF] using h.2⟩

/-- **36.1**, weak first-variation clause: at a local minimizer of the action along the variation
`(u + t φ, U + t Dφ)`, under the hypotheses of `hasDerivAt_variationalAction`, the
first-variation integrand is integrable and its integral vanishes. -/
theorem integral_firstVariation_eq_zero [MeasurableSpace E] {μ : Measure E}
    {L : E → ℝ → (E →L[ℝ] ℝ) → ℝ}
    {u : E → ℝ} {U : E → E →L[ℝ] ℝ} {φ : E → ℝ} {s : Set ℝ} {bound : E → ℝ}
    (hL : ∀ x, Differentiable ℝ (fun p : ℝ × (E →L[ℝ] ℝ) ↦ L x p.1 p.2))
    (hmeas : ∀ t : ℝ, AEStronglyMeasurable
      (fun x ↦ L x (u x + t * φ x) (U x + t • fderiv ℝ φ x)) μ)
    (hint : Integrable (fun x ↦ L x (u x) (U x)) μ) (hs : s ∈ 𝓝 0)
    (hbound : ∀ᵐ x ∂μ, ∀ t ∈ s, ‖firstVariationIntegrand L (fun y ↦ u y + t * φ y)
      (fun y ↦ U y + t • fderiv ℝ φ y) φ x‖ ≤ bound x)
    (hbound_int : Integrable bound μ)
    (hmin : IsLocalMin (fun t : ℝ ↦ variationalAction μ L
      (fun x ↦ u x + t * φ x) (fun x ↦ U x + t • fderiv ℝ φ x)) 0) :
    Integrable (firstVariationIntegrand L u U φ) μ ∧
      ∫ x, firstVariationIntegrand L u U φ x ∂μ = 0 := by
  obtain ⟨hi, hd⟩ := hasDerivAt_variationalAction hL hmeas hint hs hbound hbound_int
  exact ⟨hi, hmin.hasDerivAt_eq_zero hd⟩

end CKMA
