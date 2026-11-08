/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Weak Euler–Lagrange first variation

Integral actions with a supplied derivative field and simultaneous variation of the
value and derivative variables. Stationarity of a local minimizer follows when the
derivative-under-the-integral identity is supplied explicitly, by Mathlib's
`IsLocalMin.hasDerivAt_eq_zero`. This interface separates the variational argument from
the analytic growth conditions needed for differentiation under the integral.
Source: GAPS 36.1.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

/-- The integral action with a supplied weak derivative field. -/
def variationalAction (μ : Measure E) (L : E → ℝ → (E →L[ℝ] ℝ) → ℝ)
    (u : E → ℝ) (U : E → E →L[ℝ] ℝ) : ℝ := ∫ x, L x (u x) (U x) ∂μ

/-- The first variation integrand, differentiating the value and derivative variables together. -/
def firstVariationIntegrand (L : E → ℝ → (E →L[ℝ] ℝ) → ℝ)
    (u : E → ℝ) (U : E → E →L[ℝ] ℝ) (φ : E → ℝ) (x : E) : ℝ :=
  fderiv ℝ (fun p : ℝ × (E →L[ℝ] ℝ) ↦ L x p.1 p.2) (u x, U x)
    (φ x, fderiv ℝ φ x)

/-- **36.1**, weak first-variation clause: a local minimizer is stationary when differentiation
under the integral is justified. The analytic derivative identity is an explicit hypothesis;
verifying it from growth assumptions and the classical PDE conclusion are separate targets. -/
theorem integral_firstVariation_eq_zero (μ : Measure E)
    (L : E → ℝ → (E →L[ℝ] ℝ) → ℝ) (u : E → ℝ) (U : E → E →L[ℝ] ℝ)
    (φ : E → ℝ)
    (hmin : IsLocalMin (fun t : ℝ ↦ variationalAction μ L
      (fun x ↦ u x + t * φ x) (fun x ↦ U x + t • fderiv ℝ φ x)) 0)
    (hdiff : HasDerivAt (fun t : ℝ ↦ variationalAction μ L
      (fun x ↦ u x + t * φ x) (fun x ↦ U x + t • fderiv ℝ φ x))
      (∫ x, firstVariationIntegrand L u U φ x ∂μ) 0) :
    ∫ x, firstVariationIntegrand L u U φ x ∂μ = 0 :=
  hmin.hasDerivAt_eq_zero hdiff

end CKMA
