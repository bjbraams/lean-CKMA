/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
public import CKMA.Analysis.Complex.Laurent
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Full-polydisc Taylor expansion

Coordinate polyradii define open and closed polydiscs. Cauchy integrals over the
distinguished boundary give multiindex Taylor coefficients, their estimates and normal
convergence on the full open polydisc. Locally uniform limits on open subsets of ℂⁿ
remain holomorphic. Torus integration reuses TauCeti's polydisc Cauchy integral API.

Source: GAPS 45.2.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped BigOperators

/-- An open polydisc with unequal polyradii. -/
def polydisc {n : ℕ} (c : Fin n → ℂ) (R : Fin n → ℝ) : Set (Fin n → ℂ) :=
  {z | ∀ j, ‖z j - c j‖ < R j}

/-- A closed polydisc with unequal polyradii. -/
def closedPolydisc {n : ℕ} (c : Fin n → ℂ) (R : Fin n → ℝ) : Set (Fin n → ℂ) :=
  {z | ∀ j, ‖z j - c j‖ ≤ R j}

/-- Multivariable Cauchy coefficients on the distinguished boundary. -/
def polydiscTaylorCoefficient {n : ℕ} (f : (Fin n → ℂ) → ℂ)
    (c : Fin n → ℂ) (R : Fin n → ℝ) (α : Fin n → ℕ) : ℂ :=
  (2 * Real.pi * Complex.I) ^ (-(n : ℤ)) *
    ∯ z in T(c, R), (∏ j, (z j - c j) ^ (-(α j : ℤ) - 1)) * f z

/-- **45.2**: Taylor expansion on the full open polydisc, with normal convergence. -/
theorem polydisc_taylor {n : ℕ} (f : (Fin n → ℂ) → ℂ)
    (c : Fin n → ℂ) (R : Fin n → ℝ) (hR : ∀ j, 0 < R j)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hsub : closedPolydisc c R ⊆ U)
    (hf : DifferentiableOn ℂ f U) :
    (∀ z ∈ polydisc c R, HasSum (fun α : Fin n → ℕ ↦
      polydiscTaylorCoefficient f c R α * ∏ j, (z j - c j) ^ α j) (f z)) ∧
    NormallySummableOn (fun α : Fin n → ℕ ↦ fun z ↦
      polydiscTaylorCoefficient f c R α * ∏ j, (z j - c j) ^ α j) (polydisc c R) := by
  sorry

/-- Cauchy's multiindex coefficient estimate, equivalent to the derivative estimate after
multiplying by `α!`. -/
theorem norm_polydiscTaylorCoefficient_le {n : ℕ} (f : (Fin n → ℂ) → ℂ)
    (c : Fin n → ℂ) (R : Fin n → ℝ) (hR : ∀ j, 0 < R j)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hsub : closedPolydisc c R ⊆ U)
    (hf : DifferentiableOn ℂ f U) {M : ℝ}
    (hbound : ∀ z, (∀ j, ‖z j - c j‖ = R j) → ‖f z‖ ≤ M) (α : Fin n → ℕ) :
    ‖polydiscTaylorCoefficient f c R α‖ ≤ M * ∏ j, (R j)⁻¹ ^ α j := by
  sorry

/-- The several-variable Weierstrass theorem on open subsets of `ℂⁿ`. -/
theorem differentiableOn_of_locallyUniformLimit {n : ℕ}
    {F : ℕ → (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hF : ∀ k, DifferentiableOn ℂ (F k) U)
    (hlim : TendstoLocallyUniformlyOn F f atTop U) : DifferentiableOn ℂ f U := by
  sorry

end CKMA
