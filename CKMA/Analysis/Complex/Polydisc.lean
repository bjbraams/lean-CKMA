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
remain holomorphic. Torus integration reuses TauCeti's polydisc Cauchy integral API;
the coefficient bound uses Mathlib's norm estimate for torus integrals.

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

/-- A bound on the distinguished boundary controls the contour-defined coefficient;
this norm estimate requires no holomorphy of the integrand. -/
theorem norm_polydiscTaylorCoefficient_le_of_bound {n : ℕ}
    (f : (Fin n → ℂ) → ℂ) (c : Fin n → ℂ) (R : Fin n → ℝ)
    (hR : ∀ j, 0 < R j) {M : ℝ}
    (hbound : ∀ z, (∀ j, ‖z j - c j‖ = R j) → ‖f z‖ ≤ M) (α : Fin n → ℕ) :
    ‖polydiscTaylorCoefficient f c R α‖ ≤ M * ∏ j, (R j)⁻¹ ^ α j := by
  have hnorm : ∀ θ : Fin n → ℝ, ∀ j,
      ‖torusMap c R θ j - c j‖ = R j := by
    intro θ j
    have hh := TauCeti.torusMap_mem_pi_sphere (c := c) (fun j ↦ (hR j).le) θ j (Set.mem_univ j)
    simpa only [Metric.mem_sphere, dist_eq_norm] using hh
  have hprod : ∀ θ : Fin n → ℝ,
      ‖∏ j, (torusMap c R θ j - c j) ^ (-(α j : ℤ) - 1)‖ =
        ∏ j, (R j)⁻¹ ^ (α j + 1) := by
    intro θ
    rw [norm_prod]
    apply Finset.prod_congr rfl
    intro j _
    have he : -(α j : ℤ) - 1 = -((α j + 1 : ℕ) : ℤ) := by omega
    rw [he, norm_zpow, zpow_neg, zpow_natCast, inv_pow, hnorm]
  have hi := norm_torusIntegral_le_of_norm_le_const (c := c) (R := R)
    (f := fun z ↦ (∏ j, (z j - c j) ^ (-(α j : ℤ) - 1)) * f z)
    (C := (∏ j, (R j)⁻¹ ^ (α j + 1)) * M) (fun θ ↦ by
      rw [norm_mul, hprod]
      exact mul_le_mul_of_nonneg_left (hbound _ (hnorm θ))
        (Finset.prod_nonneg fun j _ ↦ pow_nonneg (inv_nonneg.mpr (hR j).le) _))
  have hK : ‖(2 * Real.pi * Complex.I : ℂ) ^ (-(n : ℤ))‖ =
      ((2 * Real.pi) ^ n)⁻¹ := by
    rw [norm_zpow, zpow_neg, zpow_natCast]
    simp [abs_of_pos Real.pi_pos]
  have habs : (∏ j, |R j|) = ∏ j, R j := by
    exact Finset.prod_congr rfl fun j _ ↦ abs_of_pos (hR j)
  have hcancel : (∏ j, R j) * (∏ j, (R j)⁻¹ ^ (α j + 1)) =
      ∏ j, (R j)⁻¹ ^ α j := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [pow_succ]
    calc R j * ((R j)⁻¹ ^ α j * (R j)⁻¹) =
        (R j * (R j)⁻¹) * (R j)⁻¹ ^ α j := by ring
      _ = _ := by rw [mul_inv_cancel₀ (hR j).ne', one_mul]
  have hA : (2 * Real.pi) ^ n ≠ 0 := pow_ne_zero _ (by positivity)
  calc
    ‖polydiscTaylorCoefficient f c R α‖ =
      ((2 * Real.pi) ^ n)⁻¹ *
        ‖∯ z in T(c, R), (∏ j, (z j - c j) ^ (-(α j : ℤ) - 1)) * f z‖ := by
      rw [polydiscTaylorCoefficient, norm_mul, hK]
    _ ≤ ((2 * Real.pi) ^ n)⁻¹ *
        (((2 * Real.pi) ^ n * ∏ j, |R j|) *
          ((∏ j, (R j)⁻¹ ^ (α j + 1)) * M)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = M * ∏ j, (R j)⁻¹ ^ α j := by
      rw [habs]
      calc ((2 * Real.pi) ^ n)⁻¹ *
          (((2 * Real.pi) ^ n * ∏ j, R j) *
            ((∏ j, (R j)⁻¹ ^ (α j + 1)) * M)) =
          (((2 * Real.pi) ^ n)⁻¹ * (2 * Real.pi) ^ n) *
            ((∏ j, R j) * (∏ j, (R j)⁻¹ ^ (α j + 1))) * M := by ring
        _ = _ := by rw [inv_mul_cancel₀ hA, one_mul, hcancel]; ring

/-- Cauchy's multiindex bound on the contour coefficient.
The estimate uses only the distinguished-boundary bound. -/
theorem norm_polydiscTaylorCoefficient_le {n : ℕ} (f : (Fin n → ℂ) → ℂ)
    (c : Fin n → ℂ) (R : Fin n → ℝ) (hR : ∀ j, 0 < R j) {M : ℝ}
    (hbound : ∀ z, (∀ j, ‖z j - c j‖ = R j) → ‖f z‖ ≤ M) (α : Fin n → ℕ) :
    ‖polydiscTaylorCoefficient f c R α‖ ≤ M * ∏ j, (R j)⁻¹ ^ α j := by
  exact norm_polydiscTaylorCoefficient_le_of_bound f c R hR hbound α

/-- The several-variable Weierstrass theorem on open subsets of `ℂⁿ`. -/
theorem differentiableOn_of_locallyUniformLimit {n : ℕ}
    {F : ℕ → (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hF : ∀ k, DifferentiableOn ℂ (F k) U)
    (hlim : TendstoLocallyUniformlyOn F f atTop U) : DifferentiableOn ℂ f U := by
  sorry

end CKMA
