/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.SpecialFunctions.Bessel
public import CKMA.Analysis.Complex.Laurent

/-!
# Gamma multiplication, Gauss's equation and Bessel generating series

Gauss multiplication relates a finite product of shifted Gamma values to a single
Gamma value at the multiplied argument. The hypergeometric series solves Gauss's
equation and is the unique normalized analytic solution germ; the three singular
points are regular singular, as witnessed by analytic rational germs in local and
reciprocal coordinates. The bilateral integer-order Bessel generating series
converges normally away from its auxiliary variable's origin.

Sources: GAPS 49.6, 49.13 and 49.30. Special functions and branches reuse Mathlib.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped BigOperators

/-- **49.6**: Gauss's multiplication formula at all nonpolar complex parameters.
The positive real bases fix the principal-power branches. -/
theorem gamma_multiplication (m : ℕ) (hm : 0 < m) (z : ℂ)
    (hz : ∀ n : ℕ, (m : ℂ) * z ≠ -(n : ℂ)) :
    (∏ j : Fin m, Complex.Gamma (z + (j.val : ℂ) / m)) =
      (2 * Real.pi : ℂ) ^ (((m : ℂ) - 1) / 2) *
      (m : ℂ) ^ ((1 / 2 : ℂ) - (m : ℂ) * z) * Complex.Gamma ((m : ℂ) * z) := by
  sorry

/-- Gauss's hypergeometric differential expression. -/
def gaussDifferentialExpression (a b c : ℂ) (y : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * (1 - z) * deriv (deriv y) z + (c - (a + b + 1) * z) * deriv y z - a * b * y z

/-- **49.13**: the hypergeometric series solves Gauss's equation in the unit disk.
The denominator parameter must avoid the nonpositive integers. -/
theorem gauss_hypergeometric_ode (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ))
    {z : ℂ} (hz : ‖z‖ < 1) :
    gaussDifferentialExpression a b c (ordinaryHypergeometric a b c) z = 0 := by
  sorry

/-- Normalization at zero determines the analytic solution germ, for a regular denominator
  parameter. -/
theorem gauss_hypergeometric_unique (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ))
    {y : ℂ → ℂ} (hy : AnalyticAt ℂ y 0) (hy0 : y 0 = 1)
    (hode : ∀ᶠ z in 𝓝 (0 : ℂ), gaussDifferentialExpression a b c y z = 0) :
    y =ᶠ[𝓝 (0 : ℂ)] ordinaryHypergeometric a b c := by
  sorry

/-- The regular-singular criterion for `y'' + P y' + Q y = 0`, allowing removable singularities.
Punctured equalities avoid false continuity claims for totalized rational functions at their poles.
  -/
def IsRegularSingularAt (P Q : ℂ → ℂ) (a : ℂ) : Prop :=
  ∃ p q : ℂ → ℂ, AnalyticAt ℂ p a ∧ AnalyticAt ℂ q a ∧
    (∀ᶠ z in 𝓝[≠] a, p z = (z - a) * P z) ∧
    (∀ᶠ z in 𝓝[≠] a, q z = (z - a) ^ 2 * Q z)

/-- The regular-singular criterion at infinity, after the coordinate change `z = 1/w`. -/
def IsRegularSingularAtInfinity (P Q : ℂ → ℂ) : Prop :=
  IsRegularSingularAt (fun w ↦ 2 / w - P w⁻¹ / w ^ 2) (fun w ↦ Q w⁻¹ / w ^ 4) 0

/-- All three Gauss points are regular singular (possibly ordinary in degenerate cases). -/
theorem gauss_regularSingular (a b c : ℂ) :
    let P := fun z ↦ (c - (a + b + 1) * z) / (z * (1 - z))
    let Q := fun z ↦ -(a * b) / (z * (1 - z))
    IsRegularSingularAt P Q 0 ∧ IsRegularSingularAt P Q 1 ∧ IsRegularSingularAtInfinity P Q := by
  intro P Q
  have h0 : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 ∧ z ≠ 1 := by
    have hn : ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), z ≠ 1 :=
      (isOpen_ne_fun continuous_id continuous_const).mem_nhds (by norm_num)
    have hself : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 := self_mem_nhdsWithin
    exact hself.and (hn.filter_mono nhdsWithin_le_nhds)
  have h1 : ∀ᶠ z : ℂ in 𝓝[≠] (1 : ℂ), z ≠ 0 ∧ z ≠ 1 := by
    have hn : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), z ≠ 0 :=
      (isOpen_ne_fun continuous_id continuous_const).mem_nhds (by norm_num)
    exact (hn.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  have hminus : ∀ z : ℂ, z ≠ 1 → 1 - z ≠ 0 := by
    intro z hz
    exact sub_ne_zero.mpr (Ne.symm hz)
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun z ↦ (c - (a + b + 1) * z) / (1 - z),
      fun z ↦ -(a * b) * z / (1 - z), by fun_prop (disch := norm_num),
      by fun_prop (disch := norm_num), ?_, ?_⟩
    · filter_upwards [h0] with z hz
      dsimp only [P]
      field_simp [hz.1, hminus z hz.2]
      ring
    · filter_upwards [h0] with z hz
      dsimp only [Q]
      field_simp [hz.1, hminus z hz.2]
      ring
  · refine ⟨fun z ↦ ((a + b + 1) * z - c) / z,
      fun z ↦ (a * b) * (z - 1) / z, by fun_prop (disch := norm_num),
      by fun_prop (disch := norm_num), ?_, ?_⟩
    · filter_upwards [h1] with z hz
      dsimp only [P]
      field_simp [hz.1, hminus z hz.2]
      ring
    · filter_upwards [h1] with z hz
      dsimp only [Q]
      field_simp [hz.1, hminus z hz.2]
      ring
  · refine ⟨fun w ↦ 2 - (c * w - (a + b + 1)) / (w - 1),
      fun w ↦ -(a * b) / (w - 1), by fun_prop (disch := norm_num),
      by fun_prop (disch := norm_num), ?_, ?_⟩
    · filter_upwards [h0] with w hw
      dsimp only [P]
      field_simp [hw.1, hminus w hw.2, sub_ne_zero.mpr hw.2]
      ring
    · filter_upwards [h0] with w hw
      dsimp only [Q]
      field_simp [hw.1, hminus w hw.2, sub_ne_zero.mpr hw.2]
      ring

/-- **49.30**: the bilateral Bessel generating series. -/
theorem hasSum_bessel_generating (z : ℂ) {t : ℂ} (ht : t ≠ 0) :
    HasSum (fun n : ℤ ↦ Complex.besselJ (n : ℂ) z * t ^ n)
      (Complex.exp ((z / 2) * (t - t⁻¹))) := by
  sorry

/-- Normal convergence on compact sets in `(z,t)` away from `t=0`, including uniformity in `z`. -/
theorem normallySummableOn_bessel_generating :
    NormallySummableOn (fun n : ℤ ↦ fun p : ℂ × ℂ ↦ Complex.besselJ (n : ℂ) p.1 * p.2 ^ n)
      {p | p.2 ≠ 0} := by
  sorry

end CKMA
