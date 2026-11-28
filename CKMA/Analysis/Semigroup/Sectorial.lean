/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.Semigroups.Generator.ComplexLinear

/-!
# Sectorial operators, fractional powers and spectral mapping

Closed densely defined sectorial operators and bounded holomorphic semigroup extensions,
with the sign convention that `-B` generates the semigroup. Balakrishnan integrals on
`D(B)` define fractional powers through graph closure. Eventual operator-norm continuity
gives spectral mapping after removing zero. Partial operators, generators and complex
resolvents reuse TauCeti; holomorphic maps and integration use Mathlib.
Sources: GAPS 24.20, 24.23 and 24.35.

## Main definitions

* `CKMA.operatorSector`, `CKMA.closedOperatorSector`: open punctured and closed sectors in `ℂ`.
* `CKMA.IsSectorialOperator`: sectoriality of a closed densely defined complex partial linear
  operator.
* `CKMA.HasBoundedAnalyticSemigroupExtension`: bounded holomorphic semigroup extension on a sector.
* `CKMA.balakrishnanIntegrand`, `CKMA.balakrishnanIntegral`: the Balakrishnan integrand and its
  normalized integral on the operator domain.
* `CKMA.IsEventuallyNormContinuousSemigroup`: operator-norm continuity after some time.

## Main results

* `CKMA.exists_isSectorialOperator_iff_exists_hasBoundedAnalyticSemigroupExtension`: equivalence
  between bounded holomorphic semigroup generation and sectoriality of the negative generator
  (**24.20**).
* `CKMA.IsSectorialOperator.integrableOn_balakrishnanIntegrand_and_closable`: integrability of the
  Balakrishnan integrand and closability of the Balakrishnan fractional power (**24.23**).
* `CKMA.IsEventuallyNormContinuousSemigroup.spectrum_diff_zero_eq_image_exp`: spectral mapping
  theorem away from zero for eventually norm-continuous semigroups (**24.35**).

## Implementation notes

The holomorphic extension in `CKMA.HasBoundedAnalyticSemigroupExtension` is an operator-valued map
`F : ℂ → X →L[ℂ] X`. The Balakrishnan integrand is written with the bounded resolvent
`(-t - B)⁻¹`, so that its definition needs no domain membership.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*.
* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology TauCeti.Semigroups
open scoped NNReal

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The open punctured sector around the positive real axis. -/
@[expose]
def operatorSector (θ : ℝ) : Set ℂ := {z | z ≠ 0 ∧ |Complex.arg z| < θ}

/-- Membership in the open punctured sector. -/
theorem mem_operatorSector {θ : ℝ} {z : ℂ} : z ∈ operatorSector θ ↔ z ≠ 0 ∧ |Complex.arg z| < θ :=
  Iff.rfl

/-- Closed sectors include their vertex; this matters for the spectrum of a noninvertible operator.
  -/
@[expose]
def closedOperatorSector (θ : ℝ) : Set ℂ := insert 0 {z | |Complex.arg z| ≤ θ}

/-- Membership in the closed sector. -/
theorem mem_closedOperatorSector {θ : ℝ} {z : ℂ} :
    z ∈ closedOperatorSector θ ↔ z = 0 ∨ |Complex.arg z| ≤ θ :=
  Iff.rfl

/-- Sectoriality for a closed densely defined complex partial linear operator.
The resolvent estimate is required outside each strictly larger closed sector. -/
@[expose]
def IsSectorialOperator (B : X →ₗ.[ℂ] X) (θ : ℝ) : Prop :=
  0 ≤ θ ∧ θ < Real.pi ∧ B.IsClosed ∧ Dense (B.domain : Set X) ∧
    B.spectrum ⊆ closedOperatorSector θ ∧
    ∀ φ : ℝ, θ < φ → φ < Real.pi → ∃ C : ℝ, ∀ z : ℂ,
      z ∉ closedOperatorSector φ → z ∈ B.resolventSet ∧ ‖z • B.resolvent z‖ ≤ C

omit [CompleteSpace X] in
/-- Unfolding sectoriality. -/
theorem isSectorialOperator_iff {B : X →ₗ.[ℂ] X} {θ : ℝ} :
    IsSectorialOperator B θ ↔ 0 ≤ θ ∧ θ < Real.pi ∧ B.IsClosed ∧ Dense (B.domain : Set X) ∧
      B.spectrum ⊆ closedOperatorSector θ ∧
      ∀ φ : ℝ, θ < φ → φ < Real.pi → ∃ C : ℝ, ∀ z : ℂ,
        z ∉ closedOperatorSector φ → z ∈ B.resolventSet ∧ ‖z • B.resolvent z‖ ≤ C :=
  Iff.rfl

/-- `S` has a bounded holomorphic extension to the sector of angle `θ ∈ (0, π/2]`: a holomorphic
`F : ℂ → X →L[ℂ] X`, bounded on the sector, equal to `S` on the positive axis, multiplicative
on the sector, and strongly continuous at `0` within every strictly smaller sector. -/
@[expose]
def HasBoundedAnalyticSemigroupExtension (S : StronglyContinuousSemigroup X)
    (hS : S.IsComplexLinear) (θ : ℝ) : Prop :=
  0 < θ ∧ θ ≤ Real.pi / 2 ∧ ∃ F : ℂ → X →L[ℂ] X,
    DifferentiableOn ℂ F (operatorSector θ) ∧
    (∃ M : ℝ, ∀ z ∈ operatorSector θ, ‖F z‖ ≤ M) ∧
    (∀ t : ℝ≥0, t ≠ 0 → F t = S.complexLinearOperator hS t) ∧
    (∀ z w, z ∈ operatorSector θ → w ∈ operatorSector θ →
      z + w ∈ operatorSector θ → F (z + w) = F z * F w) ∧
    ∀ φ : ℝ, 0 < φ → φ < θ → ∀ x : X,
      Tendsto (fun z ↦ F z x) (𝓝[operatorSector φ] 0) (𝓝 x)

omit [CompleteSpace X] in
/-- Unfolding the bounded holomorphic extension property. -/
theorem hasBoundedAnalyticSemigroupExtension_iff {S : StronglyContinuousSemigroup X}
    {hS : S.IsComplexLinear} {θ : ℝ} :
    HasBoundedAnalyticSemigroupExtension S hS θ ↔ 0 < θ ∧ θ ≤ Real.pi / 2 ∧
      ∃ F : ℂ → X →L[ℂ] X, DifferentiableOn ℂ F (operatorSector θ) ∧
        (∃ M : ℝ, ∀ z ∈ operatorSector θ, ‖F z‖ ≤ M) ∧
        (∀ t : ℝ≥0, t ≠ 0 → F t = S.complexLinearOperator hS t) ∧
        (∀ z w, z ∈ operatorSector θ → w ∈ operatorSector θ →
          z + w ∈ operatorSector θ → F (z + w) = F z * F w) ∧
        ∀ φ : ℝ, 0 < φ → φ < θ → ∀ x : X,
          Tendsto (fun z ↦ F z x) (𝓝[operatorSector φ] 0) (𝓝 x) :=
  Iff.rfl

/-- **24.20**: the negative of a sectorial operator of angle below `π / 2` generates a bounded
analytic semigroup, and every such generator has this sectorial characterization. -/
theorem exists_isSectorialOperator_iff_exists_hasBoundedAnalyticSemigroupExtension
    (B : X →ₗ.[ℂ] X) :
    (∃ θ : ℝ, θ < Real.pi / 2 ∧ IsSectorialOperator B θ) ↔
      ∃ (S : StronglyContinuousSemigroup X) (hS : S.IsComplexLinear),
        S.complexGenerator hS = -B ∧ ∃ θ : ℝ, HasBoundedAnalyticSemigroupExtension S hS θ := by
  sorry

/-- The Balakrishnan integrand `t ^ (α - 1) • (x + t R(-t, B) x)`, where
`R(-t, B) = (-t - B)⁻¹ = -(t + B)⁻¹`, so that it equals `t ^ (α - 1) • B (t + B)⁻¹ x`. -/
@[expose]
def balakrishnanIntegrand (B : X →ₗ.[ℂ] X) (α : ℝ) (x : X) (t : ℝ) : X :=
  t ^ (α - 1) • (x + (t : ℂ) • B.resolvent (-(t : ℂ)) x)

omit [CompleteSpace X] in
/-- Unfolding the Balakrishnan integrand. -/
theorem balakrishnanIntegrand_def (B : X →ₗ.[ℂ] X) (α : ℝ) (x : X) (t : ℝ) :
    balakrishnanIntegrand B α x t = t ^ (α - 1) • (x + (t : ℂ) • B.resolvent (-(t : ℂ)) x) :=
  rfl

/-- The Balakrishnan integral `(sin (π α) / π) ∫₀^∞ t ^ (α - 1) B (t + B)⁻¹ x dt`. -/
@[expose]
def balakrishnanIntegral (B : X →ₗ.[ℂ] X) (α : ℝ) (x : X) : X :=
  (Real.sin (Real.pi * α) / Real.pi) • ∫ t in Set.Ioi (0 : ℝ), balakrishnanIntegrand B α x t

omit [CompleteSpace X] in
/-- Unfolding the Balakrishnan integral. -/
theorem balakrishnanIntegral_def (B : X →ₗ.[ℂ] X) (α : ℝ) (x : X) :
    balakrishnanIntegral B α x = (Real.sin (Real.pi * α) / Real.pi) •
      ∫ t in Set.Ioi (0 : ℝ), balakrishnanIntegrand B α x t :=
  rfl

/-- **24.23**: for a sectorial `B` and `0 < α < 1`, the Balakrishnan integrand is integrable on
`(0, ∞)` for `x ∈ D(B)`, and the closure of the graph of `x ↦ balakrishnanIntegral B α x` on
`D(B)` is the graph of a closed partial operator, the fractional power `B ^ α`. -/
theorem IsSectorialOperator.integrableOn_balakrishnanIntegrand_and_closable
    {B : X →ₗ.[ℂ] X} {θ α : ℝ}
    (hB : IsSectorialOperator B θ) (hα : 0 < α) (hα1 : α < 1) :
    (∀ x : B.domain, IntegrableOn (balakrishnanIntegrand B α x) (Set.Ioi 0)) ∧
      ∃ C : X →ₗ.[ℂ] X, C.IsClosed ∧ (C.graph : Set (X × X)) =
        closure {p | ∃ x : B.domain, p = ((x : X), balakrishnanIntegral B α x)} := by
  sorry

/-- Eventual norm continuity: `t ↦ S t` is continuous in operator norm on `(t₀, ∞)` for some
`t₀ ≥ 0`. -/
@[expose]
def IsEventuallyNormContinuousSemigroup (S : StronglyContinuousSemigroup X) : Prop :=
  ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ContinuousOn S.realOperator (Set.Ioi t₀)

omit [CompleteSpace X] in
/-- Unfolding eventual norm continuity. -/
theorem isEventuallyNormContinuousSemigroup_iff {S : StronglyContinuousSemigroup X} :
    IsEventuallyNormContinuousSemigroup S ↔
      ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ContinuousOn S.realOperator (Set.Ioi t₀) :=
  Iff.rfl

/-- **24.35**: spectral mapping for eventually norm-continuous semigroups,
`σ(S t) \ {0} = exp (t σ(A))` for `t > 0`. Bounded analytic semigroups are a special case. -/
theorem IsEventuallyNormContinuousSemigroup.spectrum_diff_zero_eq_image_exp
    {S : StronglyContinuousSemigroup X} (hc : IsEventuallyNormContinuousSemigroup S)
    (hS : S.IsComplexLinear)
    {t : ℝ≥0} (ht : 0 < t) :
    spectrum ℂ (S.complexLinearOperator hS t) \ {0} =
      (fun z : ℂ ↦ Complex.exp ((t : ℂ) * z)) '' (S.complexGenerator hS).spectrum := by
  sorry

end CKMA
