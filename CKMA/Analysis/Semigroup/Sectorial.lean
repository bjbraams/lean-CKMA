/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.Semigroups.Resolvent.Complex
public import TauCeti.Analysis.Semigroups.Generator.Neg
public import TauCeti.Analysis.Normed.Operator.Resolvent.Spectrum
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Sectorial operators, fractional powers and spectral mapping

Closed densely defined sectorial operators and bounded holomorphic semigroup extensions,
with the sign convention that `-B` generates the semigroup. Balakrishnan integrals on
`D(B)` define fractional powers through graph closure. Eventual operator-norm continuity
gives spectral mapping after removing zero. Partial operators, generators and complex
resolvents reuse TauCeti; holomorphic maps and integration use Mathlib.
Sources: GAPS 24.20, 24.23 and 24.35.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology TauCeti.Semigroups
open scoped NNReal

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The open punctured sector around the positive real axis. -/
def operatorSector (θ : ℝ) : Set ℂ := {z | z ≠ 0 ∧ |Complex.arg z| < θ}

/-- Closed sectors include their vertex; this matters for the spectrum of a noninvertible operator.
  -/
def closedOperatorSector (θ : ℝ) : Set ℂ := insert 0 {z | |Complex.arg z| ≤ θ}

/-- Sectoriality for a closed densely defined complex partial linear operator.
The resolvent estimate is required outside each strictly larger closed sector. -/
def IsSectorialOperator (B : X →ₗ.[ℂ] X) (θ : ℝ) : Prop :=
  0 ≤ θ ∧ θ < Real.pi ∧ B.IsClosed ∧ Dense (B.domain : Set X) ∧
    B.spectrum ⊆ closedOperatorSector θ ∧
    ∀ φ : ℝ, θ < φ → φ < Real.pi → ∃ C : ℝ, ∀ z : ℂ,
      z ∉ closedOperatorSector φ → z ∈ B.resolventSet ∧ ‖z • B.resolvent z‖ ≤ C

/-- A bounded holomorphic semigroup extension, expressed using an actual operator-valued map.
Its limit at zero is strong and is tested on every strictly smaller sector. -/
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

/-- **24.20**: the negative of a sectorial operator of angle below pi/2 generates a bounded
analytic semigroup, and every such generator has this sectorial characterization. -/
theorem sectorial_iff_analytic_generation (B : X →ₗ.[ℂ] X) :
    (∃ θ : ℝ, θ < Real.pi / 2 ∧ IsSectorialOperator B θ) ↔
      ∃ (S : StronglyContinuousSemigroup X) (hS : S.IsComplexLinear),
        S.complexGenerator hS = -B ∧ ∃ θ : ℝ, HasBoundedAnalyticSemigroupExtension S hS θ := by
  sorry

/-- The Balakrishnan integrand, written with a bounded resolvent so no unproved domain
membership is needed in its definition. Here `R(-t,B)=-(t+B)^(-1)`. -/
def balakrishnanIntegrand (B : X →ₗ.[ℂ] X) (α : ℝ) (x : X) (t : ℝ) : X :=
  t ^ (α - 1) • (x + (t : ℂ) • B.resolvent (-(t : ℂ)) x)

/-- The Balakrishnan expression on the initial generator domain, with its sine normalization. -/
def balakrishnanIntegral (B : X →ₗ.[ℂ] X) (α : ℝ) (x : X) : X :=
  (Real.sin (Real.pi * α) / Real.pi) • ∫ t in Set.Ioi (0 : ℝ), balakrishnanIntegrand B α x t

/-- **24.23**: the integral on `D(B)` is integrable, and closing its graph gives a closed
fractional-power partial operator. This statement does not assume boundedness of `B`. -/
theorem balakrishnan_fractionalPower {B : X →ₗ.[ℂ] X} {θ α : ℝ}
    (hB : IsSectorialOperator B θ) (hα : 0 < α) (hα1 : α < 1) :
    (∀ x : B.domain, IntegrableOn (balakrishnanIntegrand B α x) (Set.Ioi 0)) ∧
      ∃ C : X →ₗ.[ℂ] X, C.IsClosed ∧ (C.graph : Set (X × X)) =
        closure {p | ∃ x : B.domain, p = ((x : X), balakrishnanIntegral B α x)} := by
  sorry

/-- Eventual continuity in operator norm, rather than only strong continuity of orbits. -/
def IsEventuallyNormContinuousSemigroup (S : StronglyContinuousSemigroup X) : Prop :=
  ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ContinuousOn S.realOperator (Set.Ioi t₀)

/-- **24.35**: spectral mapping for eventually norm-continuous semigroups, with the exceptional
zero spectral value removed. Bounded analytic semigroups are an important subcase. -/
theorem spectralMapping_eventuallyNormContinuous (S : StronglyContinuousSemigroup X)
    (hS : S.IsComplexLinear) (hc : IsEventuallyNormContinuousSemigroup S)
    {t : ℝ≥0} (ht : 0 < t) :
    spectrum ℂ (S.complexLinearOperator hS t) \ {0} =
      (fun z : ℂ ↦ Complex.exp ((t : ℂ) * z)) '' (S.complexGenerator hS).spectrum := by
  sorry

end CKMA
