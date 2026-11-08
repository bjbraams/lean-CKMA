/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Operator.Fredholm
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Analytic.Basic

/-!
# Analytic Fredholm families and simple eigenvalue branches

For a holomorphic compact-operator family invertible at one point of a connected domain,
exceptional parameters are discrete and the inverse is analytic elsewhere. Genuine inverse
poles have positive order, a nonzero analytic regularization at the base point, and invertibility
on a punctured neighborhood. At-most-pole regularizations are kept as a separate weaker notion.

An algebraically simple eigenpair is expressed by a rank-one projection and a two-sided reduced
resolvent identity. Its analytic continuation supplies an eigenvalue and a nonzero eigenvector
branch. Sources: GAPS 21.15 and 22.34; finite-rank principal parts are outside the displayed pole
  clause.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The noninvertibility set of a compact Fredholm family inside its parameter domain. -/
def fredholmExceptionalSet (K : ℂ → X →L[ℂ] X) (U : Set ℂ) : Set ℂ :=
  {z ∈ U | ¬ IsUnit (1 - K z)}

/-- A finite-order analytic regularization of the totalized inverse. Order zero is allowed,
so this weaker condition also includes removable singularities and regular points. -/
def HasFiniteOrderInverseRegularization (K : ℂ → X →L[ℂ] X) (a : ℂ) : Prop :=
  ∃ m : ℕ, ∃ F : ℂ → X →L[ℂ] X, AnalyticAt ℂ F a ∧
    ∀ᶠ z in 𝓝[≠] a, (z - a) ^ m • Ring.inverse (1 - K z) = F z

/-- A genuine inverse pole: the family is invertible on a punctured neighborhood and a
positive-order regularization is analytic with nonzero value at the base point. -/
def HasOperatorInversePole (K : ℂ → X →L[ℂ] X) (a : ℂ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ F : ℂ → X →L[ℂ] X, AnalyticAt ℂ F a ∧ F a ≠ 0 ∧
    (∀ᶠ z in 𝓝[≠] a, IsUnit (1 - K z)) ∧
    ∀ᶠ z in 𝓝[≠] a, (z - a) ^ m • Ring.inverse (1 - K z) = F z

omit [CompleteSpace X] in
/-- Every genuine inverse pole has a finite-order analytic regularization. -/
theorem HasOperatorInversePole.hasFiniteOrderInverseRegularization
    {K : ℂ → X →L[ℂ] X} {a : ℂ} (h : HasOperatorInversePole K a) :
    HasFiniteOrderInverseRegularization K a := by
  obtain ⟨m, _, F, hF, _, _, heq⟩ := h
  exact ⟨m, F, hF, heq⟩

/-- **21.15**: if the family is invertible at one point, exceptional points are discrete,
the inverse is analytic off them, and every exceptional point has a finite-order pole. -/
theorem analytic_fredholm {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (K : ℂ → X →L[ℂ] X) (hK : DifferentiableOn ℂ K U)
    (hc : ∀ z ∈ U, IsCompactOperator (K z))
    (hunit : ∃ z ∈ U, IsUnit (1 - K z)) :
    (∀ a ∈ fredholmExceptionalSet K U, ∃ r : ℝ, 0 < r ∧
      ∀ z ∈ fredholmExceptionalSet K U, dist z a < r → z = a) ∧
    DifferentiableOn ℂ (fun z ↦ Ring.inverse (1 - K z)) (U \ fredholmExceptionalSet K U) ∧
    ∀ a ∈ fredholmExceptionalSet K U, HasOperatorInversePole K a := by
  sorry

/-- Algebraic simplicity in a concrete reduced-resolvent form.
Geometric multiplicity one alone is insufficient: a Jordan block would permit branching. -/
def IsSimpleSpectralEigenpair (A : X →L[ℂ] X) (z : ℂ) (u : X) : Prop :=
  ∃ φ : X →L[ℂ] ℂ, φ u = 1 ∧ A u = z • u ∧ ∃ R : X →L[ℂ] X,
    (A - z • (1 : X →L[ℂ] X)) * R = 1 - φ.smulRight u ∧
    R * (A - z • (1 : X →L[ℂ] X)) = 1 - φ.smulRight u

/-- **22.34**, the bounded type-(A) simple-eigenvalue clause: an actual analytic eigenvector
and eigenvalue branch through the specified algebraically simple eigenpair. -/
theorem analytic_simple_eigenpair (A : ℂ → X →L[ℂ] X) (hA : AnalyticAt ℂ A 0)
    {z₀ : ℂ} {u₀ : X} (hpair : IsSimpleSpectralEigenpair (A 0) z₀ u₀) :
    ∃ r : ℝ, 0 < r ∧ ∃ z : ℂ → ℂ, ∃ u : ℂ → X,
      DifferentiableOn ℂ z (Metric.ball 0 r) ∧ DifferentiableOn ℂ u (Metric.ball 0 r) ∧
      z 0 = z₀ ∧ u 0 = u₀ ∧
      ∀ t ∈ Metric.ball 0 r, u t ≠ 0 ∧ A t (u t) = z t • u t := by
  sorry

end CKMA
