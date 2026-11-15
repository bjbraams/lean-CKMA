/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.PDE.Euclidean
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Kružkov entropy solutions and Hopf–Lax evolution

Bounded scalar conservation laws on positive times, their local initial traces,
maximum principle and spacetime-almost-everywhere uniqueness. The Euclidean
Hopf–Lax formula `hopfLaxHamiltonian` uses an extended-real Legendre transform until
convex superlinearity ensures finiteness. Hamilton–Jacobi solutions are defined by
first-order viscosity tests. The name is distinct from TauCeti's real Lagrangian formula.
Integration, convexity and local extrema use Mathlib.
Sources: GAPS 34.9 and 34.14.

## Main definitions

* `CKMA.kruzhkovFlux`, `CKMA.IsKruzhkovSolution`, `CKMA.HasLocalInitialTrace`:
  Kružkov entropy flux, bounded entropy solution predicate, and local `L¹` initial trace.
* `CKMA.hamiltonianLegendre`, `CKMA.hopfLaxHamiltonian`, `CKMA.IsHamiltonJacobiViscositySolution`:
  Euclidean Legendre transform, Hopf–Lax infimum, and Hamilton–Jacobi viscosity solutions.

## Main results

* `CKMA.exists_kruzhkovSolution`, `CKMA.kruzhkov_unique` (**34.9**): existence and uniqueness of
  Kružkov entropy solutions for bounded initial data.
* `CKMA.hopfLaxHamiltonian_viscosity` (**34.14**): the Hopf–Lax formula is finite and solves the
  Hamilton–Jacobi equation in the viscosity sense.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

/-- Kružkov's entropy flux at a constant state. -/
def kruzhkovFlux {d : ℕ} (f : ℝ → EuclideanRealSpace d) (k u : ℝ) : EuclideanRealSpace d :=
  (if k < u then (1 : ℝ) else if u < k then -1 else 0) • (f u - f k)

/-- Bounded entropy solution on positive times, tested against nonnegative compact spacetime
functions, including the initial trace term. -/
def IsKruzhkovSolution {d : ℕ} (f : ℝ → EuclideanRealSpace d)
    (u₀ : EuclideanRealSpace d → ℝ) (u : ℝ → EuclideanRealSpace d → ℝ) : Prop :=
  Measurable (Function.uncurry u) ∧
  (∃ M : ℝ, ∀ᵐ z ∂(volume : Measure (ℝ × EuclideanRealSpace d)).restrict
    (Set.Ioi 0 ×ˢ Set.univ), |u z.1 z.2| ≤ M) ∧
  ∀ k : ℝ, ∀ φ : ℝ × EuclideanRealSpace d → ℝ,
    IsCompactSmoothTestOn Set.univ φ → (∀ z, 0 ≤ φ z) →
    0 ≤ (∫ t in Set.Ioi (0 : ℝ), ∫ x,
      |u t x - k| * deriv (fun s ↦ φ (s, x)) t +
        ⟪kruzhkovFlux f k (u t x), gradient (fun y ↦ φ (t, y)) x⟫_ℝ) +
      ∫ x, |u₀ x - k| * φ (0, x)

/-- Locally integrable initial trace in the `L¹_loc` sense. -/
def HasLocalInitialTrace {d : ℕ} (u₀ : EuclideanRealSpace d → ℝ)
    (u : ℝ → EuclideanRealSpace d → ℝ) : Prop :=
  ∀ R : ℝ, 0 < R → Tendsto (fun t : ℝ ↦ ∫⁻ x in Metric.ball 0 R,
    ENNReal.ofReal |u t x - u₀ x|) (𝓝[>] 0) (𝓝 0)

/-- **34.9**: bounded initial data admit an entropy solution with its local initial trace
and maximum principle. Uniqueness is a.e. in spacetime, not equality of representatives. -/
theorem exists_kruzhkovSolution {d : ℕ} (hd : 0 < d)
    (f : ℝ → EuclideanRealSpace d) (hf : ContDiff ℝ 2 f)
    (u₀ : EuclideanRealSpace d → ℝ) (hu₀ : Measurable u₀) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐ x ∂volume, |u₀ x| ≤ M) :
    ∃ u, IsKruzhkovSolution f u₀ u ∧ HasLocalInitialTrace u₀ u ∧
      ∀ᵐ z ∂(volume : Measure (ℝ × EuclideanRealSpace d)).restrict
        (Set.Ioi 0 ×ˢ Set.univ), |u z.1 z.2| ≤ M := by
  sorry

/-- Uniqueness for the same bounded initial datum. -/
theorem kruzhkov_unique {d : ℕ} (f : ℝ → EuclideanRealSpace d) (hf : ContDiff ℝ 2 f)
    (u₀ : EuclideanRealSpace d → ℝ) {u v : ℝ → EuclideanRealSpace d → ℝ}
    (hu : IsKruzhkovSolution f u₀ u) (hv : IsKruzhkovSolution f u₀ v)
    (htu : HasLocalInitialTrace u₀ u) (htv : HasLocalInitialTrace u₀ v) :
    Function.uncurry u =ᵐ[(volume : Measure (ℝ × EuclideanRealSpace d)).restrict
      (Set.Ioi 0 ×ˢ Set.univ)] Function.uncurry v := by
  sorry

/-- The Euclidean Legendre transform of a finite Hamiltonian. -/
def hamiltonianLegendre {d : ℕ} (H : EuclideanRealSpace d → ℝ)
    (v : EuclideanRealSpace d) : EReal :=
  ⨆ p : EuclideanRealSpace d, ((⟪p, v⟫_ℝ - H p : ℝ) : EReal)

/-- The Euclidean Hamiltonian Hopf–Lax infimum, retaining extended values until coercivity
proves it finite. -/
def hopfLaxHamiltonian {d : ℕ} (H v₀ : EuclideanRealSpace d → ℝ)
    (t : ℝ) (x : EuclideanRealSpace d) : EReal :=
  ⨅ y : EuclideanRealSpace d,
    (v₀ y : EReal) + (t : EReal) * hamiltonianLegendre H (t⁻¹ • (x - y))

/-- First-order viscosity tests for the Euclidean Hamilton–Jacobi equation. -/
def IsHamiltonJacobiViscositySolution {d : ℕ} (H : EuclideanRealSpace d → ℝ)
    (v : ℝ × EuclideanRealSpace d → ℝ) : Prop :=
  ContinuousOn v (Set.Ioi (0 : ℝ) ×ˢ Set.univ) ∧
  (∀ z ∈ Set.Ioi (0 : ℝ) ×ˢ Set.univ, ∀ φ : ℝ × EuclideanRealSpace d → ℝ,
    ContDiffAt ℝ 1 φ z → IsLocalMaxOn (fun y ↦ v y - φ y)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) z →
        fderiv ℝ φ z (1, 0) + H (gradient (fun x ↦ φ (z.1, x)) z.2) ≤ 0) ∧
  (∀ z ∈ Set.Ioi (0 : ℝ) ×ˢ Set.univ, ∀ φ : ℝ × EuclideanRealSpace d → ℝ,
    ContDiffAt ℝ 1 φ z → IsLocalMinOn (fun y ↦ v y - φ y)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) z →
        0 ≤ fderiv ℝ φ z (1, 0) + H (gradient (fun x ↦ φ (z.1, x)) z.2))

/-- **34.14**: the Hopf–Lax infimum is finite and is a viscosity solution with initial data.
The a.e. derivative-to-entropy bridge remains a separate interface. -/
theorem hopfLaxHamiltonian_viscosity {d : ℕ} (H v₀ : EuclideanRealSpace d → ℝ)
    (hH : ConvexOn ℝ Set.univ H)
    (hsuper : Tendsto (fun p : EuclideanRealSpace d ↦ H p / ‖p‖) (Filter.comap norm atTop) atTop)
    {L : ℝ≥0} (hv₀ : LipschitzWith L v₀) :
    ∃ v : ℝ × EuclideanRealSpace d → ℝ,
      (∀ t : ℝ, 0 < t → ∀ x, hopfLaxHamiltonian H v₀ t x = v (t, x)) ∧
      IsHamiltonJacobiViscositySolution H v ∧ ∀ x,
        Tendsto (fun t : ℝ ↦ v (t, x)) (𝓝[>] 0) (𝓝 (v₀ x)) := by
  sorry

end CKMA
