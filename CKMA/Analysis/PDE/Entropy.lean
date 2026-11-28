/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.PDE.Euclidean
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

import Mathlib.MeasureTheory.Measure.OpenPos

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
  Kružkov entropy solutions for bounded initial data and a `C¹` flux.
* `CKMA.hopfLaxHamiltonian_viscosity` (**34.14**): the Hopf–Lax formula is finite and solves the
  Hamilton–Jacobi equation in the viscosity sense.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

/-- Kružkov's entropy flux at a constant state. -/
@[expose]
def kruzhkovFlux {d : ℕ} (f : ℝ → EuclideanSpace ℝ (Fin d)) (k u : ℝ) :
    EuclideanSpace ℝ (Fin d) :=
  (if k < u then (1 : ℝ) else if u < k then -1 else 0) • (f u - f k)

/-- Unfolding Kružkov's entropy flux. -/
theorem kruzhkovFlux_def {d : ℕ} (f : ℝ → EuclideanSpace ℝ (Fin d)) (k u : ℝ) :
    kruzhkovFlux f k u = (if k < u then (1 : ℝ) else if u < k then -1 else 0) • (f u - f k) :=
  rfl

/-- The entropy flux is `f u - f k` above the constant state. -/
theorem kruzhkovFlux_of_lt {d : ℕ} (f : ℝ → EuclideanSpace ℝ (Fin d)) {k u : ℝ} (h : k < u) :
    kruzhkovFlux f k u = f u - f k := by
  simp [kruzhkovFlux, h]

/-- The entropy flux is `f k - f u` below the constant state. -/
theorem kruzhkovFlux_of_gt {d : ℕ} (f : ℝ → EuclideanSpace ℝ (Fin d)) {k u : ℝ} (h : u < k) :
    kruzhkovFlux f k u = f k - f u := by
  simp [kruzhkovFlux, h, h.not_gt, neg_sub]

/-- The entropy flux vanishes at the constant state. -/
@[simp]
theorem kruzhkovFlux_self {d : ℕ} (f : ℝ → EuclideanSpace ℝ (Fin d)) (k : ℝ) :
    kruzhkovFlux f k k = 0 := by
  simp [kruzhkovFlux]

/-- Bounded entropy solution on positive times, tested against nonnegative compact spacetime
functions, including the initial trace term. Each identity is a Bochner integral, so a
non-integrable integrand has integral `0`. -/
@[expose]
def IsKruzhkovSolution {d : ℕ} (f : ℝ → EuclideanSpace ℝ (Fin d))
    (u₀ : EuclideanSpace ℝ (Fin d) → ℝ) (u : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  Measurable (Function.uncurry u) ∧
  (∃ M : ℝ, ∀ᵐ z ∂(volume : Measure (ℝ × EuclideanSpace ℝ (Fin d))).restrict
    (Set.Ioi 0 ×ˢ Set.univ), |u z.1 z.2| ≤ M) ∧
  ∀ k : ℝ, ∀ φ : ℝ × EuclideanSpace ℝ (Fin d) → ℝ,
    IsCompactSmoothTestOn Set.univ φ → (∀ z, 0 ≤ φ z) →
    0 ≤ (∫ t in Set.Ioi (0 : ℝ), ∫ x,
      |u t x - k| * deriv (fun s ↦ φ (s, x)) t +
        ⟪kruzhkovFlux f k (u t x), gradient (fun y ↦ φ (t, y)) x⟫_ℝ) +
      ∫ x, |u₀ x - k| * φ (0, x)

/-- Unfolding the Kružkov entropy-solution predicate. -/
theorem isKruzhkovSolution_iff {d : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin d)}
    {u₀ : EuclideanSpace ℝ (Fin d) → ℝ} {u : ℝ → EuclideanSpace ℝ (Fin d) → ℝ} :
    IsKruzhkovSolution f u₀ u ↔
      Measurable (Function.uncurry u) ∧
      (∃ M : ℝ, ∀ᵐ z ∂(volume : Measure (ℝ × EuclideanSpace ℝ (Fin d))).restrict
        (Set.Ioi 0 ×ˢ Set.univ), |u z.1 z.2| ≤ M) ∧
      ∀ k : ℝ, ∀ φ : ℝ × EuclideanSpace ℝ (Fin d) → ℝ,
        IsCompactSmoothTestOn Set.univ φ → (∀ z, 0 ≤ φ z) →
        0 ≤ (∫ t in Set.Ioi (0 : ℝ), ∫ x,
          |u t x - k| * deriv (fun s ↦ φ (s, x)) t +
            ⟪kruzhkovFlux f k (u t x), gradient (fun y ↦ φ (t, y)) x⟫_ℝ) +
          ∫ x, |u₀ x - k| * φ (0, x) :=
  Iff.rfl

/-- An entropy solution is jointly measurable. -/
theorem IsKruzhkovSolution.measurable {d : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin d)}
    {u₀ : EuclideanSpace ℝ (Fin d) → ℝ} {u : ℝ → EuclideanSpace ℝ (Fin d) → ℝ}
    (h : IsKruzhkovSolution f u₀ u) : Measurable (Function.uncurry u) :=
  h.1

/-- Locally integrable initial trace in the `L¹_loc` sense. -/
@[expose]
def HasLocalInitialTrace {d : ℕ} (u₀ : EuclideanSpace ℝ (Fin d) → ℝ)
    (u : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ R : ℝ, 0 < R → Tendsto (fun t : ℝ ↦ ∫⁻ x in Metric.ball 0 R,
    ENNReal.ofReal |u t x - u₀ x|) (𝓝[>] 0) (𝓝 0)

/-- Unfolding the local initial trace. -/
theorem hasLocalInitialTrace_iff {d : ℕ} {u₀ : EuclideanSpace ℝ (Fin d) → ℝ}
    {u : ℝ → EuclideanSpace ℝ (Fin d) → ℝ} :
    HasLocalInitialTrace u₀ u ↔ ∀ R : ℝ, 0 < R → Tendsto (fun t : ℝ ↦
      ∫⁻ x in Metric.ball 0 R, ENNReal.ofReal |u t x - u₀ x|) (𝓝[>] 0) (𝓝 0) :=
  Iff.rfl

/-- **34.9**: for a `C¹` flux, bounded initial data admit an entropy solution with its local
initial trace and the maximum principle `|u| ≤ M`. Uniqueness (`kruzhkov_unique`) is a.e. in
spacetime, not equality of representatives. -/
theorem exists_kruzhkovSolution {d : ℕ}
    (f : ℝ → EuclideanSpace ℝ (Fin d)) (hf : ContDiff ℝ 1 f)
    (u₀ : EuclideanSpace ℝ (Fin d) → ℝ) (hu₀ : Measurable u₀) {M : ℝ}
    (hbound : ∀ᵐ x ∂volume, |u₀ x| ≤ M) :
    ∃ u, IsKruzhkovSolution f u₀ u ∧ HasLocalInitialTrace u₀ u ∧
      ∀ᵐ z ∂(volume : Measure (ℝ × EuclideanSpace ℝ (Fin d))).restrict
        (Set.Ioi 0 ×ˢ Set.univ), |u z.1 z.2| ≤ M := by
  have : NeZero (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    refine ⟨fun hμ => ?_⟩
    have hpos := Metric.measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin d)))
      (0 : EuclideanSpace ℝ (Fin d)) one_pos
    rw [hμ] at hpos
    simp at hpos
  by_cases hM : 0 ≤ M
  · sorry
  · obtain ⟨x, hx⟩ := hbound.exists
    exact absurd ((abs_nonneg (u₀ x)).trans hx) hM

/-- **34.9**, uniqueness: for a `C¹` flux, two entropy solutions with the same initial trace
agree a.e. on positive times. -/
theorem kruzhkov_unique {d : ℕ} (f : ℝ → EuclideanSpace ℝ (Fin d)) (hf : ContDiff ℝ 1 f)
    (u₀ : EuclideanSpace ℝ (Fin d) → ℝ) {u v : ℝ → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IsKruzhkovSolution f u₀ u) (hv : IsKruzhkovSolution f u₀ v)
    (htu : HasLocalInitialTrace u₀ u) (htv : HasLocalInitialTrace u₀ v) :
    Function.uncurry u =ᵐ[(volume : Measure (ℝ × EuclideanSpace ℝ (Fin d))).restrict
      (Set.Ioi 0 ×ˢ Set.univ)] Function.uncurry v := by
  sorry

/-- The Euclidean Legendre transform of a finite Hamiltonian. -/
@[expose]
def hamiltonianLegendre {d : ℕ} (H : EuclideanSpace ℝ (Fin d) → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) : EReal :=
  ⨆ p : EuclideanSpace ℝ (Fin d), ((⟪p, v⟫_ℝ - H p : ℝ) : EReal)

/-- The Euclidean Hamiltonian Hopf–Lax infimum, retaining extended values until coercivity
proves it finite. -/
@[expose]
def hopfLaxHamiltonian {d : ℕ} (H v₀ : EuclideanSpace ℝ (Fin d) → ℝ)
    (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) : EReal :=
  ⨅ y : EuclideanSpace ℝ (Fin d),
    (v₀ y : EReal) + (t : EReal) * hamiltonianLegendre H (t⁻¹ • (x - y))

/-- Unfolding the Legendre transform. -/
theorem hamiltonianLegendre_def {d : ℕ} (H : EuclideanSpace ℝ (Fin d) → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) :
    hamiltonianLegendre H v = ⨆ p : EuclideanSpace ℝ (Fin d), ((⟪p, v⟫_ℝ - H p : ℝ) : EReal) :=
  rfl

/-- The Fenchel–Young inequality `⟪p, v⟫ - H p ≤ H^*(v)`. -/
theorem le_hamiltonianLegendre {d : ℕ} (H : EuclideanSpace ℝ (Fin d) → ℝ)
    (p v : EuclideanSpace ℝ (Fin d)) :
    ((⟪p, v⟫_ℝ - H p : ℝ) : EReal) ≤ hamiltonianLegendre H v :=
  le_iSup (fun p : EuclideanSpace ℝ (Fin d) ↦ ((⟪p, v⟫_ℝ - H p : ℝ) : EReal)) p

/-- Unfolding the Hopf–Lax infimum. -/
theorem hopfLaxHamiltonian_def {d : ℕ} (H v₀ : EuclideanSpace ℝ (Fin d) → ℝ)
    (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    hopfLaxHamiltonian H v₀ t x = ⨅ y : EuclideanSpace ℝ (Fin d),
      (v₀ y : EReal) + (t : EReal) * hamiltonianLegendre H (t⁻¹ • (x - y)) := rfl

/-- The Hopf–Lax infimum is bounded by each competitor. -/
theorem hopfLaxHamiltonian_le {d : ℕ} (H v₀ : EuclideanSpace ℝ (Fin d) → ℝ)
    (t : ℝ) (x y : EuclideanSpace ℝ (Fin d)) :
    hopfLaxHamiltonian H v₀ t x ≤
      (v₀ y : EReal) + (t : EReal) * hamiltonianLegendre H (t⁻¹ • (x - y)) :=
  iInf_le (fun y : EuclideanSpace ℝ (Fin d) ↦
    (v₀ y : EReal) + (t : EReal) * hamiltonianLegendre H (t⁻¹ • (x - y))) y

/-- First-order viscosity tests for the Euclidean Hamilton–Jacobi equation. -/
@[expose]
def IsHamiltonJacobiViscositySolution {d : ℕ} (H : EuclideanSpace ℝ (Fin d) → ℝ)
    (v : ℝ × EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ContinuousOn v (Set.Ioi (0 : ℝ) ×ˢ Set.univ) ∧
  (∀ z ∈ Set.Ioi (0 : ℝ) ×ˢ Set.univ, ∀ φ : ℝ × EuclideanSpace ℝ (Fin d) → ℝ,
    ContDiffAt ℝ 1 φ z → IsLocalMaxOn (fun y ↦ v y - φ y)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) z →
        fderiv ℝ φ z (1, 0) + H (gradient (fun x ↦ φ (z.1, x)) z.2) ≤ 0) ∧
  (∀ z ∈ Set.Ioi (0 : ℝ) ×ˢ Set.univ, ∀ φ : ℝ × EuclideanSpace ℝ (Fin d) → ℝ,
    ContDiffAt ℝ 1 φ z → IsLocalMinOn (fun y ↦ v y - φ y)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) z →
        0 ≤ fderiv ℝ φ z (1, 0) + H (gradient (fun x ↦ φ (z.1, x)) z.2))

/-- Unfolding the Hamilton–Jacobi viscosity-solution predicate. -/
theorem isHamiltonJacobiViscositySolution_iff {d : ℕ} {H : EuclideanSpace ℝ (Fin d) → ℝ}
    {v : ℝ × EuclideanSpace ℝ (Fin d) → ℝ} :
    IsHamiltonJacobiViscositySolution H v ↔
      ContinuousOn v (Set.Ioi (0 : ℝ) ×ˢ Set.univ) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ) ×ˢ Set.univ, ∀ φ : ℝ × EuclideanSpace ℝ (Fin d) → ℝ,
        ContDiffAt ℝ 1 φ z → IsLocalMaxOn (fun y ↦ v y - φ y)
          (Set.Ioi (0 : ℝ) ×ˢ Set.univ) z →
            fderiv ℝ φ z (1, 0) + H (gradient (fun x ↦ φ (z.1, x)) z.2) ≤ 0) ∧
      (∀ z ∈ Set.Ioi (0 : ℝ) ×ˢ Set.univ, ∀ φ : ℝ × EuclideanSpace ℝ (Fin d) → ℝ,
        ContDiffAt ℝ 1 φ z → IsLocalMinOn (fun y ↦ v y - φ y)
          (Set.Ioi (0 : ℝ) ×ˢ Set.univ) z →
            0 ≤ fderiv ℝ φ z (1, 0) + H (gradient (fun x ↦ φ (z.1, x)) z.2)) :=
  Iff.rfl

/-- **34.14**: for a convex superlinear Hamiltonian and Lipschitz initial data, the Hopf–Lax
infimum is finite for `t > 0`, is a viscosity solution of `v_t + H(∇v) = 0`, and tends to the
initial data as `t → 0⁺`. -/
theorem hopfLaxHamiltonian_viscosity {d : ℕ} (H v₀ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hH : ConvexOn ℝ Set.univ H)
    (hsuper : Tendsto (fun p : EuclideanSpace ℝ (Fin d) ↦ H p / ‖p‖) (Filter.comap norm atTop)
      atTop)
    {L : ℝ≥0} (hv₀ : LipschitzWith L v₀) :
    ∃ v : ℝ × EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ t : ℝ, 0 < t → ∀ x, hopfLaxHamiltonian H v₀ t x = v (t, x)) ∧
      IsHamiltonJacobiViscositySolution H v ∧ ∀ x,
        Tendsto (fun t : ℝ ↦ v (t, x)) (𝓝[>] 0) (𝓝 (v₀ x)) := by
  sorry

end CKMA
