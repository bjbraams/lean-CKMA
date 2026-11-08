/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.PDE.Euclidean
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Leray–Hopf existence and two-dimensional uniqueness

Incompressible weak momentum equations for nonnegative-time curves in the actual L²
velocity space. Leray–Hopf solutions have weak continuity, measurable weak gradients,
local finite dissipation and energy inequalities from time zero and almost every starting
time. The existence statement is three-dimensional; velocity uniqueness is two-dimensional
and does not identify arbitrary representatives of the weak gradient.
Sources: GAPS 34.54 and 34.55. Weak derivatives use TauCeti; L² and integration use Mathlib.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped NNReal ENNReal InnerProductSpace

/-- Square-integrable velocity fields with their actual Hilbert-space structure. -/
abbrev VelocityLTwo (d : ℕ) := Lp (EuclideanRealSpace d) 2 (volume : Measure (EuclideanRealSpace d))

/-- Distributional incompressibility, tested by gradients of compactly supported smooth scalars. -/
def IsDivergenceFreeField {d : ℕ} (u : EuclideanRealSpace d → EuclideanRealSpace d) : Prop :=
  ∀ φ : EuclideanRealSpace d → ℝ, IsCompactSmoothTestOn Set.univ φ →
    ∫ x, ⟪u x, gradient φ x⟫_ℝ = 0

/-- Weak continuity of a nonnegative-time velocity curve, using the Hilbert dual pairing. -/
def IsWeaklyContinuousVelocity {d : ℕ} (u : ℝ≥0 → VelocityLTwo d) : Prop :=
  ∀ v : VelocityLTwo d, Continuous (fun t ↦ ⟪u t, v⟫_ℝ)

/-- The unforced viscous weak momentum equation, tested against divergence-free smooth
spacetime fields. Two spatial integrations by parts put the viscosity on the test field. -/
def SatisfiesWeakNavierStokes {d : ℕ} (ν : ℝ) (u₀ : VelocityLTwo d)
    (u : ℝ≥0 → VelocityLTwo d) : Prop :=
  ∀ φ : ℝ × EuclideanRealSpace d → EuclideanRealSpace d,
    IsCompactSmoothTestOn Set.univ φ →
    (∀ t x, euclideanDivergence (fun y ↦ φ (t, y)) x = 0) →
    (∫ t in Set.Ioi (0 : ℝ), ∫ x,
      ⟪u t.toNNReal x, deriv (fun s ↦ φ (s, x)) t⟫_ℝ +
      ⟪u t.toNNReal x, fderiv ℝ (fun y ↦ φ (t, y)) x (u t.toNNReal x)⟫_ℝ +
      ν * ⟪u t.toNNReal x, Laplacian.laplacian (fun y ↦ φ (t, y)) x⟫_ℝ) +
      (∫ x, ⟪u₀ x, φ (0, x)⟫_ℝ) = 0

/-- The viscous dissipation associated with a candidate spatial weak derivative. -/
def viscousDissipation {d : ℕ}
    (G : ℝ≥0 → EuclideanRealSpace d → EuclideanRealSpace d →L[ℝ] EuclideanRealSpace d)
    (t : ℝ) : ℝ := ∫ x, vectorGradientEnergy (G t.toNNReal x)

/-- Leray–Hopf solutions with actual weak spatial derivatives, weak `L²` continuity,
local finite dissipation, the weak equation, and the strong energy inequality for a.e.
starting time as well as time zero. Curves are indexed by `ℝ≥0`, so uniqueness does not
accidentally constrain arbitrary negative-time extensions. -/
def IsLerayHopfSolution {d : ℕ} (ν : ℝ) (u₀ : VelocityLTwo d) (u : ℝ≥0 → VelocityLTwo d)
    (G : ℝ≥0 → EuclideanRealSpace d → EuclideanRealSpace d →L[ℝ] EuclideanRealSpace d) : Prop :=
  u 0 = u₀ ∧ IsWeaklyContinuousVelocity u ∧
  (∀ t, IsDivergenceFreeField (u t)) ∧
  AEStronglyMeasurable (fun t : ℝ ↦ u t.toNNReal) (volume.restrict (Set.Ioi 0)) ∧
  AEStronglyMeasurable (fun z : ℝ × EuclideanRealSpace d ↦ G z.1.toNNReal z.2)
    (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod volume) ∧
  (∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
    TauCeti.HasWeakFDerivOn volume ⊤ (u t.toNNReal) (G t.toNNReal)) ∧
  (∀ T : ℝ, 0 < T → (∫⁻ t in Set.Ioo (0 : ℝ) T, ∫⁻ x,
    ENNReal.ofReal (vectorGradientEnergy (G t.toNNReal x))) < ∞) ∧
  SatisfiesWeakNavierStokes ν u₀ u ∧
  (∀ t : ℝ≥0, ‖u t‖ ^ 2 + 2 * ν * (∫ s in (0 : ℝ)..t, viscousDissipation G s) ≤ ‖u₀‖ ^ 2) ∧
  (∀ᵐ (s : ℝ) ∂volume.restrict (Set.Ioi (0 : ℝ)), ∀ t : ℝ≥0, s ≤ (t : ℝ) →
    ‖u t‖ ^ 2 + 2 * ν * (∫ r in s..(t : ℝ), viscousDissipation G r) ≤ ‖u s.toNNReal‖ ^ 2)

/-- **34.54**: global three-dimensional Leray–Hopf existence on Euclidean space.
No uniqueness is asserted in dimension three. -/
theorem exists_lerayHopf_threeDimensional {ν : ℝ} (hν : 0 < ν) (u₀ : VelocityLTwo 3)
    (hdiv : IsDivergenceFreeField u₀) :
    ∃ (u : ℝ≥0 → VelocityLTwo 3)
      (G : ℝ≥0 → EuclideanRealSpace 3 → EuclideanRealSpace 3 →L[ℝ] EuclideanRealSpace 3),
      IsLerayHopfSolution ν u₀ u G := by
  sorry

/-- **34.55**: the two-dimensional global energy-class velocity is unique.
Gradient representatives are quantified existentially because they are only determined a.e. -/
theorem existsUnique_lerayHopf_twoDimensional {ν : ℝ} (hν : 0 < ν) (u₀ : VelocityLTwo 2)
    (hdiv : IsDivergenceFreeField u₀) :
    ∃! u : ℝ≥0 → VelocityLTwo 2,
      ∃ G : ℝ≥0 → EuclideanRealSpace 2 → EuclideanRealSpace 2 →L[ℝ] EuclideanRealSpace 2,
        IsLerayHopfSolution ν u₀ u G := by
  sorry

end CKMA
