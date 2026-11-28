/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.PDE.Euclidean
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Leray–Hopf existence and two-dimensional uniqueness

Incompressible weak momentum equations for nonnegative-time curves in the actual L²
velocity space. Leray–Hopf solutions have weak continuity, measurable weak gradients,
local finite dissipation and energy inequalities from time zero and almost every starting
time. The existence statement is three-dimensional; velocity uniqueness is two-dimensional
and does not identify arbitrary representatives of the weak gradient.
Sources: GAPS 34.54 and 34.55. Weak derivatives use TauCeti; L² and integration use Mathlib.

## Main definitions

* `CKMA.VelocityLTwo`: square-integrable velocity fields on `ℝ^d`.
* `CKMA.IsDivergenceFreeField`: distributional incompressibility of a velocity field.
* `CKMA.IsWeaklyContinuousVelocity`: weak `L²` continuity of a velocity curve.
* `CKMA.SatisfiesWeakNavierStokes`: the unforced viscous weak momentum equation.
* `CKMA.viscousDissipation`: viscous dissipation of a candidate spatial weak derivative.
* `CKMA.IsLerayHopfSolution`: Leray–Hopf weak solutions satisfying the energy inequalities.

## Main results

* `CKMA.exists_lerayHopf_threeDimensional` (**34.54**): existence of global Leray–Hopf weak
  solutions in dimension three.
* `CKMA.existsUnique_lerayHopf_twoDimensional` (**34.55**): existence and uniqueness of the
  Leray–Hopf velocity curve in dimension two.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped NNReal ENNReal InnerProductSpace

/-- Square-integrable velocity fields with their actual Hilbert-space structure. -/
abbrev VelocityLTwo (d : ℕ) :=
  Lp (EuclideanSpace ℝ (Fin d)) 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))

/-- Distributional incompressibility, tested by gradients of compactly supported smooth scalars. -/
@[expose]
def IsDivergenceFreeField {d : ℕ} (u : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, IsCompactSmoothTestOn Set.univ φ →
    ∫ x, ⟪u x, gradient φ x⟫_ℝ = 0

/-- Unfolding distributional incompressibility. -/
theorem isDivergenceFreeField_iff {d : ℕ}
    {u : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} :
    IsDivergenceFreeField u ↔ ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ,
      IsCompactSmoothTestOn Set.univ φ → ∫ x, ⟪u x, gradient φ x⟫_ℝ = 0 := Iff.rfl

/-- The zero field is divergence free. -/
theorem isDivergenceFreeField_zero {d : ℕ} :
    IsDivergenceFreeField (0 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :=
  fun _ _ ↦ by simp

/-- Weak continuity of a nonnegative-time velocity curve, using the Hilbert dual pairing. -/
@[expose]
def IsWeaklyContinuousVelocity {d : ℕ} (u : ℝ≥0 → VelocityLTwo d) : Prop :=
  ∀ v : VelocityLTwo d, Continuous (fun t ↦ ⟪u t, v⟫_ℝ)

/-- Unfolding weak continuity. -/
theorem isWeaklyContinuousVelocity_iff {d : ℕ} {u : ℝ≥0 → VelocityLTwo d} :
    IsWeaklyContinuousVelocity u ↔ ∀ v : VelocityLTwo d, Continuous (fun t ↦ ⟪u t, v⟫_ℝ) :=
  Iff.rfl

/-- A norm-continuous velocity curve is weakly continuous. -/
theorem isWeaklyContinuousVelocity_of_continuous {d : ℕ} {u : ℝ≥0 → VelocityLTwo d}
    (hu : Continuous u) : IsWeaklyContinuousVelocity u :=
  fun _ ↦ hu.inner continuous_const

/-- The unforced viscous weak momentum equation, tested against divergence-free smooth
spacetime fields. Two spatial integrations by parts put the viscosity on the test field.
Each identity is a Bochner integral, so a non-integrable integrand has integral `0`. -/
@[expose]
def SatisfiesWeakNavierStokes {d : ℕ} (ν : ℝ) (u₀ : VelocityLTwo d)
    (u : ℝ≥0 → VelocityLTwo d) : Prop :=
  ∀ φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
    IsCompactSmoothTestOn Set.univ φ →
    (∀ t x, euclideanDivergence (fun y ↦ φ (t, y)) x = 0) →
    (∫ t in Set.Ioi (0 : ℝ), ∫ x,
      ⟪u t.toNNReal x, deriv (fun s ↦ φ (s, x)) t⟫_ℝ +
      ⟪u t.toNNReal x, fderiv ℝ (fun y ↦ φ (t, y)) x (u t.toNNReal x)⟫_ℝ +
      ν * ⟪u t.toNNReal x, Laplacian.laplacian (fun y ↦ φ (t, y)) x⟫_ℝ) +
      (∫ x, ⟪u₀ x, φ (0, x)⟫_ℝ) = 0

/-- Unfolding the weak momentum equation. -/
theorem satisfiesWeakNavierStokes_iff {d : ℕ} {ν : ℝ} {u₀ : VelocityLTwo d}
    {u : ℝ≥0 → VelocityLTwo d} :
    SatisfiesWeakNavierStokes ν u₀ u ↔
      ∀ φ : ℝ × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        IsCompactSmoothTestOn Set.univ φ →
        (∀ t x, euclideanDivergence (fun y ↦ φ (t, y)) x = 0) →
        (∫ t in Set.Ioi (0 : ℝ), ∫ x,
          ⟪u t.toNNReal x, deriv (fun s ↦ φ (s, x)) t⟫_ℝ +
          ⟪u t.toNNReal x, fderiv ℝ (fun y ↦ φ (t, y)) x (u t.toNNReal x)⟫_ℝ +
          ν * ⟪u t.toNNReal x, Laplacian.laplacian (fun y ↦ φ (t, y)) x⟫_ℝ) +
          (∫ x, ⟪u₀ x, φ (0, x)⟫_ℝ) = 0 :=
  Iff.rfl

/-- The viscous dissipation associated with a candidate spatial weak derivative. -/
@[expose]
def viscousDissipation {d : ℕ}
    (G : ℝ≥0 → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (t : ℝ) : ℝ := ∫ x, vectorGradientEnergy (G t.toNNReal x)

/-- Unfolding the viscous dissipation. -/
theorem viscousDissipation_def {d : ℕ}
    (G : ℝ≥0 → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    viscousDissipation G t = ∫ x, vectorGradientEnergy (G t.toNNReal x) := rfl

/-- The viscous dissipation is nonnegative. -/
theorem viscousDissipation_nonneg {d : ℕ}
    (G : ℝ≥0 → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    0 ≤ viscousDissipation G t :=
  integral_nonneg fun _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- Leray–Hopf solutions with actual weak spatial derivatives, weak `L²` continuity,
local finite dissipation, the weak equation, and the strong energy inequality for a.e.
starting time as well as time zero. Curves are indexed by `ℝ≥0`, so uniqueness does not
accidentally constrain arbitrary negative-time extensions. -/
@[expose]
def IsLerayHopfSolution {d : ℕ} (ν : ℝ) (u₀ : VelocityLTwo d) (u : ℝ≥0 → VelocityLTwo d)
    (G : ℝ≥0 → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) : Prop :=
  u 0 = u₀ ∧ IsWeaklyContinuousVelocity u ∧
  (∀ t, IsDivergenceFreeField (u t)) ∧
  AEStronglyMeasurable (fun t : ℝ ↦ u t.toNNReal) (volume.restrict (Set.Ioi 0)) ∧
  AEStronglyMeasurable (fun z : ℝ × EuclideanSpace ℝ (Fin d) ↦ G z.1.toNNReal z.2)
    (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod volume) ∧
  (∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
    TauCeti.HasWeakFDerivOn volume ⊤ (u t.toNNReal) (G t.toNNReal)) ∧
  (∀ T : ℝ, 0 < T → (∫⁻ t in Set.Ioo (0 : ℝ) T, ∫⁻ x,
    ENNReal.ofReal (vectorGradientEnergy (G t.toNNReal x))) < ∞) ∧
  SatisfiesWeakNavierStokes ν u₀ u ∧
  (∀ t : ℝ≥0, ‖u t‖ ^ 2 + 2 * ν * (∫ s in (0 : ℝ)..t, viscousDissipation G s) ≤ ‖u₀‖ ^ 2) ∧
  (∀ᵐ (s : ℝ) ∂volume.restrict (Set.Ioi (0 : ℝ)), ∀ t : ℝ≥0, s ≤ (t : ℝ) →
    ‖u t‖ ^ 2 + 2 * ν * (∫ r in s..(t : ℝ), viscousDissipation G r) ≤ ‖u s.toNNReal‖ ^ 2)

section IsLerayHopfSolution

variable {d : ℕ} {ν : ℝ} {u₀ : VelocityLTwo d} {u : ℝ≥0 → VelocityLTwo d}
  {G : ℝ≥0 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)}

/-- Unfolding the Leray–Hopf predicate. -/
theorem isLerayHopfSolution_iff :
    IsLerayHopfSolution ν u₀ u G ↔
      u 0 = u₀ ∧ IsWeaklyContinuousVelocity u ∧
      (∀ t, IsDivergenceFreeField (u t)) ∧
      AEStronglyMeasurable (fun t : ℝ ↦ u t.toNNReal) (volume.restrict (Set.Ioi 0)) ∧
      AEStronglyMeasurable (fun z : ℝ × EuclideanSpace ℝ (Fin d) ↦ G z.1.toNNReal z.2)
        (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod volume) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        TauCeti.HasWeakFDerivOn volume ⊤ (u t.toNNReal) (G t.toNNReal)) ∧
      (∀ T : ℝ, 0 < T → (∫⁻ t in Set.Ioo (0 : ℝ) T, ∫⁻ x,
        ENNReal.ofReal (vectorGradientEnergy (G t.toNNReal x))) < ∞) ∧
      SatisfiesWeakNavierStokes ν u₀ u ∧
      (∀ t : ℝ≥0, ‖u t‖ ^ 2 + 2 * ν * (∫ s in (0 : ℝ)..t, viscousDissipation G s) ≤
        ‖u₀‖ ^ 2) ∧
      (∀ᵐ (s : ℝ) ∂volume.restrict (Set.Ioi (0 : ℝ)), ∀ t : ℝ≥0, s ≤ (t : ℝ) →
        ‖u t‖ ^ 2 + 2 * ν * (∫ r in s..(t : ℝ), viscousDissipation G r) ≤
          ‖u s.toNNReal‖ ^ 2) :=
  Iff.rfl

/-- A Leray–Hopf solution starts at its initial datum. -/
theorem IsLerayHopfSolution.apply_zero (h : IsLerayHopfSolution ν u₀ u G) : u 0 = u₀ := h.1

/-- A Leray–Hopf solution is weakly continuous. -/
theorem IsLerayHopfSolution.isWeaklyContinuousVelocity (h : IsLerayHopfSolution ν u₀ u G) :
    IsWeaklyContinuousVelocity u := h.2.1

/-- A Leray–Hopf solution is divergence free at every time. -/
theorem IsLerayHopfSolution.isDivergenceFreeField (h : IsLerayHopfSolution ν u₀ u G) (t : ℝ≥0) :
    IsDivergenceFreeField (u t) := h.2.2.1 t

/-- A Leray–Hopf solution satisfies the weak momentum equation. -/
theorem IsLerayHopfSolution.satisfiesWeakNavierStokes (h : IsLerayHopfSolution ν u₀ u G) :
    SatisfiesWeakNavierStokes ν u₀ u := h.2.2.2.2.2.2.2.1

/-- The energy inequality from time zero. -/
theorem IsLerayHopfSolution.energy_le (h : IsLerayHopfSolution ν u₀ u G) (t : ℝ≥0) :
    ‖u t‖ ^ 2 + 2 * ν * (∫ s in (0 : ℝ)..t, viscousDissipation G s) ≤ ‖u₀‖ ^ 2 :=
  h.2.2.2.2.2.2.2.2.1 t

/-- For `ν ≥ 0` the kinetic energy of a Leray–Hopf solution does not exceed its initial value. -/
theorem IsLerayHopfSolution.norm_le (h : IsLerayHopfSolution ν u₀ u G) (hν : 0 ≤ ν)
    (t : ℝ≥0) : ‖u t‖ ≤ ‖u₀‖ := by
  have hD : 0 ≤ ∫ s in (0 : ℝ)..t, viscousDissipation G s :=
    intervalIntegral.integral_nonneg t.2 fun s _ ↦ viscousDissipation_nonneg G s
  have := h.energy_le t
  have h2 : ‖u t‖ ^ 2 ≤ ‖u₀‖ ^ 2 := by nlinarith [mul_nonneg hν hD]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

end IsLerayHopfSolution

/-- **34.54**: for `ν > 0` every divergence-free `u₀ ∈ L²(ℝ³)` admits a global Leray–Hopf weak
solution. -/
theorem exists_lerayHopf_threeDimensional {ν : ℝ} (hν : 0 < ν) (u₀ : VelocityLTwo 3)
    (hdiv : IsDivergenceFreeField u₀) :
    ∃ (u : ℝ≥0 → VelocityLTwo 3)
      (G : ℝ≥0 → EuclideanSpace ℝ (Fin 3) →
        EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
      IsLerayHopfSolution ν u₀ u G := by
  sorry

/-- **34.55**: for `ν > 0` and divergence-free `u₀ ∈ L²(ℝ²)` there is exactly one Leray–Hopf
velocity curve. Gradient representatives are quantified existentially because they are only
determined a.e. -/
theorem existsUnique_lerayHopf_twoDimensional {ν : ℝ} (hν : 0 < ν) (u₀ : VelocityLTwo 2)
    (hdiv : IsDivergenceFreeField u₀) :
    ∃! u : ℝ≥0 → VelocityLTwo 2,
      ∃ G : ℝ≥0 → EuclideanSpace ℝ (Fin 2) →
          EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2),
        IsLerayHopfSolution ν u₀ u G := by
  sorry

end CKMA
