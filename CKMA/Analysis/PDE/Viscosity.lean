/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.PDE.EllipticEstimates
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Viscosity comparison and Evans–Krylov regularity

Scalar viscosity subsolutions and supersolutions are tested at local smooth contacts.
Degenerate ellipticity uses the decreasing operator convention; the Hessian-only uniform
ellipticity convention is increasing and measured against trace. The comparison theorem
has positive zeroth order, while Evans–Krylov treats convex or concave uniformly elliptic
operators with Hölder forcing. Semicontinuity, local extrema and derivatives use Mathlib.
Sources: GAPS 33.23 and 33.30.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped ENNReal


/-- Continuous bilinear scalar Hessian jets. Operators below ignore antisymmetric parts
by the quadratic-form order in the ellipticity definition. -/
abbrev HessianJet (d : ℕ) := EuclideanRealSpace d →L[ℝ] EuclideanRealSpace d →L[ℝ] ℝ

/-- Positive semidefiniteness of a real bilinear Hessian increment. -/
def IsNonnegativeHessian {d : ℕ} (X : HessianJet d) : Prop := ∀ v, 0 ≤ X v v

/-- Degenerate ellipticity: increasing the Hessian decreases the equation operator. -/
def IsDegenerateElliptic {d : ℕ}
    (G : EuclideanRealSpace d → ℝ → (EuclideanRealSpace d →L[ℝ] ℝ) → HessianJet d → ℝ) : Prop :=
  ∀ x r p X Y, IsNonnegativeHessian (Y - X) → G x r p Y ≤ G x r p X

/-- Upper semicontinuous viscosity subsolutions, tested by local `C²` upper contacts. -/
def IsViscositySubsolution {d : ℕ}
    (G : EuclideanRealSpace d → ℝ → (EuclideanRealSpace d →L[ℝ] ℝ) → HessianJet d → ℝ)
    (Ω : Set (EuclideanRealSpace d)) (u : EuclideanRealSpace d → ℝ) : Prop :=
  UpperSemicontinuousOn u Ω ∧ ∀ x ∈ Ω, ∀ φ : EuclideanRealSpace d → ℝ,
    ContDiffAt ℝ 2 φ x → IsLocalMaxOn (fun y ↦ u y - φ y) Ω x →
      G x (u x) (fderiv ℝ φ x) (fderiv ℝ (fderiv ℝ φ) x) ≤ 0

/-- Lower semicontinuous viscosity supersolutions use lower contacts and the reverse inequality. -/
def IsViscositySupersolution {d : ℕ}
    (G : EuclideanRealSpace d → ℝ → (EuclideanRealSpace d →L[ℝ] ℝ) → HessianJet d → ℝ)
    (Ω : Set (EuclideanRealSpace d)) (u : EuclideanRealSpace d → ℝ) : Prop :=
  LowerSemicontinuousOn u Ω ∧ ∀ x ∈ Ω, ∀ φ : EuclideanRealSpace d → ℝ,
    ContDiffAt ℝ 2 φ x → IsLocalMinOn (fun y ↦ u y - φ y) Ω x →
      0 ≤ G x (u x) (fderiv ℝ φ x) (fderiv ℝ (fderiv ℝ φ) x)

/-- A continuous viscosity solution is both a subsolution and a supersolution. -/
def IsViscositySolution {d : ℕ}
    (G : EuclideanRealSpace d → ℝ → (EuclideanRealSpace d →L[ℝ] ℝ) → HessianJet d → ℝ)
    (Ω : Set (EuclideanRealSpace d)) (u : EuclideanRealSpace d → ℝ) : Prop :=
  ContinuousOn u Ω ∧ IsViscositySubsolution G Ω u ∧ IsViscositySupersolution G Ω u

/-- **33.23**: comparison for positive zeroth order and an autonomous degenerate elliptic part. -/
theorem viscosity_comparison {d : ℕ} (hd : 0 < d) {Ω : Set (EuclideanRealSpace d)}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) {γ : ℝ} (hγ : 0 < γ)
    (G₀ : (EuclideanRealSpace d →L[ℝ] ℝ) → HessianJet d → ℝ)
    (hGc : Continuous (fun z : (EuclideanRealSpace d →L[ℝ] ℝ) × HessianJet d ↦ G₀ z.1 z.2))
    (hGe : IsDegenerateElliptic (fun _ _ p X ↦ G₀ p X))
    (f u v : EuclideanRealSpace d → ℝ) (hf : ContinuousOn f (closure Ω))
    (hu : ContinuousOn u (closure Ω)) (hv : ContinuousOn v (closure Ω))
    (hus : IsViscositySubsolution (fun x r p X ↦ γ * r + G₀ p X - f x) Ω u)
    (hvs : IsViscositySupersolution (fun x r p X ↦ γ * r + G₀ p X - f x) Ω v)
    (hboundary : ∀ x ∈ frontier Ω, u x ≤ v x) : ∀ x ∈ Ω, u x ≤ v x := by
  sorry

/-- Uniform ellipticity in the increasing `F(D²u)` convention, measured against trace. -/
def IsUniformlyEllipticHessian {d : ℕ} (F : HessianJet d → ℝ) (ell Λ : ℝ) : Prop :=
  0 < ell ∧ ell ≤ Λ ∧ ∀ X P, IsNonnegativeHessian P →
    ell * euclideanHessianTrace P ≤ F (X + P) - F X ∧
      F (X + P) - F X ≤ Λ * euclideanHessianTrace P

/-- **33.30**: Evans–Krylov a priori regularity and estimate for convex or concave uniformly
elliptic Hessian operators, with Hölder forcing. The sign convention is `f-F(D²u)=0`. -/
theorem evans_krylov {d : ℕ} (hd : 0 < d) {α ell Λ : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (F : HessianJet d → ℝ) (he : IsUniformlyEllipticHessian F ell Λ)
    (hcv : ConvexOn ℝ Set.univ F ∨ ConcaveOn ℝ Set.univ F) :
    ∃ β C : ℝ, 0 < β ∧ β < 1 ∧ 0 < C ∧ ∀ u f : EuclideanRealSpace d → ℝ,
      holderGaugeOn α f (Metric.ball 0 2) ≠ ∞ → uniformGaugeOn u (Metric.ball 0 2) ≠ ∞ →
      IsViscositySolution (fun x _ _ X ↦ f x - F X) (Metric.ball 0 2) u →
      ContDiffOn ℝ 2 u (Metric.ball 0 1) ∧
      cTwoHolderGauge β u (Metric.ball 0 1) ≤ ENNReal.ofReal C *
        (uniformGaugeOn u (Metric.ball 0 2) + holderGaugeOn α f (Metric.ball 0 2) +
          ENNReal.ofReal |F 0|) := by
  sorry

end CKMA
