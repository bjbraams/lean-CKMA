/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.PDE.Euclidean
public import CKMA.Analysis.PDE.HolderGauge

import Mathlib.Topology.Semicontinuity.Basic

/-!
# Viscosity comparison and Evans–Krylov regularity

Scalar viscosity subsolutions and supersolutions are tested at local smooth contacts.
Degenerate ellipticity uses the decreasing operator convention; the Hessian-only uniform
ellipticity convention is increasing and measured against trace. The comparison theorem
has positive zeroth order, while Evans–Krylov treats convex or concave uniformly elliptic
operators with Hölder forcing, measured with the extended gauges of
`CKMA.Analysis.PDE.HolderGauge`. Semicontinuity, local extrema and derivatives use Mathlib.
Sources: GAPS 33.23 and 33.30.

## Main definitions

* `CKMA.HessianJet`, `CKMA.IsNonnegativeHessian`: Hessian jets and their positivity.
* `CKMA.IsDegenerateElliptic`: degenerate ellipticity of a second-order operator.
* `CKMA.IsViscositySubsolution`, `CKMA.IsViscositySupersolution`, `CKMA.IsViscositySolution`:
  viscosity subsolutions, supersolutions, and solutions.
* `CKMA.IsUniformlyEllipticHessian`: uniform ellipticity of a pure Hessian operator.

## Main results

* `CKMA.IsViscositySolution.continuousOn`: a viscosity solution is continuous on `Ω`.
* `CKMA.viscosity_comparison` (**33.23**): comparison principle for viscosity sub- and
  supersolutions on bounded open domains.
* `CKMA.evans_krylov` (**33.30**): interior `C^{2,α}` regularity and estimate for convex or
  concave fully nonlinear uniformly elliptic equations.
-/

public section

noncomputable section

namespace CKMA

open scoped ENNReal


/-- Continuous bilinear scalar Hessian jets. Operators below ignore antisymmetric parts
by the quadratic-form order in the ellipticity definition. -/
abbrev HessianJet (d : ℕ) := EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ

/-- Positive semidefiniteness of a real bilinear Hessian increment. -/
@[expose]
def IsNonnegativeHessian {d : ℕ} (X : HessianJet d) : Prop := ∀ v, 0 ≤ X v v

/-- A Hessian jet is nonnegative exactly when its quadratic form is. -/
theorem isNonnegativeHessian_iff {d : ℕ} {X : HessianJet d} :
    IsNonnegativeHessian X ↔ ∀ v, 0 ≤ X v v := Iff.rfl

/-- Degenerate ellipticity: increasing the Hessian decreases the equation operator. -/
@[expose]
def IsDegenerateElliptic {d : ℕ}
    (G : EuclideanSpace ℝ (Fin d) → ℝ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) → HessianJet d → ℝ) :
    Prop :=
  ∀ x r p X Y, IsNonnegativeHessian (Y - X) → G x r p Y ≤ G x r p X

/-- The defining monotonicity of a degenerate elliptic operator. -/
theorem isDegenerateElliptic_iff {d : ℕ}
    {G : EuclideanSpace ℝ (Fin d) → ℝ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) → HessianJet d → ℝ} :
    IsDegenerateElliptic G ↔
      ∀ x r p X Y, IsNonnegativeHessian (Y - X) → G x r p Y ≤ G x r p X := Iff.rfl

/-- Upper semicontinuous viscosity subsolutions, tested by local `C²` upper contacts. -/
@[expose]
def IsViscositySubsolution {d : ℕ}
    (G : EuclideanSpace ℝ (Fin d) → ℝ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) → HessianJet d → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (u : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  UpperSemicontinuousOn u Ω ∧ ∀ x ∈ Ω, ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ,
    ContDiffAt ℝ 2 φ x → IsLocalMaxOn (fun y ↦ u y - φ y) Ω x →
      G x (u x) (fderiv ℝ φ x) (fderiv ℝ (fderiv ℝ φ) x) ≤ 0

/-- The defining semicontinuity and upper-contact test of a viscosity subsolution. -/
theorem isViscositySubsolution_iff {d : ℕ}
    {G : EuclideanSpace ℝ (Fin d) → ℝ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) → HessianJet d → ℝ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))} {u : EuclideanSpace ℝ (Fin d) → ℝ} :
    IsViscositySubsolution G Ω u ↔
      UpperSemicontinuousOn u Ω ∧ ∀ x ∈ Ω, ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ,
        ContDiffAt ℝ 2 φ x → IsLocalMaxOn (fun y ↦ u y - φ y) Ω x →
          G x (u x) (fderiv ℝ φ x) (fderiv ℝ (fderiv ℝ φ) x) ≤ 0 := Iff.rfl

/-- Lower semicontinuous viscosity supersolutions use lower contacts and the reverse inequality. -/
@[expose]
def IsViscositySupersolution {d : ℕ}
    (G : EuclideanSpace ℝ (Fin d) → ℝ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) → HessianJet d → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (u : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  LowerSemicontinuousOn u Ω ∧ ∀ x ∈ Ω, ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ,
    ContDiffAt ℝ 2 φ x → IsLocalMinOn (fun y ↦ u y - φ y) Ω x →
      0 ≤ G x (u x) (fderiv ℝ φ x) (fderiv ℝ (fderiv ℝ φ) x)

/-- The defining semicontinuity and lower-contact test of a viscosity supersolution. -/
theorem isViscositySupersolution_iff {d : ℕ}
    {G : EuclideanSpace ℝ (Fin d) → ℝ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) → HessianJet d → ℝ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))} {u : EuclideanSpace ℝ (Fin d) → ℝ} :
    IsViscositySupersolution G Ω u ↔
      LowerSemicontinuousOn u Ω ∧ ∀ x ∈ Ω, ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ,
        ContDiffAt ℝ 2 φ x → IsLocalMinOn (fun y ↦ u y - φ y) Ω x →
          0 ≤ G x (u x) (fderiv ℝ φ x) (fderiv ℝ (fderiv ℝ φ) x) := Iff.rfl

/-- A viscosity solution is both a subsolution and a supersolution.
Continuity on `Ω` follows from the two semicontinuity hypotheses. -/
@[expose]
def IsViscositySolution {d : ℕ}
    (G : EuclideanSpace ℝ (Fin d) → ℝ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) → HessianJet d → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (u : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  IsViscositySubsolution G Ω u ∧ IsViscositySupersolution G Ω u

/-- A viscosity solution is exactly a subsolution that is also a supersolution. -/
theorem isViscositySolution_iff {d : ℕ}
    {G : EuclideanSpace ℝ (Fin d) → ℝ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) → HessianJet d → ℝ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))} {u : EuclideanSpace ℝ (Fin d) → ℝ} :
    IsViscositySolution G Ω u ↔ IsViscositySubsolution G Ω u ∧ IsViscositySupersolution G Ω u :=
  Iff.rfl

/-- Upper and lower semicontinuity of a viscosity solution give continuity on `Ω`. -/
theorem IsViscositySolution.continuousOn {d : ℕ}
    {G : EuclideanSpace ℝ (Fin d) → ℝ → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) → HessianJet d → ℝ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))} {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : IsViscositySolution G Ω u) : ContinuousOn u Ω :=
  continuousOn_iff_lower_upperSemicontinuousOn.2 ⟨h.2.1, h.1.1⟩

/-- **33.23**: comparison for positive zeroth order and an autonomous degenerate elliptic part. -/
theorem viscosity_comparison {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) {γ : ℝ} (hγ : 0 < γ)
    (G₀ : (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) → HessianJet d → ℝ)
    (hGc : Continuous (fun z : (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) × HessianJet d ↦ G₀ z.1 z.2))
    (hGe : IsDegenerateElliptic (fun _ _ p X ↦ G₀ p X))
    (f u v : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ContinuousOn f (closure Ω))
    (hu : ContinuousOn u (closure Ω)) (hv : ContinuousOn v (closure Ω))
    (hus : IsViscositySubsolution (fun x r p X ↦ γ * r + G₀ p X - f x) Ω u)
    (hvs : IsViscositySupersolution (fun x r p X ↦ γ * r + G₀ p X - f x) Ω v)
    (hboundary : ∀ x ∈ frontier Ω, u x ≤ v x) : ∀ x ∈ Ω, u x ≤ v x := by
  sorry

/-- Uniform ellipticity in the increasing `F(D²u)` convention, measured against trace. -/
@[expose]
def IsUniformlyEllipticHessian {d : ℕ} (F : HessianJet d → ℝ) (ell Λ : ℝ) : Prop :=
  0 < ell ∧ ell ≤ Λ ∧ ∀ X P, IsNonnegativeHessian P →
    ell * euclideanHessianTrace P ≤ F (X + P) - F X ∧
      F (X + P) - F X ≤ Λ * euclideanHessianTrace P

/-- The defining two-sided trace bounds of uniform Hessian ellipticity. -/
theorem isUniformlyEllipticHessian_iff {d : ℕ} {F : HessianJet d → ℝ} {ell Λ : ℝ} :
    IsUniformlyEllipticHessian F ell Λ ↔ 0 < ell ∧ ell ≤ Λ ∧ ∀ X P, IsNonnegativeHessian P →
      ell * euclideanHessianTrace P ≤ F (X + P) - F X ∧
        F (X + P) - F X ≤ Λ * euclideanHessianTrace P := Iff.rfl

/-- **33.30**: Evans–Krylov a priori regularity and estimate for convex or concave uniformly
elliptic Hessian operators, with Hölder forcing. The sign convention is `f-F(D²u)=0`. -/
theorem evans_krylov {d : ℕ} {α ell Λ : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (F : HessianJet d → ℝ) (he : IsUniformlyEllipticHessian F ell Λ)
    (hcv : ConvexOn ℝ Set.univ F ∨ ConcaveOn ℝ Set.univ F) :
    ∃ β C : ℝ, 0 < β ∧ β < 1 ∧ 0 < C ∧ ∀ u f : EuclideanSpace ℝ (Fin d) → ℝ,
      holderGaugeOn α f (Metric.ball 0 2) ≠ ∞ → uniformGaugeOn u (Metric.ball 0 2) ≠ ∞ →
      IsViscositySolution (fun x _ _ X ↦ f x - F X) (Metric.ball 0 2) u →
      ContDiffOn ℝ 2 u (Metric.ball 0 1) ∧
      cTwoHolderGauge β u (Metric.ball 0 1) ≤ ENNReal.ofReal C *
        (uniformGaugeOn u (Metric.ball 0 2) + holderGaugeOn α f (Metric.ball 0 2) +
          ENNReal.ofReal |F 0|) := by
  sorry

end CKMA
