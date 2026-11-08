/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.PDE.Euclidean
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# Hard-sphere collisions and entropy dissipation

Three-dimensional elastic collision velocities and the hard-sphere collision operator
with a probability-normalized angular measure. Entropy production has factor `1/4`;
the H identity uses positive densities and explicit integrability of all four logarithmic
collision tests. Iterated integrals use Mathlib's product-measure and Bochner APIs.
Source: GAPS 34.70.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped ENNReal

/-- Uniform angular probability obtained by radial projection of normalized unit-ball volume.
The pole is a null set; assigning it direction zero does not change the angular measure. -/
def hardSphereAngularMeasure : Measure (EuclideanRealSpace 3) :=
  ((volume (Metric.ball (0 : EuclideanRealSpace 3) 1))⁻¹ : ℝ≥0∞) •
    (volume.restrict (Metric.ball (0 : EuclideanRealSpace 3) 1)).map (fun x ↦ ‖x‖⁻¹ • x)

/-- Post-collision velocity, with the scattering direction in the first or second output. -/
def postCollisionVelocity (v w σ : EuclideanRealSpace 3) (first : Bool) : EuclideanRealSpace 3 :=
  (1 / 2 : ℝ) • (v + w) + (if first then ‖v - w‖ / 2 else -(‖v - w‖ / 2)) • σ

/-- Pre-collision product of a one-particle density. -/
def collisionPreProduct (f : EuclideanRealSpace 3 → ℝ) (v w : EuclideanRealSpace 3) : ℝ := f v * f w

/-- Post-collision product of the same density. -/
def collisionPostProduct (f : EuclideanRealSpace 3 → ℝ) (v w σ : EuclideanRealSpace 3) : ℝ :=
  f (postCollisionVelocity v w σ true) * f (postCollisionVelocity v w σ false)

/-- The hard-sphere collision operator with probability-normalized angular measure. -/
def hardSphereCollisionOperator (f : EuclideanRealSpace 3 → ℝ) (v : EuclideanRealSpace 3) : ℝ :=
  ∫ w, ∫ σ, ‖v - w‖ * (collisionPostProduct f v w σ - collisionPreProduct f v w)
    ∂hardSphereAngularMeasure

/-- Nonnegative collision entropy production, with the conventional factor `1/4`. -/
def hardSphereEntropyProduction (f : EuclideanRealSpace 3 → ℝ) : ℝ :=
  (1 / 4 : ℝ) * ∫ v, ∫ w, ∫ σ,
    ‖v - w‖ * (collisionPreProduct f v w - collisionPostProduct f v w σ) *
      (Real.log (collisionPreProduct f v w) - Real.log (collisionPostProduct f v w σ))
    ∂hardSphereAngularMeasure

/-- All four velocity evaluations appearing in the collision entropy symmetrization. -/
def collisionEvaluation (i : Fin 4)
    (z : EuclideanRealSpace 3 × EuclideanRealSpace 3 × EuclideanRealSpace 3) : EuclideanRealSpace 3
      :=
  if i.val = 0 then z.1 else if i.val = 1 then z.2.1 else
    postCollisionVelocity z.1 z.2.1 z.2.2 (i.val = 2)

/-- Explicit absolute-integrability conditions justifying Fubini and the four logarithmic tests. -/
def HasIntegrableCollisionEntropy (f : EuclideanRealSpace 3 → ℝ) : Prop :=
  ∀ i : Fin 4, Integrable (fun z : EuclideanRealSpace 3 × EuclideanRealSpace 3 × EuclideanRealSpace
    3 ↦
    ‖z.1 - z.2.1‖ * (collisionPostProduct f z.1 z.2.1 z.2.2 - collisionPreProduct f z.1 z.2.1) *
      Real.log (f (collisionEvaluation i z)))
    ((volume : Measure (EuclideanRealSpace 3)).prod (volume.prod hardSphereAngularMeasure))

/-- **34.70**, the collisional H identity and entropy dissipation.
The transport part of the spatially inhomogeneous theorem is a separate interface.
Strict positivity avoids interpreting `0 log 0` in this first classical formulation. -/
theorem hardSphere_hTheorem (f : EuclideanRealSpace 3 → ℝ) (hf : Measurable f)
    (hpos : ∀ v, 0 < f v) (hint : HasIntegrableCollisionEntropy f) :
    (∫ v, hardSphereCollisionOperator f v * Real.log (f v)) = -hardSphereEntropyProduction f ∧
      0 ≤ hardSphereEntropyProduction f := by
  sorry

end CKMA
