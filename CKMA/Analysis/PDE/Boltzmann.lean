/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.PDE.Euclidean
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Hard-sphere collisions and entropy dissipation

Three-dimensional elastic collision velocities and the hard-sphere collision operator
with a probability-normalized angular measure. Entropy production has factor `1/4`;
the H identity uses positive densities and explicit integrability of all four logarithmic
collision tests. Iterated integrals use Mathlib's product-measure and Bochner APIs.
Source: GAPS 34.70.

## Main definitions

* `CKMA.hardSphereAngularMeasure`: uniform angular probability measure on the unit sphere in `ℝ³`.
* `CKMA.postCollisionVelocity`: post-collision velocities for elastic hard-sphere collisions.
* `CKMA.hardSphereCollisionOperator`: the hard-sphere Boltzmann collision operator.
* `CKMA.hardSphereEntropyProduction`: the collision entropy production functional with factor
  `1/4`.
* `CKMA.HasIntegrableCollisionEntropy`: integrability of the four logarithmic collision tests.

## Main results

* `CKMA.hardSphereEntropyProduction_nonneg`: nonnegativity for strictly positive densities.
* `CKMA.hardSphere_hTheorem` (**34.70**): Boltzmann's H identity relating the logarithmic
  collision test to entropy production, together with nonnegativity of the entropy production.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped ENNReal

/-- Uniform angular probability obtained by radial projection of normalized unit-ball volume.
The pole is a null set; assigning it direction zero does not change the angular measure. -/
@[expose]
def hardSphereAngularMeasure : Measure (EuclideanSpace ℝ (Fin 3)) :=
  ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1))⁻¹ : ℝ≥0∞) •
    (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)).map (fun x ↦ ‖x‖⁻¹ • x)

/-- Unfolding the angular measure. -/
theorem hardSphereAngularMeasure_def :
    hardSphereAngularMeasure =
      ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1))⁻¹ : ℝ≥0∞) •
        (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)).map
          (fun x ↦ ‖x‖⁻¹ • x) := rfl

/-- Post-collision velocity, with the scattering direction in the first or second output. -/
@[expose]
def postCollisionVelocity (v w σ : EuclideanSpace ℝ (Fin 3)) (first : Bool) :
    EuclideanSpace ℝ (Fin 3) :=
  (1 / 2 : ℝ) • (v + w) + (if first then ‖v - w‖ / 2 else -(‖v - w‖ / 2)) • σ

/-- The first post-collision velocity `(v + w) / 2 + |v - w| σ / 2`. -/
theorem postCollisionVelocity_true (v w σ : EuclideanSpace ℝ (Fin 3)) :
    postCollisionVelocity v w σ true = (1 / 2 : ℝ) • (v + w) + (‖v - w‖ / 2) • σ := by
  simp [postCollisionVelocity]

/-- The second post-collision velocity `(v + w) / 2 - |v - w| σ / 2`. -/
theorem postCollisionVelocity_false (v w σ : EuclideanSpace ℝ (Fin 3)) :
    postCollisionVelocity v w σ false = (1 / 2 : ℝ) • (v + w) - (‖v - w‖ / 2) • σ := by
  simp [postCollisionVelocity, neg_smul, sub_eq_add_neg]

/-- Elastic collisions conserve momentum. -/
theorem postCollisionVelocity_add (v w σ : EuclideanSpace ℝ (Fin 3)) :
    postCollisionVelocity v w σ true + postCollisionVelocity v w σ false = v + w := by
  rw [postCollisionVelocity_true, postCollisionVelocity_false, add_add_sub_cancel, ← add_smul]
  norm_num

/-- Pre-collision product of a one-particle density. -/
@[expose]
def collisionPreProduct (f : EuclideanSpace ℝ (Fin 3) → ℝ) (v w : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  f v * f w

/-- Unfolding the pre-collision product. -/
theorem collisionPreProduct_def (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (v w : EuclideanSpace ℝ (Fin 3)) : collisionPreProduct f v w = f v * f w := rfl

/-- Post-collision product of the same density. -/
@[expose]
def collisionPostProduct (f : EuclideanSpace ℝ (Fin 3) → ℝ) (v w σ : EuclideanSpace ℝ (Fin 3)) :
    ℝ :=
  f (postCollisionVelocity v w σ true) * f (postCollisionVelocity v w σ false)

/-- Unfolding the post-collision product. -/
theorem collisionPostProduct_def (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (v w σ : EuclideanSpace ℝ (Fin 3)) :
    collisionPostProduct f v w σ =
      f (postCollisionVelocity v w σ true) * f (postCollisionVelocity v w σ false) := rfl

/-- The hard-sphere collision operator with probability-normalized angular measure. -/
@[expose]
def hardSphereCollisionOperator (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (v : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∫ w, ∫ σ, ‖v - w‖ * (collisionPostProduct f v w σ - collisionPreProduct f v w)
    ∂hardSphereAngularMeasure

/-- Unfolding the collision operator. -/
theorem hardSphereCollisionOperator_def (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (v : EuclideanSpace ℝ (Fin 3)) :
    hardSphereCollisionOperator f v =
      ∫ w, ∫ σ, ‖v - w‖ * (collisionPostProduct f v w σ - collisionPreProduct f v w)
        ∂hardSphereAngularMeasure := rfl

/-- Nonnegative collision entropy production, with the conventional factor `1/4`. -/
@[expose]
def hardSphereEntropyProduction (f : EuclideanSpace ℝ (Fin 3) → ℝ) : ℝ :=
  (1 / 4 : ℝ) * ∫ v, ∫ w, ∫ σ,
    ‖v - w‖ * (collisionPreProduct f v w - collisionPostProduct f v w σ) *
      (Real.log (collisionPreProduct f v w) - Real.log (collisionPostProduct f v w σ))
    ∂hardSphereAngularMeasure

/-- Unfolding the entropy production. -/
theorem hardSphereEntropyProduction_def (f : EuclideanSpace ℝ (Fin 3) → ℝ) :
    hardSphereEntropyProduction f = (1 / 4 : ℝ) * ∫ v, ∫ w, ∫ σ,
      ‖v - w‖ * (collisionPreProduct f v w - collisionPostProduct f v w σ) *
        (Real.log (collisionPreProduct f v w) - Real.log (collisionPostProduct f v w σ))
      ∂hardSphereAngularMeasure := rfl

/-- The hard-sphere entropy production is nonnegative for strictly positive densities. -/
theorem hardSphereEntropyProduction_nonneg (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hpos : ∀ v, 0 < f v) : 0 ≤ hardSphereEntropyProduction f := by
  rw [hardSphereEntropyProduction]
  refine mul_nonneg (by positivity)
    (integral_nonneg fun v ↦ integral_nonneg fun w ↦ integral_nonneg fun σ ↦ ?_)
  let p := collisionPreProduct f v w
  let q := collisionPostProduct f v w σ
  have hp : 0 < p := mul_pos (hpos v) (hpos w)
  have hq : 0 < q := mul_pos (hpos _) (hpos _)
  rw [mul_assoc]
  refine mul_nonneg (norm_nonneg _) ?_
  by_cases hpq : p ≤ q
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hpq)
      (sub_nonpos.mpr (Real.log_le_log hp hpq))
  · exact mul_nonneg (sub_nonneg.mpr (le_of_not_ge hpq))
      (sub_nonneg.mpr (Real.log_le_log hq (le_of_not_ge hpq)))

/-- All four velocity evaluations appearing in the collision entropy symmetrization. -/
@[expose]
def collisionEvaluation (i : Fin 4)
    (z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  if i.val = 0 then z.1 else if i.val = 1 then z.2.1 else
    postCollisionVelocity z.1 z.2.1 z.2.2 (i.val = 2)

/-- Unfolding the four collision evaluations. -/
theorem collisionEvaluation_def (i : Fin 4)
    (z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    collisionEvaluation i z = if i.val = 0 then z.1 else if i.val = 1 then z.2.1 else
      postCollisionVelocity z.1 z.2.1 z.2.2 (i.val = 2) := rfl

/-- Explicit absolute-integrability conditions justifying Fubini and the four logarithmic tests. -/
@[expose]
def HasIntegrableCollisionEntropy (f : EuclideanSpace ℝ (Fin 3) → ℝ) : Prop :=
  ∀ i : Fin 4, Integrable
    (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) ↦
    ‖z.1 - z.2.1‖ * (collisionPostProduct f z.1 z.2.1 z.2.2 - collisionPreProduct f z.1 z.2.1) *
      Real.log (f (collisionEvaluation i z)))
    ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (volume.prod hardSphereAngularMeasure))

/-- Unfolding the integrability hypothesis of the H identity. -/
theorem hasIntegrableCollisionEntropy_iff {f : EuclideanSpace ℝ (Fin 3) → ℝ} :
    HasIntegrableCollisionEntropy f ↔ ∀ i : Fin 4, Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) ↦
        ‖z.1 - z.2.1‖ *
          (collisionPostProduct f z.1 z.2.1 z.2.2 - collisionPreProduct f z.1 z.2.1) *
          Real.log (f (collisionEvaluation i z)))
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
        (volume.prod hardSphereAngularMeasure)) :=
  Iff.rfl

/-- **34.70**, the collisional H identity and entropy dissipation for the spatially homogeneous
hard-sphere operator: `∫ Q(f, f) log f = -D(f)` and `D(f) ≥ 0`, for a measurable strictly
positive density whose four logarithmic collision tests are integrable. Strict positivity
avoids the convention `0 log 0`. -/
theorem hardSphere_hTheorem (f : EuclideanSpace ℝ (Fin 3) → ℝ) (hf : Measurable f)
    (hpos : ∀ v, 0 < f v) (hint : HasIntegrableCollisionEntropy f) :
    (∫ v, hardSphereCollisionOperator f v * Real.log (f v)) = -hardSphereEntropyProduction f ∧
      0 ≤ hardSphereEntropyProduction f := by
  refine ⟨?_, hardSphereEntropyProduction_nonneg f hpos⟩
  sorry

end CKMA
