/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Topology.Algebra.PontryaginDual
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Pontryagin duality and LCA Fourier analysis

The evaluation pairing identifies a locally compact abelian group with its double
character dual. With a compatible dual Haar measure, the Fourier integral extends to
a Plancherel unitary and satisfies Hausdorff–Young bounds on `L¹ ∩ Lᵖ`. The Plancherel
statement assumes second countability. Character groups use Mathlib's compact-open
Pontryagin dual.

Sources: GAPS 28.24 and 28.29.

## Main definitions

* `CKMA.groupFourierIntegral`: Fourier integral on a locally compact abelian group against a
  continuous unitary character.

## Main results

* `CKMA.exists_pontryaginDual_equiv`: Pontryagin biduality isomorphism for locally compact abelian
  groups (**28.24**).
* `CKMA.exists_groupPlancherel`: Plancherel theorem and Hausdorff–Young inequality on
  second-countable locally compact abelian groups (**28.29**).
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped ENNReal ComplexConjugate

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G]

/-- **28.24**: the evaluation pairing identifies every LCA group with its double Pontryagin dual.
Mathlib's compact-open continuous-character group is used at both dual levels. -/
theorem exists_pontryaginDual_equiv :
    ∃ U : G ≃ₜ* PontryaginDual (PontryaginDual G), ∀ x χ, U x χ = χ x := by
  sorry

/-- The Fourier integral on a locally compact abelian group at a continuous unitary character. -/
@[expose]
def groupFourierIntegral [MeasurableSpace G] (μ : Measure G) (f : G → ℂ)
    (χ : PontryaginDual G) : ℂ := ∫ x, f x * conj (χ x : ℂ) ∂μ

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] in
/-- Unfolding the group Fourier integral. -/
theorem groupFourierIntegral_def [MeasurableSpace G] (μ : Measure G) (f : G → ℂ)
    (χ : PontryaginDual G) : groupFourierIntegral μ f χ = ∫ x, f x * conj (χ x : ℂ) ∂μ := rfl

/-- **28.29**, for a second-countable LCA group: there is a Haar measure on the dual for which the
Fourier integral extends from `L¹ ∩ L²` to a unitary `L²(G) ≃ L²(Ĝ)` (Plancherel) and satisfies
the Hausdorff–Young bound `‖f̂‖_q ≤ ‖f‖_p` on `L¹ ∩ Lᵖ` for `1 ≤ p ≤ 2`, `1/p + 1/q = 1`. -/
theorem exists_groupPlancherel [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    (μ : Measure G) [Measure.IsHaarMeasure μ] :
    ∃ ν : Measure (PontryaginDual G), Measure.IsHaarMeasure ν ∧
      (∃ U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν,
        ∀ f : Lp ℂ 2 μ, Integrable (f : G → ℂ) μ →
          (U f : PontryaginDual G → ℂ) =ᵐ[ν] groupFourierIntegral μ f) ∧
      ∀ p q : ℝ≥0∞, 1 ≤ p → p ≤ 2 → p⁻¹ + q⁻¹ = 1 →
        ∀ f : G → ℂ, Integrable f μ → MemLp f p μ →
          eLpNorm (groupFourierIntegral μ f) q ν ≤ eLpNorm f p μ := by
  sorry

end CKMA
