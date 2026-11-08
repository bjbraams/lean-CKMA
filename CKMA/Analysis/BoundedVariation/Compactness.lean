/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.TotalVariation
public import TauCeti.Analysis.BoundedVariation.Perimeter
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# BV compactness and the coarea formula

Integrable scalar functions of bounded distributional variation, their size bounds,
and compactness for families supported in a common compact set. The coarea formula
expresses total variation through perimeters of superlevel sets, retaining infinite values.
Variation, perimeter and their lower semicontinuity are the objects of TauCeti's
`Analysis.BoundedVariation.TotalVariation` and `Perimeter` modules.
Sources: GAPS 37.24 and 37.30.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal

/-- Integrable functions of finite variation, using TauCeti's actual distributional variation. -/
def IsBVFunctionOn {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  IntegrableOn u Ω ∧ TauCeti.totalVariationOn volume Ω u < ∞

/-- The extended L1-plus-variation bound; no representative quotient or norm instance is assumed. -/
def bvSizeOn {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  eLpNorm u 1 (volume.restrict Ω) + TauCeti.totalVariationOn volume Ω u

/-- Zero is BV on every open set, including unbounded sets. -/
theorem isBVFunctionOn_zero {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin d))) :
    IsBVFunctionOn Ω (fun _ ↦ 0) := by
  constructor
  · exact integrableOn_zero
  · simpa using (TauCeti.totalVariationOn_zero (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
      (Ω := Ω))

/-- **37.24**, whole-space BV compactness for uniformly bounded families supported in a fixed
compact set. The bounded-Lipschitz-domain extension interface is a separate target. -/
theorem bv_compactness_of_compact_support {d : ℕ}
    (u : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hu : ∀ n, IsBVFunctionOn ⊤ (u n)) (K : Set (EuclideanSpace ℝ (Fin d)))
    (hK : IsCompact K) (hs : ∀ n, ∀ᵐ x ∂volume, x ∉ K → u n x = 0)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hb : ∀ n, bvSizeOn ⊤ (u n) ≤ C) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ v : EuclideanSpace ℝ (Fin d) → ℝ,
      IsBVFunctionOn ⊤ v ∧ (∀ᵐ x ∂volume, x ∉ K → v x = 0) ∧
      Tendsto (fun n ↦ eLpNorm (fun x ↦ u (r n) x - v x) 1 volume) atTop (𝓝 0) ∧
      TauCeti.totalVariationOn volume ⊤ v ≤
        liminf (fun n ↦ TauCeti.totalVariationOn volume ⊤ (u (r n))) atTop := by
  sorry

/-- **37.30**: the full scalar BV coarea identity, retaining possibly infinite perimeters. -/
theorem bv_coarea {d : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin d)))
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hm : Measurable u) (hu : IsBVFunctionOn Ω u) :
    TauCeti.totalVariationOn volume Ω u =
      ∫⁻ t : ℝ, TauCeti.perimeter volume Ω {x | t < u x} := by
  sorry

end CKMA
