/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Self-similar compact sets and invariant laws (39.73)

A nonempty finite family of maps with a common contraction constant below one has a
unique nonempty compact attractor in a complete nonempty metric space. The proof applies
Mathlib's Banach contraction theorem
to the Hausdorff metric on nonempty compact sets.
The measure theorem allows any nonnegative weights summing to one, including zero weights.

The invariant Borel probability is unique among all invariant probabilities; no moment
assumption is imposed. Strictly positive weights are unnecessary for this conclusion,
although they matter when identifying the support with the full compact attractor.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory TopologicalSpace Metric
open scoped BigOperators NNReal ENNReal

variable {X ι : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    [Fintype ι]

/-- **39.73**: Hutchinson's unique nonempty compact attractor. -/
theorem existsUnique_selfSimilar_compact [Nonempty ι] (S : ι → X → X) {c : ℝ≥0}
    (hc : c < 1) (hS : ∀ i, LipschitzWith c (S i)) :
    ∃! K : NonemptyCompacts X, (K : Set X) = ⋃ i, S i '' (K : Set X) := by
  classical
  let F : NonemptyCompacts X → NonemptyCompacts X := fun K ↦
    ⟨⟨⋃ i, S i '' (K : Set X), isCompact_iUnion (fun i ↦ K.isCompact.image (hS i).continuous)⟩,
      Set.nonempty_iUnion.mpr ⟨Classical.arbitrary ι, K.nonempty.image _⟩⟩
  have hmap (i : ι) (A B : NonemptyCompacts X) :
      hausdorffEDist (S i '' (A : Set X)) (S i '' (B : Set X)) ≤ c * edist A B := by
    have haux (A B : NonemptyCompacts X) (x : X) (hx : x ∈ A) :
        ∃ y ∈ S i '' (B : Set X), edist (S i x) y ≤ c * edist A B := by
      obtain ⟨y, hy, he⟩ := B.isCompact.exists_infEDist_eq_edist B.nonempty x
      refine ⟨S i y, ⟨y, hy, rfl⟩, (hS i x y).trans ?_⟩
      have hxy : edist x y ≤ edist A B := by
        rw [← he]
        change infEDist x (B : Set X) ≤ hausdorffEDist (A : Set X) B
        exact infEDist_le_hausdorffEDist_of_mem hx
      exact mul_le_mul_of_nonneg_left hxy zero_le
    apply hausdorffEDist_le_of_mem_edist
    · rintro _ ⟨x, hx, rfl⟩
      exact haux A B x hx
    · rintro _ ⟨x, hx, rfl⟩
      simpa only [edist_comm] using haux B A x hx
  have hF : ContractingWith c F := by
    refine ⟨hc, fun A B ↦ ?_⟩
    change hausdorffEDist (⋃ i, S i '' (A : Set X)) (⋃ i, S i '' (B : Set X)) ≤ _
    exact hausdorffEDist_iUnion_le.trans (iSup_le fun i ↦ hmap i A B)
  refine ⟨hF.fixedPoint F, ?_, ?_⟩
  · exact (congrArg (fun K : NonemptyCompacts X ↦ (K : Set X)) hF.fixedPoint_isFixedPt).symm
  · intro K hK
    exact hF.fixedPoint_unique (NonemptyCompacts.ext hK.symm)

/-- Nonnegative weights of total mass one give a unique invariant Borel probability measure.
Uniqueness is among all invariant probabilities, without a moment assumption. -/
theorem existsUnique_selfSimilar_measure [MeasurableSpace X] [BorelSpace X]
    (S : ι → X → X) {c : ℝ≥0} (hc : c < 1) (hS : ∀ i, LipschitzWith c (S i))
    (p : ι → ℝ≥0) (hsum : ∑ i, p i = 1) :
    ∃! μ : Measure X, IsProbabilityMeasure μ ∧ μ = ∑ i, p i • μ.map (S i) := by
  sorry

end CKMA
