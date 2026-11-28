/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Real.Dini.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

import CKMA.Analysis.Real.Dini.FiniteGap
import CKMA.Analysis.Real.Dini.Infinite
import CKMA.Analysis.Real.Dini.Young

/-!
# Assembly of the Denjoy–Young–Saks alternatives

Young's strict comparisons, the two infinite mismatches, and the finite gap are null. Outside
that null set each opposite pair of Dini derivatives is either a common finite value or the pair
`⊤` with `⊥`. The four combinations are exactly the four `HasDiniType` alternatives, and the
comparisons `lower ≤ upper` make the choice unique; the resulting theorem is
`CKMA.ae_existsUnique_diniType`. Source: GAPS 05.10.

## Main results

* `CKMA.Dini.ae_oppositePair`: almost every point has matching or opposite-infinite upper-right
  and lower-left Dini derivatives.
* `CKMA.Dini.opposite_of_neg`: the opposite-pair pattern of `-f` gives the lower-right and
  upper-left pattern of `f`.
-/

public section

noncomputable section

namespace CKMA.Dini

open Set Filter Topology MeasureTheory

/-- The null set of points that fail an opposite-pair Dini pattern. -/
private def exceptional (f : ℝ → ℝ) : Set ℝ :=
  {x | upperRightDiniDerivative f x < lowerLeftDiniDerivative f x} ∪
    ({x | upperLeftDiniDerivative f x < lowerRightDiniDerivative f x} ∪
      (infiniteUp f ∪ (infiniteDown f ∪ finiteStrict f)))

/-- The exceptional set is a union of five null sets. -/
private theorem volume_exceptional (f : ℝ → ℝ) : volume (exceptional f) = 0 :=
  measure_union_null (volume_lt_upperRight_lowerLeft f) <|
    measure_union_null (volume_lt_upperLeft_lowerRight f) <|
      measure_union_null (volume_infiniteUp f) <|
        measure_union_null (volume_infiniteDown f) (volume_finiteStrict f)

/-- Almost every point has matching upper-right and lower-left Dini derivatives. -/
theorem ae_oppositePair (f : ℝ → ℝ) :
    ∀ᵐ x ∂volume,
      (∃ a : ℝ, upperRightDiniDerivative f x = a ∧ lowerLeftDiniDerivative f x = a) ∨
        upperRightDiniDerivative f x = ⊤ ∧ lowerLeftDiniDerivative f x = ⊥ := by
  refine ((measure_eq_zero_iff_ae_notMem).1 (volume_exceptional f)).mono fun x hx => ?_
  simp only [exceptional, mem_union, mem_ofPred_eq, not_or] at hx
  obtain ⟨hYL, -, hUp, hDown, hFin⟩ := hx
  have hle : lowerLeftDiniDerivative f x ≤ upperRightDiniDerivative f x := le_of_not_gt hYL
  by_cases htop : upperRightDiniDerivative f x = ⊤
  · have hbot : lowerLeftDiniDerivative f x = ⊥ := by
      by_contra hne
      exact hUp ⟨htop, hne⟩
    exact Or.inr ⟨htop, hbot⟩
  · have hbot : lowerLeftDiniDerivative f x ≠ ⊥ := by
      intro h
      exact hDown ⟨h, htop⟩
    have hURbot : upperRightDiniDerivative f x ≠ ⊥ := by
      intro h
      have : lowerLeftDiniDerivative f x ≤ ⊥ := by simpa [h] using hle
      exact hbot (le_bot_iff.mp this)
    have hLLtop : lowerLeftDiniDerivative f x ≠ ⊤ := by
      intro h
      have : ⊤ ≤ upperRightDiniDerivative f x := by simpa [h] using hle
      exact htop (top_le_iff.mp this)
    have hcoeU := EReal.coe_toReal htop hURbot
    have hlt : ¬ lowerLeftDiniDerivative f x < upperRightDiniDerivative f x := by
      intro h
      exact hFin (mem_finiteStrict_of_lt htop hURbot hLLtop hbot h)
    have heq : lowerLeftDiniDerivative f x = upperRightDiniDerivative f x :=
      le_antisymm hle (le_of_not_gt hlt)
    refine Or.inl ⟨(upperRightDiniDerivative f x).toReal, hcoeU.symm, ?_⟩
    rw [heq]
    exact hcoeU.symm

/-- Negation turns the upper-right pattern into the lower-right pattern. -/
lemma opposite_of_neg (f : ℝ → ℝ) {x : ℝ}
    (h : (∃ a : ℝ, upperRightDiniDerivative (-f) x = a ∧
        lowerLeftDiniDerivative (-f) x = a) ∨
      upperRightDiniDerivative (-f) x = ⊤ ∧ lowerLeftDiniDerivative (-f) x = ⊥) :
    (∃ b : ℝ, lowerRightDiniDerivative f x = b ∧ upperLeftDiniDerivative f x = b) ∨
      upperLeftDiniDerivative f x = ⊤ ∧ lowerRightDiniDerivative f x = ⊥ := by
  rw [upperRightDiniDerivative_neg, lowerLeftDiniDerivative_neg] at h
  rcases h with ⟨a, haR, haL⟩ | ⟨haR, haL⟩
  · refine Or.inl ⟨-a, ?_, ?_⟩
    · have hneg := congrArg Neg.neg haR
      rw [neg_neg, ← EReal.coe_neg] at hneg
      exact hneg
    · have hneg := congrArg Neg.neg haL
      rw [neg_neg, ← EReal.coe_neg] at hneg
      exact hneg
  · exact Or.inr ⟨EReal.neg_eq_bot_iff.mp haL, EReal.neg_eq_top_iff.mp haR⟩

end CKMA.Dini
