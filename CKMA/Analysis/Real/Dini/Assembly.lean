/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Real.Dini.FiniteGap
public import CKMA.Analysis.Real.Dini.Pattern

/-!
# Assembly of the Denjoy–Young–Saks alternatives

Young's strict comparisons, the two infinite mismatches, and the finite gap are null. Outside
that null set each opposite pair of Dini derivatives is either a common finite value or the pair
`⊤` with `⊥`. The four combinations are exactly the four `HasDiniType` alternatives, and the
comparisons `lower ≤ upper` make the choice unique. Source: GAPS 05.10.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Set Filter Topology MeasureTheory

/-- The null set of points that fail an opposite-pair Dini pattern. -/
def exceptional (f : ℝ → ℝ) : Set ℝ :=
  {x | upperRightDiniDerivative f x < lowerLeftDiniDerivative f x} ∪
    ({x | upperLeftDiniDerivative f x < lowerRightDiniDerivative f x} ∪
      (infiniteUp f ∪ (infiniteDown f ∪ finiteStrict f)))

/-- The exceptional set is a union of five null sets. -/
theorem volume_exceptional (f : ℝ → ℝ) : volume (exceptional f) = 0 := by
  have h1 := volume_lt_upperRight_lowerLeft f
  have h2 := volume_lt_upperLeft_lowerRight f
  have h3 := volume_infiniteUp f
  have h4 := volume_infiniteDown f
  have h5 := volume_finiteStrict f
  refine le_antisymm ?_ bot_le
  calc volume (exceptional f)
      ≤ volume {x | upperRightDiniDerivative f x < lowerLeftDiniDerivative f x} +
          volume ({x | upperLeftDiniDerivative f x < lowerRightDiniDerivative f x} ∪
            (infiniteUp f ∪ (infiniteDown f ∪ finiteStrict f))) :=
        measure_union_le _ _
    _ ≤ volume {x | upperRightDiniDerivative f x < lowerLeftDiniDerivative f x} +
          (volume {x | upperLeftDiniDerivative f x < lowerRightDiniDerivative f x} +
            volume (infiniteUp f ∪ (infiniteDown f ∪ finiteStrict f))) :=
        add_le_add_right (measure_union_le _ _) _
    _ ≤ volume {x | upperRightDiniDerivative f x < lowerLeftDiniDerivative f x} +
          (volume {x | upperLeftDiniDerivative f x < lowerRightDiniDerivative f x} +
            (volume (infiniteUp f) + volume (infiniteDown f ∪ finiteStrict f))) :=
        add_le_add_right (add_le_add_right (measure_union_le _ _) _) _
    _ ≤ volume {x | upperRightDiniDerivative f x < lowerLeftDiniDerivative f x} +
          (volume {x | upperLeftDiniDerivative f x < lowerRightDiniDerivative f x} +
            (volume (infiniteUp f) + (volume (infiniteDown f) + volume (finiteStrict f)))) :=
        add_le_add_right (add_le_add_right (add_le_add_right (measure_union_le _ _) _) _) _
    _ = 0 := by simp [h1, h2, h3, h4, h5]

/-- Almost every point has matching upper-right and lower-left Dini derivatives. -/
theorem ae_oppositePair (f : ℝ → ℝ) :
    ∀ᵐ x ∂volume,
      (∃ a : ℝ, upperRightDiniDerivative f x = a ∧ lowerLeftDiniDerivative f x = a) ∨
        upperRightDiniDerivative f x = ⊤ ∧ lowerLeftDiniDerivative f x = ⊥ := by
  refine ((measure_eq_zero_iff_ae_notMem).1 (volume_exceptional f)).mono fun x hx => ?_
  have hYL : ¬ upperRightDiniDerivative f x < lowerLeftDiniDerivative f x := by
    intro h
    exact hx (Or.inl h)
  have hx1 : x ∉ {x | upperLeftDiniDerivative f x < lowerRightDiniDerivative f x} ∪
      (infiniteUp f ∪ (infiniteDown f ∪ finiteStrict f)) := by
    intro h
    exact hx (Or.inr h)
  have hYR : ¬ upperLeftDiniDerivative f x < lowerRightDiniDerivative f x := by
    intro h
    exact hx1 (Or.inl h)
  have hx2 : x ∉ infiniteUp f ∪ (infiniteDown f ∪ finiteStrict f) := by
    intro h
    exact hx1 (Or.inr h)
  have hUp : x ∉ infiniteUp f := by
    intro h
    exact hx2 (Or.inl h)
  have hx3 : x ∉ infiniteDown f ∪ finiteStrict f := by
    intro h
    exact hx2 (Or.inr h)
  have hDown : x ∉ infiniteDown f := by
    intro h
    exact hx3 (Or.inl h)
  have hFin : x ∉ finiteStrict f := by
    intro h
    exact hx3 (Or.inr h)
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
    have hcoeL := EReal.coe_toReal hLLtop hbot
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

/-- Almost every point realises exactly one Denjoy–Young–Saks alternative. -/
theorem ae_diniType (f : ℝ → ℝ) :
    ∀ᵐ x ∂volume, ∃! i : Fin 4, HasDiniType f x i := by
  filter_upwards [ae_oppositePair f, ae_oppositePair (-f)] with x hx hx'
  exact existsUnique_diniType_of_patterns f x hx (opposite_of_neg f hx')

end CKMA
