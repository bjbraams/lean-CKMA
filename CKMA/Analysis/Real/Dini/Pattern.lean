/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Real.Dini.Basic

/-!
# The four Dini patterns are exclusive

If each opposite pair of Dini derivatives is either a common finite value or the infinite pair
`⊤` with `⊥`, then exactly one of the four Denjoy–Young–Saks alternatives holds. The comparison
of a lower derivative with the corresponding upper derivative is `liminf_le_limsup`.
Source: GAPS 05.10.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology

/-- The extended quotient is bounded above. -/
private lemma diniQuotient_bddAbove (f : ℝ → ℝ) (x : ℝ) (l : Filter ℝ) :
    l.IsBoundedUnder (· ≤ ·) (extendedDifferenceQuotient f x) :=
  ⟨⊤, Eventually.of_forall fun _ => le_top⟩

/-- The extended quotient is bounded below. -/
private lemma diniQuotient_bddBelow (f : ℝ → ℝ) (x : ℝ) (l : Filter ℝ) :
    l.IsBoundedUnder (· ≥ ·) (extendedDifferenceQuotient f x) :=
  ⟨⊥, Eventually.of_forall fun _ => bot_le⟩

private lemma right_le (f : ℝ → ℝ) (x : ℝ) :
    lowerRightDiniDerivative f x ≤ upperRightDiniDerivative f x :=
  liminf_le_limsup (h := diniQuotient_bddAbove f x _) (h' := diniQuotient_bddBelow f x _)

private lemma left_le (f : ℝ → ℝ) (x : ℝ) :
    lowerLeftDiniDerivative f x ≤ upperLeftDiniDerivative f x :=
  liminf_le_limsup (h := diniQuotient_bddAbove f x _) (h' := diniQuotient_bddBelow f x _)

/-- Finite equal right and left derivatives give the first alternative. -/
lemma hasDiniType_zero {f : ℝ → ℝ} {x a : ℝ}
    (hUR : upperRightDiniDerivative f x = a) (hLR : lowerRightDiniDerivative f x = a)
    (hUL : upperLeftDiniDerivative f x = a) (hLL : lowerLeftDiniDerivative f x = a) :
    HasDiniType f x 0 := by
  unfold HasDiniType
  simp
  exact ⟨a, hUR, hLR, hUL, hLL⟩

/-- Both upper derivatives `⊤` and both lower derivatives `⊥` give the second alternative. -/
lemma hasDiniType_one {f : ℝ → ℝ} {x : ℝ}
    (hUR : upperRightDiniDerivative f x = ⊤) (hUL : upperLeftDiniDerivative f x = ⊤)
    (hLR : lowerRightDiniDerivative f x = ⊥) (hLL : lowerLeftDiniDerivative f x = ⊥) :
    HasDiniType f x 1 := by
  unfold HasDiniType
  simp
  exact ⟨hUR, hUL, hLR, hLL⟩

/-- The mixed pattern with upper right `⊤` and lower left `⊥` is the third alternative. -/
lemma hasDiniType_two {f : ℝ → ℝ} {x a : ℝ}
    (hUR : upperRightDiniDerivative f x = ⊤) (hLL : lowerLeftDiniDerivative f x = ⊥)
    (hLR : lowerRightDiniDerivative f x = a) (hUL : upperLeftDiniDerivative f x = a) :
    HasDiniType f x 2 := by
  unfold HasDiniType
  simp
  exact ⟨hUR, hLL, a, hLR, hUL⟩

/-- The mixed pattern with upper left `⊤` and lower right `⊥` is the fourth alternative. -/
lemma hasDiniType_three {f : ℝ → ℝ} {x a : ℝ}
    (hUL : upperLeftDiniDerivative f x = ⊤) (hLR : lowerRightDiniDerivative f x = ⊥)
    (hLL : lowerLeftDiniDerivative f x = a) (hUR : upperRightDiniDerivative f x = a) :
    HasDiniType f x 3 := by
  unfold HasDiniType
  simp
  exact ⟨hUL, hLR, a, hLL, hUR⟩

private lemma ne_zero_of_top {a : ℝ} {z : EReal} (hz : z = a) (ht : z = ⊤) : False :=
  EReal.coe_ne_top a (hz.symm.trans ht)

private lemma ne_zero_of_bot {a : ℝ} {z : EReal} (hz : z = a) (ht : z = ⊥) : False :=
  EReal.coe_ne_bot a (hz.symm.trans ht)

/-- The two opposite-pair patterns determine a unique Dini type. -/
theorem existsUnique_diniType_of_patterns (f : ℝ → ℝ) (x : ℝ)
    (h : (∃ a : ℝ, upperRightDiniDerivative f x = a ∧ lowerLeftDiniDerivative f x = a) ∨
      upperRightDiniDerivative f x = ⊤ ∧ lowerLeftDiniDerivative f x = ⊥)
    (h' : (∃ b : ℝ, lowerRightDiniDerivative f x = b ∧ upperLeftDiniDerivative f x = b) ∨
      upperLeftDiniDerivative f x = ⊤ ∧ lowerRightDiniDerivative f x = ⊥) :
    ∃! i : Fin 4, HasDiniType f x i := by
  rcases h with ⟨a, haU, haL⟩ | ⟨haU, haL⟩
  · rcases h' with ⟨b, hbR, hbL⟩ | ⟨hbL, hbR⟩
    · have hba : (b : EReal) ≤ a := by
        rw [← hbR, ← haU]
        exact right_le f x
      have hab : (a : EReal) ≤ b := by
        rw [← haL, ← hbL]
        exact left_le f x
      have heq : a = b :=
        le_antisymm (EReal.coe_le_coe_iff.1 hab) (EReal.coe_le_coe_iff.1 hba)
      refine ⟨0, hasDiniType_zero haU (heq ▸ hbR) (heq ▸ hbL) haL, ?_⟩
      intro j hj
      fin_cases j
      · rfl
      · unfold HasDiniType at hj
        simp at hj
        exact False.elim (ne_zero_of_top haU hj.1)
      · unfold HasDiniType at hj
        simp at hj
        exact False.elim (ne_zero_of_top haU hj.1)
      · unfold HasDiniType at hj
        simp at hj
        exact False.elim (ne_zero_of_top (heq ▸ hbL) hj.1)
    · refine ⟨3, hasDiniType_three hbL hbR haL haU, ?_⟩
      intro j hj
      fin_cases j
      · unfold HasDiniType at hj
        simp at hj
        rcases hj with ⟨c, -, -, hcL, -⟩
        exact False.elim (ne_zero_of_top hcL hbL)
      · unfold HasDiniType at hj
        simp at hj
        exact False.elim (ne_zero_of_top haU hj.1)
      · unfold HasDiniType at hj
        simp at hj
        exact False.elim (ne_zero_of_top haU hj.1)
      · rfl
  · rcases h' with ⟨b, hbR, hbL⟩ | ⟨hbL, hbR⟩
    · refine ⟨2, hasDiniType_two haU haL hbR hbL, ?_⟩
      intro j hj
      fin_cases j
      · unfold HasDiniType at hj
        simp at hj
        rcases hj with ⟨c, hcU, -, -, -⟩
        exact False.elim (ne_zero_of_top hcU haU)
      · unfold HasDiniType at hj
        simp at hj
        exact False.elim (ne_zero_of_bot hbR hj.2.2.1)
      · rfl
      · unfold HasDiniType at hj
        simp at hj
        exact False.elim (ne_zero_of_top hbL hj.1)
    · refine ⟨1, hasDiniType_one haU hbL hbR haL, ?_⟩
      intro j hj
      fin_cases j
      · unfold HasDiniType at hj
        simp at hj
        rcases hj with ⟨c, hcU, -, -, -⟩
        exact False.elim (ne_zero_of_top hcU haU)
      · rfl
      · unfold HasDiniType at hj
        simp at hj
        rcases hj with ⟨-, -, c, hc, -⟩
        exact False.elim (ne_zero_of_bot hc hbR)
      · unfold HasDiniType at hj
        simp at hj
        rcases hj with ⟨-, -, c, -, hc⟩
        exact False.elim (ne_zero_of_top hc haU)

end CKMA
