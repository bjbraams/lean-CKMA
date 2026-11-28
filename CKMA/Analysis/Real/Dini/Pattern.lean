/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Real.Dini.Basic

import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# The four Dini patterns are exclusive

If each opposite pair of Dini derivatives is either a common finite value or the infinite pair
`⊤` with `⊥`, then exactly one of the four Denjoy–Young–Saks alternatives holds. The comparison
of a lower derivative with the corresponding upper derivative is `liminf_le_limsup`.
Source: GAPS 05.10.

## Main results

* `CKMA.lowerRightDiniDerivative_le_upperRightDiniDerivative`,
  `CKMA.lowerLeftDiniDerivative_le_upperLeftDiniDerivative`: a lower Dini derivative is at most
  the upper one on the same side.
* `CKMA.Dini.existsUnique_diniType_of_patterns`: the two opposite-pair patterns determine a
  unique Dini type.
-/

public section

noncomputable section

namespace CKMA

open Filter Topology

/-- The lower right Dini derivative is at most the upper right Dini derivative. -/
lemma lowerRightDiniDerivative_le_upperRightDiniDerivative (f : ℝ → ℝ) (x : ℝ) :
    lowerRightDiniDerivative f x ≤ upperRightDiniDerivative f x :=
  liminf_le_limsup (h := isBoundedUnder_le_extendedDifferenceQuotient f x _)
    (h' := isBoundedUnder_ge_extendedDifferenceQuotient f x _)

/-- The lower left Dini derivative is at most the upper left Dini derivative. -/
lemma lowerLeftDiniDerivative_le_upperLeftDiniDerivative (f : ℝ → ℝ) (x : ℝ) :
    lowerLeftDiniDerivative f x ≤ upperLeftDiniDerivative f x :=
  liminf_le_limsup (h := isBoundedUnder_le_extendedDifferenceQuotient f x _)
    (h' := isBoundedUnder_ge_extendedDifferenceQuotient f x _)

namespace Dini

/-- An `EReal` value cannot simultaneously equal a finite real number and `⊤`. -/
private lemma coe_eq_top_false {a : ℝ} {z : EReal} (hz : z = a) (ht : z = ⊤) : False :=
  EReal.coe_ne_top a (hz.symm.trans ht)

/-- An `EReal` value cannot simultaneously equal a finite real number and `⊥`. -/
private lemma coe_eq_bot_false {a : ℝ} {z : EReal} (hz : z = a) (ht : z = ⊥) : False :=
  EReal.coe_ne_bot a (hz.symm.trans ht)

/-- The two opposite-pair patterns determine a unique Dini type. -/
theorem existsUnique_diniType_of_patterns (f : ℝ → ℝ) (x : ℝ)
    (h : (∃ a : ℝ, upperRightDiniDerivative f x = a ∧ lowerLeftDiniDerivative f x = a) ∨
      upperRightDiniDerivative f x = ⊤ ∧ lowerLeftDiniDerivative f x = ⊥)
    (h' : (∃ b : ℝ, lowerRightDiniDerivative f x = b ∧ upperLeftDiniDerivative f x = b) ∨
      upperLeftDiniDerivative f x = ⊤ ∧ lowerRightDiniDerivative f x = ⊥) :
    ∃! t : DiniType, HasDiniType f x t := by
  rcases h with ⟨a, haU, haL⟩ | ⟨haU, haL⟩
  · rcases h' with ⟨b, hbR, hbL⟩ | ⟨hbL, hbR⟩
    · have hba : (b : EReal) ≤ a := by
        rw [← hbR, ← haU]
        exact lowerRightDiniDerivative_le_upperRightDiniDerivative f x
      have hab : (a : EReal) ≤ b := by
        rw [← haL, ← hbL]
        exact lowerLeftDiniDerivative_le_upperLeftDiniDerivative f x
      obtain rfl : a = b :=
        le_antisymm (EReal.coe_le_coe_iff.1 hab) (EReal.coe_le_coe_iff.1 hba)
      refine ⟨.finite, ⟨a, haU, hbR, hbL, haL⟩, fun t ht => ?_⟩
      cases t with
      | finite => rfl
      | infinite => exact (coe_eq_top_false haU ht.1).elim
      | upperRightTop => exact (coe_eq_top_false haU ht.1).elim
      | upperLeftTop => exact (coe_eq_top_false hbL ht.1).elim
    · refine ⟨.upperLeftTop, ⟨hbL, hbR, a, haL, haU⟩, fun t ht => ?_⟩
      cases t with
      | finite => exact (coe_eq_top_false ht.choose_spec.2.2.1 hbL).elim
      | infinite => exact (coe_eq_top_false haU ht.1).elim
      | upperRightTop => exact (coe_eq_top_false haU ht.1).elim
      | upperLeftTop => rfl
  · rcases h' with ⟨b, hbR, hbL⟩ | ⟨hbL, hbR⟩
    · refine ⟨.upperRightTop, ⟨haU, haL, b, hbR, hbL⟩, fun t ht => ?_⟩
      cases t with
      | finite => exact (coe_eq_top_false ht.choose_spec.1 haU).elim
      | infinite => exact (coe_eq_bot_false hbR ht.2.2.1).elim
      | upperRightTop => rfl
      | upperLeftTop => exact (coe_eq_top_false hbL ht.1).elim
    · refine ⟨.infinite, ⟨haU, hbL, hbR, haL⟩, fun t ht => ?_⟩
      cases t with
      | finite => exact (coe_eq_top_false ht.choose_spec.1 haU).elim
      | infinite => rfl
      | upperRightTop => exact (coe_eq_bot_false ht.2.2.choose_spec.1 hbR).elim
      | upperLeftTop => exact (coe_eq_top_false ht.2.2.choose_spec.2 haU).elim

end Dini

end CKMA
