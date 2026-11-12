/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Real.Dini.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# Young's comparison of opposite Dini derivatives

The set where the upper right derivative lies strictly below the lower left derivative is
countable, and likewise with the two sides exchanged. Both sets are Lebesgue null. The
argument uses only the strict limsup and liminf inequalities, so the function is an arbitrary
map `ℝ → ℝ`. Source: GAPS 05.10.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Set Filter Topology MeasureTheory

/-- Points at which every right increment of length at most `1/(n + 1)` has slope `< p` and every
left increment of that length has slope `> p`. -/
def uniformCross (f : ℝ → ℝ) (p : ℚ) (n : ℕ) : Set ℝ :=
  {x | (∀ h, 0 < h → h ≤ (1 : ℝ) / (n + 1) → (f (x + h) - f x) / h < p) ∧
    (∀ h, -(1 : ℝ) / (n + 1) ≤ h → h < 0 → p < (f (x + h) - f x) / h)}

/-- A short negative increment is at least `-1 / (n + 1)` when the distance is at most that. -/
lemma neg_div_le_of_sub_le {n : ℕ} {d : ℝ} (hd : d ≤ (1 : ℝ) / (n + 1)) :
    -(1 : ℝ) / (n + 1) ≤ -d := by
  rw [neg_div ((n : ℝ) + 1) (1 : ℝ)]
  exact neg_le_neg hd

/-- A uniformly crossed set is separated by `1/(n + 1)`. -/
lemma uniformCross_separated (f : ℝ → ℝ) (p : ℚ) (n : ℕ) :
    (uniformCross f p n).Pairwise (fun x y => (1 : ℝ) / (n + 1) < |x - y|) := by
  intro x hx y hy hxy
  set δ : ℝ := (1 : ℝ) / (n + 1)
  have hδ : 0 < δ := by positivity
  by_contra hnear
  have hley : |y - x| ≤ δ := by
    rw [abs_sub_comm]
    exact le_of_not_gt hnear
  rcases lt_or_gt_of_ne hxy with hxy' | hyx
  · have hpos : 0 < y - x := sub_pos.2 hxy'
    have hlen : y - x ≤ δ := by
      rw [abs_of_pos hpos] at hley
      exact hley
    have hraw := hx.1 (y - x) hpos hlen
    have hadd : x + (y - x) = y := by
      rw [add_comm]
      exact sub_add_cancel y x
    rw [hadd] at hraw
    have hneg : x - y < 0 := by linarith
    have hbound : -(1 : ℝ) / (n + 1) ≤ x - y := by
      rw [← neg_sub y x]
      exact neg_div_le_of_sub_le hlen
    have hrawL := hy.2 (x - y) hbound hneg
    have haddL : y + (x - y) = x := by
      rw [add_comm]
      exact sub_add_cancel x y
    rw [haddL] at hrawL
    linarith [differenceQuotient_rev f x y]
  · have hpos : 0 < x - y := sub_pos.2 hyx
    have hlen : x - y ≤ δ := by
      have habs : |x - y| ≤ δ := by
        rw [abs_sub_comm] at hley
        exact hley
      rw [abs_of_pos hpos] at habs
      exact habs
    have hraw := hy.1 (x - y) hpos hlen
    have hadd : y + (x - y) = x := by
      rw [add_comm]
      exact sub_add_cancel x y
    rw [hadd] at hraw
    have hneg : y - x < 0 := by linarith
    have hbound : -(1 : ℝ) / (n + 1) ≤ y - x := by
      rw [← neg_sub x y]
      exact neg_div_le_of_sub_le hlen
    have hrawL := hx.2 (y - x) hbound hneg
    have haddL : x + (y - x) = y := by
      rw [add_comm]
      exact sub_add_cancel y x
    rw [haddL] at hrawL
    linarith [differenceQuotient_rev f y x]

/-- A separated subset of `ℝ` is countable. -/
lemma countable_of_separated {s : Set ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : s.Pairwise fun x y => δ < |x - y|) : s.Countable := by
  refine Set.PairwiseDisjoint.countable_of_Ioo (y := fun x => x + δ / 2)
    (fun x hx y hy hxy => ?_) (fun x _ => by linarith)
  refine disjoint_left.2 ?_
  intro z hz hz'
  rcases lt_or_gt_of_ne hxy with hxy' | hyx
  · have hlt : |x - y| < δ := by
      have hz1 : z < x + δ / 2 := hz.2
      have hz2 : y < z := hz'.1
      have : y - x < δ / 2 := by linarith
      have habs : |x - y| = y - x := by
        rw [abs_sub_comm]
        exact abs_of_pos (sub_pos.2 hxy')
      linarith
    exact (not_lt_of_gt (hsep hx hy hxy)) hlt
  · have hlt : |x - y| < δ := by
      have hz1 : z < y + δ / 2 := hz'.2
      have hz2 : x < z := hz.1
      have : x - y < δ / 2 := by linarith
      have habs : |x - y| = x - y := abs_of_pos (sub_pos.2 hyx)
      linarith
    exact (not_lt_of_gt (hsep hx hy hxy)) hlt

/-- Each uniformly crossed set is countable. -/
lemma uniformCross_countable (f : ℝ → ℝ) (p : ℚ) (n : ℕ) :
    (uniformCross f p n).Countable :=
  countable_of_separated (by positivity : (0 : ℝ) < 1 / (n + 1))
    (uniformCross_separated f p n)

/-- The extended difference quotient changes sign with `f`. -/
lemma extendedDifferenceQuotient_neg (f : ℝ → ℝ) (x h : ℝ) :
    extendedDifferenceQuotient (-f) x h = -extendedDifferenceQuotient f x h := by
  unfold extendedDifferenceQuotient
  rw [← EReal.coe_neg]
  congr 1
  simp only [Pi.neg_apply]
  ring

/-- Negation swaps the upper right and lower right Dini derivatives, up to sign. -/
lemma upperRightDiniDerivative_neg (f : ℝ → ℝ) (x : ℝ) :
    upperRightDiniDerivative (-f) x = -lowerRightDiniDerivative f x := by
  unfold upperRightDiniDerivative lowerRightDiniDerivative
  have hfun : extendedDifferenceQuotient (-f) x = -extendedDifferenceQuotient f x := by
    ext h
    exact extendedDifferenceQuotient_neg f x h
  rw [hfun, EReal.limsup_neg]

/-- Negation swaps the lower right and upper right Dini derivatives, up to sign. -/
lemma lowerRightDiniDerivative_neg (f : ℝ → ℝ) (x : ℝ) :
    lowerRightDiniDerivative (-f) x = -upperRightDiniDerivative f x := by
  unfold lowerRightDiniDerivative upperRightDiniDerivative
  have hfun : extendedDifferenceQuotient (-f) x = -extendedDifferenceQuotient f x := by
    ext h
    exact extendedDifferenceQuotient_neg f x h
  rw [hfun, EReal.liminf_neg]

/-- Negation swaps the upper left and lower left Dini derivatives, up to sign. -/
lemma upperLeftDiniDerivative_neg (f : ℝ → ℝ) (x : ℝ) :
    upperLeftDiniDerivative (-f) x = -lowerLeftDiniDerivative f x := by
  unfold upperLeftDiniDerivative lowerLeftDiniDerivative
  have hfun : extendedDifferenceQuotient (-f) x = -extendedDifferenceQuotient f x := by
    ext h
    exact extendedDifferenceQuotient_neg f x h
  rw [hfun, EReal.limsup_neg]

/-- Negation swaps the lower left and upper left Dini derivatives, up to sign. -/
lemma lowerLeftDiniDerivative_neg (f : ℝ → ℝ) (x : ℝ) :
    lowerLeftDiniDerivative (-f) x = -upperLeftDiniDerivative f x := by
  unfold lowerLeftDiniDerivative upperLeftDiniDerivative
  have hfun : extendedDifferenceQuotient (-f) x = -extendedDifferenceQuotient f x := by
    ext h
    exact extendedDifferenceQuotient_neg f x h
  rw [hfun, EReal.liminf_neg]

/-- The image of an extended quotient lies below every extended-real upper bound. -/
lemma diniQuotient_bddAbove (f : ℝ → ℝ) (x : ℝ) (l : Filter ℝ) :
    l.IsBoundedUnder (· ≤ ·) (extendedDifferenceQuotient f x) :=
  ⟨⊤, Eventually.of_forall fun _ => le_top⟩

/-- The image of an extended quotient lies above every extended-real lower bound. -/
lemma diniQuotient_bddBelow (f : ℝ → ℝ) (x : ℝ) (l : Filter ℝ) :
    l.IsBoundedUnder (· ≥ ·) (extendedDifferenceQuotient f x) :=
  ⟨⊥, Eventually.of_forall fun _ => bot_le⟩

/-- Where the upper right derivative is strictly below the lower left derivative, the set is
countable. -/
theorem countable_lt_upperRight_lowerLeft (f : ℝ → ℝ) :
    {x | upperRightDiniDerivative f x < lowerLeftDiniDerivative f x}.Countable := by
  refine Countable.mono ?_ (countable_iUnion fun p : ℚ =>
    countable_iUnion fun n : ℕ => uniformCross_countable f p n)
  intro x hx
  obtain ⟨ρ, hρU, hρL⟩ := EReal.exists_rat_btwn_of_lt hx
  have hR : ∀ᶠ h in 𝓝[>] (0 : ℝ), extendedDifferenceQuotient f x h < (ρ : ℝ) :=
    eventually_lt_of_limsup_lt hρU (diniQuotient_bddAbove f x _)
  have hL : ∀ᶠ h in 𝓝[<] (0 : ℝ), (ρ : ℝ) < extendedDifferenceQuotient f x h :=
    eventually_lt_of_lt_liminf hρL (diniQuotient_bddBelow f x _)
  rw [eventually_iff] at hR hL
  obtain ⟨εR, hεR, hsubR⟩ := (mem_nhdsGT_iff_exists_Ioo_subset (a := (0 : ℝ))).1 hR
  obtain ⟨εL, hεL, hsubL⟩ := (mem_nhdsLT_iff_exists_Ioo_subset (a := (0 : ℝ))).1 hL
  have hεRpos : 0 < εR := hεR
  have hεLneg : εL < 0 := hεL
  have hmin : 0 < min εR (-εL) := lt_min hεRpos (neg_pos.2 hεLneg)
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / min εR (-εL))
  have hn0 : 0 < (n : ℝ) := by
    have : 0 < 1 / min εR (-εL) := one_div_pos.2 hmin
    exact this.trans hn
  have hδ : (1 : ℝ) / (n + 1) < min εR (-εL) := by
    have hstep : (1 : ℝ) / (n + 1) < 1 / n := by
      rw [one_div_lt_one_div (by linarith : (0 : ℝ) < (n : ℝ) + 1) hn0]
      linarith
    exact hstep.trans ((one_div_lt hmin hn0).1 hn)
  refine mem_iUnion.2 ⟨ρ, mem_iUnion.2 ⟨n, ?_⟩⟩
  refine ⟨?_, ?_⟩
  · intro h hh0 hhδ
    have hmem : h ∈ Ioo (0 : ℝ) εR :=
      ⟨hh0, lt_of_le_of_lt hhδ (hδ.trans_le (min_le_left _ _))⟩
    have hquot : extendedDifferenceQuotient f x h < (ρ : ℝ) := hsubR hmem
    unfold extendedDifferenceQuotient at hquot
    rw [EReal.coe_lt_coe_iff] at hquot
    exact hquot
  · intro h hhδ hh0
    have hδL : (1 : ℝ) / (n + 1) < -εL := hδ.trans_le (min_le_right _ _)
    have hge : εL < h := by
      have hε : εL < -((1 : ℝ) / (n + 1)) := by
        simpa using neg_lt_neg hδL
      have hlow : -((1 : ℝ) / (n + 1)) ≤ h := by
        rw [neg_div ((n : ℝ) + 1) (1 : ℝ)] at hhδ
        exact hhδ
      exact lt_of_lt_of_le hε hlow
    have hmem : h ∈ Ioo εL 0 := ⟨hge, hh0⟩
    have hquot : (ρ : ℝ) < extendedDifferenceQuotient f x h := hsubL hmem
    unfold extendedDifferenceQuotient at hquot
    rw [EReal.coe_lt_coe_iff] at hquot
    exact hquot

/-- Exchanging the two sides is negation of the function. -/
theorem countable_lt_upperLeft_lowerRight (f : ℝ → ℝ) :
    {x | upperLeftDiniDerivative f x < lowerRightDiniDerivative f x}.Countable :=
  (countable_lt_upperRight_lowerLeft (-f)).mono fun x hx => by
    change upperRightDiniDerivative (-f) x < lowerLeftDiniDerivative (-f) x
    rw [upperRightDiniDerivative_neg, lowerLeftDiniDerivative_neg]
    exact EReal.neg_lt_neg_iff.2 hx

/-- The strict inequality between the upper right and lower left derivatives is null. -/
theorem volume_lt_upperRight_lowerLeft (f : ℝ → ℝ) :
    volume {x | upperRightDiniDerivative f x < lowerLeftDiniDerivative f x} = 0 :=
  (countable_lt_upperRight_lowerLeft f).measure_zero volume

/-- The strict inequality between the upper left and lower right derivatives is null. -/
theorem volume_lt_upperLeft_lowerRight (f : ℝ → ℝ) :
    volume {x | upperLeftDiniDerivative f x < lowerRightDiniDerivative f x} = 0 :=
  (countable_lt_upperLeft_lowerRight f).measure_zero volume

end CKMA
