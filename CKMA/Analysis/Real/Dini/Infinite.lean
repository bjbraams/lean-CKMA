/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Real.Dini.Covering
public import CKMA.Analysis.Real.Dini.Young
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Tactic

/-!
# Infinite Dini mismatches are null

For an arbitrary `f : ℝ → ℝ`, the set where the upper right derivative is `⊤` while the lower
left derivative is not `⊥` is a countable union of sets controlled by
`volume_eq_zero_of_arbitrarily_steep`. Reflection `x ↦ f (-x)` carries the opposite mismatch
to the same statement. Source: GAPS 05.10.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Set Filter Topology MeasureTheory
open scoped ENNReal

/-- Negation sends right punctured neighbourhoods of `0` to left ones. -/
lemma map_neg_nhdsGT_zero :
    map (fun x : ℝ => -x) (𝓝[>] (0 : ℝ)) = 𝓝[<] (0 : ℝ) := by
  refine le_antisymm ?_ ?_
  · rw [map_le_iff_le_comap]
    intro s hs
    rw [mem_comap] at hs
    obtain ⟨t, ht, htsub⟩ := hs
    rw [mem_nhdsLT_iff_exists_Ioo_subset] at ht
    obtain ⟨ε, hε, hsub⟩ := ht
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    refine ⟨-ε, neg_pos.2 hε, ?_⟩
    intro x hx
    exact htsub (hsub ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  · have hle : map (fun x : ℝ => -x) (𝓝[<] (0 : ℝ)) ≤ 𝓝[>] (0 : ℝ) := by
      rw [map_le_iff_le_comap]
      intro s hs
      rw [mem_comap] at hs
      obtain ⟨t, ht, htsub⟩ := hs
      rw [mem_nhdsGT_iff_exists_Ioo_subset] at ht
      obtain ⟨ε, hε, hsub⟩ := ht
      rw [mem_nhdsLT_iff_exists_Ioo_subset]
      refine ⟨-ε, neg_lt_zero.2 hε, ?_⟩
      intro x hx
      exact htsub (hsub ⟨by linarith [hx.2], by linarith [hx.1]⟩)
    have hid : (fun x : ℝ => -x) ∘ (fun x : ℝ => -x) = id := by
      ext x
      simp
    calc 𝓝[<] (0 : ℝ)
        = map (fun x : ℝ => -x) (map (fun x : ℝ => -x) (𝓝[<] 0)) := by
          rw [map_map, hid, map_id]
      _ ≤ map (fun x : ℝ => -x) (𝓝[>] 0) := map_mono hle

/-- Negation sends left punctured neighbourhoods of `0` to right ones. -/
lemma map_neg_nhdsLT_zero :
    map (fun x : ℝ => -x) (𝓝[<] (0 : ℝ)) = 𝓝[>] (0 : ℝ) := by
  have h := congrArg (map (fun x : ℝ => -x)) map_neg_nhdsGT_zero
  have hid : (fun x : ℝ => -x) ∘ (fun x : ℝ => -x) = id := by
    ext x
    simp
  rw [map_map, hid, map_id] at h
  exact h.symm

/-- Difference quotients of `f (-·)` are signed reflected quotients of `f`. -/
lemma extendedDifferenceQuotient_comp_neg (f : ℝ → ℝ) (x h : ℝ) :
    extendedDifferenceQuotient (fun t => f (-t)) x h =
      -extendedDifferenceQuotient f (-x) (-h) := by
  unfold extendedDifferenceQuotient
  dsimp
  rw [show -(x + h) = -x + -h by ring, ← EReal.coe_neg]
  congr 1
  rw [div_neg, neg_neg]

/-- Reflection swaps the upper right derivative with the signed lower left derivative. -/
lemma upperRightDiniDerivative_comp_neg (f : ℝ → ℝ) (x : ℝ) :
    upperRightDiniDerivative (fun t => f (-t)) x =
      -lowerLeftDiniDerivative f (-x) := by
  unfold upperRightDiniDerivative lowerLeftDiniDerivative
  have hfun : extendedDifferenceQuotient (fun t => f (-t)) x =
      fun h => -extendedDifferenceQuotient f (-x) (-h) := by
    ext h
    exact extendedDifferenceQuotient_comp_neg f x h
  rw [hfun]
  set q := extendedDifferenceQuotient f (-x)
  have hcomp : (fun h => -q (-h)) = (-q) ∘ Neg.neg := by
    ext h
    simp
  rw [hcomp, limsup_comp, map_neg_nhdsGT_zero]
  exact EReal.limsup_neg

/-- Reflection swaps the lower left derivative with the signed upper right derivative. -/
lemma lowerLeftDiniDerivative_comp_neg (f : ℝ → ℝ) (x : ℝ) :
    lowerLeftDiniDerivative (fun t => f (-t)) x =
      -upperRightDiniDerivative f (-x) := by
  unfold lowerLeftDiniDerivative upperRightDiniDerivative
  have hfun : extendedDifferenceQuotient (fun t => f (-t)) x =
      fun h => -extendedDifferenceQuotient f (-x) (-h) := by
    ext h
    exact extendedDifferenceQuotient_comp_neg f x h
  rw [hfun]
  set q := extendedDifferenceQuotient f (-x)
  have hcomp : (fun h => -q (-h)) = (-q) ∘ Neg.neg := by
    ext h
    simp
  rw [hcomp, liminf_comp, map_neg_nhdsLT_zero]
  exact EReal.liminf_neg

/-- A right increment steeper than `k` exists at every positive scale above the limsup. -/
lemma exists_right_slope_gt (f : ℝ → ℝ) (x k ε : ℝ)
    (hk : (k : EReal) < upperRightDiniDerivative f x) (hε : 0 < ε) :
    ∃ h, 0 < h ∧ h < ε ∧ k < (f (x + h) - f x) / h := by
  have hfreq : ∃ᶠ h in 𝓝[>] (0 : ℝ), (k : EReal) < extendedDifferenceQuotient f x h :=
    frequently_lt_of_lt_limsup (hu := isCobounded_le_of_bot) hk
  have hmem : Ioo (0 : ℝ) ε ∈ 𝓝[>] 0 := by
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    exact ⟨ε, hε, subset_rfl⟩
  have hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h ∧ h < ε :=
    eventually_of_mem hmem fun h hh => ⟨hh.1, hh.2⟩
  obtain ⟨h, hhE, hh⟩ := (hfreq.and_eventually hsmall).exists
  refine ⟨h, hh.1, hh.2, ?_⟩
  unfold extendedDifferenceQuotient at hhE
  exact (EReal.coe_lt_coe_iff).1 hhE

/-- Upper right derivative `⊤`, with left slopes of length `1/(n + 1)` above `q`. -/
def leftSteep (f : ℝ → ℝ) (q : ℚ) (n : ℕ) : Set ℝ :=
  {x | upperRightDiniDerivative f x = ⊤ ∧
    ∀ h, -(1 : ℝ) / (n + 1) ≤ h → h < 0 → (q : ℝ) < (f (x + h) - f x) / h}

/-- On a short interval ending in `leftSteep`, the outer measure of that set vanishes. -/
lemma volume_leftSteep_Ioo (f : ℝ → ℝ) (q : ℚ) (n : ℕ) {a b : ℝ}
    (hab : a < b) (hlen : b - a < (1 : ℝ) / (n + 1)) (hb : b ∈ leftSteep f q n) :
    volume (leftSteep f q n ∩ Ioo a b) = 0 := by
  refine volume_eq_zero_of_arbitrarily_steep (c := (q : ℝ)) (δ := (1 : ℝ) / (n + 1))
    f (leftSteep f q n) hab hlen hb ?_ ?_
  · intro x hx u hu hux
    have hlt : u - x < 0 := by linarith
    have hge : -(1 : ℝ) / (n + 1) ≤ u - x := by
      have hstrict : x - (1 : ℝ) / (n + 1) < u := hu
      have hsub : -((1 : ℝ) / (n + 1)) < u - x := by linarith
      rw [← neg_div ((n : ℝ) + 1) (1 : ℝ)] at hsub
      exact hsub.le
    have hs := hx.2 (u - x) hge hlt
    have hadd : x + (u - x) = u := by
      rw [add_comm]
      exact sub_add_cancel u x
    rw [hadd] at hs
    rw [differenceQuotient_rev f x u]
    exact hs
  · intro k hk x hx ε hε
    have hxlt : x < b := hx.2.2
    have htop : (k : EReal) < upperRightDiniDerivative f x := by
      rw [hx.1.1]
      exact EReal.coe_lt_top k
    have hε' : 0 < min ε (b - x) := lt_min hε (sub_pos.2 hxlt)
    obtain ⟨h, hh0, hhε, hhs⟩ :=
      exists_right_slope_gt f x k (min ε (b - x)) htop hε'
    have hh : x + h - x = h := by ring
    refine ⟨x + h, by linarith, ?_, ?_, ?_⟩
    · have : h < b - x := lt_of_lt_of_le hhε (min_le_right _ _)
      linarith
    · rw [hh]
      exact lt_of_lt_of_le hhε (min_le_left _ _)
    · rw [hh]
      exact hhs

/-- If every subinterval ending in `E` is null, then `E` is null on `(α, β)`. -/
lemma volume_eq_zero_on_short_window {E : Set ℝ} {α β : ℝ} (hαβ : α < β)
    (hpiece : ∀ b ∈ E ∩ Ioo α β, volume (E ∩ Ioo α b) = 0) :
    volume (E ∩ Ioo α β) = 0 := by
  set S := E ∩ Ioo α β
  by_cases hS : S.Nonempty
  · have hBdd : BddAbove S := ⟨β, fun z hz => hz.2.2.le⟩
    set βs := sSup S
    choose u hu using fun k : ℕ =>
      exists_lt_of_lt_csSup hS
        (sub_lt_self βs (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1)))
    have hzero : ∀ k, volume (E ∩ Ioo α (u k)) = 0 :=
      fun k => hpiece (u k) (hu k).1
    have hcover : S ⊆ {βs} ∪ ⋃ k, E ∩ Ioo α (u k) := by
      intro z hz
      by_cases hzβ : z = βs
      · exact Or.inl hzβ
      · have hlt : z < βs := lt_of_le_of_ne (le_csSup hBdd hz) hzβ
        have hden : 0 < βs - z := sub_pos.2 hlt
        obtain ⟨k, hk⟩ := exists_nat_gt (1 / (βs - z))
        have hk0 : (0 : ℝ) < k := (one_div_pos.2 hden).trans hk
        have hfrac : (1 : ℝ) / (k + 1) < βs - z := by
          have h1 : (1 : ℝ) / (k + 1) < 1 / k := by
            rw [one_div_lt_one_div (by linarith) hk0]
            linarith
          exact h1.trans ((one_div_lt hden hk0).1 hk)
        exact Or.inr <| mem_iUnion.2 ⟨k, hz.1, hz.2.1, by linarith [(hu k).2]⟩
    have hU : volume (⋃ k : ℕ, E ∩ Ioo α (u k)) = 0 :=
      (measure_iUnion_null_iff).2 hzero
    have hsing : volume ({βs} : Set ℝ) = 0 := measure_singleton _
    refine le_antisymm ?_ bot_le
    calc volume S
        ≤ volume ({βs} ∪ ⋃ k, E ∩ Ioo α (u k)) := measure_mono hcover
      _ ≤ volume ({βs} : Set ℝ) + volume (⋃ k, E ∩ Ioo α (u k)) := measure_union_le _ _
      _ = 0 := by simp [hsing, hU]
  · rw [not_nonempty_iff_eq_empty.mp hS, measure_empty]

/-- Each uniformly left-steep set is Lebesgue null. -/
lemma volume_leftSteep_eq_zero (f : ℝ → ℝ) (q : ℚ) (n : ℕ) :
    volume (leftSteep f q n) = 0 := by
  set δ : ℝ := (1 : ℝ) / (n + 1)
  have hδ : 0 < δ := by positivity
  set ℓ : ℝ := δ / 2
  have hℓ : 0 < ℓ := by
    unfold ℓ
    exact half_pos hδ
  have hℓδ : ℓ < δ := by
    unfold ℓ
    exact half_lt_self hδ
  let window : ℤ → Set ℝ :=
    fun m => leftSteep f q n ∩ Ioo ((m : ℝ) * ℓ) (((m + 1 : ℤ) : ℝ) * ℓ)
  have hwindow : ∀ m, volume (window m) = 0 := by
    intro m
    have hαβ : (m : ℝ) * ℓ < ((m + 1 : ℤ) : ℝ) * ℓ := by
      have hm : ((m + 1 : ℤ) : ℝ) = (m : ℝ) + 1 := by simp
      rw [hm]
      nlinarith
    refine volume_eq_zero_on_short_window hαβ ?_
    intro b hb
    have hlen : b - (m : ℝ) * ℓ < δ := by
      have hbβ : b < ((m + 1 : ℤ) : ℝ) * ℓ := hb.2.2
      have hm : ((m + 1 : ℤ) : ℝ) = (m : ℝ) + 1 := by simp
      rw [hm] at hbβ
      nlinarith [hℓδ]
    exact volume_leftSteep_Ioo f q n hb.2.1 hlen hb.1
  let grid : Set ℝ := range fun m : ℤ => (m : ℝ) * ℓ
  have hsub : leftSteep f q n ⊆ grid ∪ ⋃ m, window m := by
    intro x hx
    let m := Int.floor (x / ℓ)
    have hmul : (m : ℝ) * ℓ ≤ x := by
      have hle := Int.floor_le (x / ℓ)
      have hne : ℓ ≠ 0 := hℓ.ne'
      nlinarith [div_mul_cancel₀ x hne]
    have hup : x < ((m + 1 : ℤ) : ℝ) * ℓ := by
      have hlt := Int.lt_floor_add_one (x / ℓ)
      have hm : ((m + 1 : ℤ) : ℝ) = (m : ℝ) + 1 := by simp
      rw [hm]
      have hne : ℓ ≠ 0 := hℓ.ne'
      nlinarith [div_mul_cancel₀ x hne]
    by_cases hxeq : x = (m : ℝ) * ℓ
    · exact Or.inl ⟨m, hxeq.symm⟩
    · have hlt : (m : ℝ) * ℓ < x := lt_of_le_of_ne hmul (Ne.symm hxeq)
      exact Or.inr <| mem_iUnion.2 ⟨m, hx, hlt, hup⟩
  have hgrid : volume grid = 0 := (countable_range _).measure_zero volume
  have hU : volume (⋃ m : ℤ, window m) = 0 := (measure_iUnion_null_iff).2 hwindow
  refine le_antisymm ?_ bot_le
  calc volume (leftSteep f q n)
      ≤ volume (grid ∪ ⋃ m, window m) := measure_mono hsub
    _ ≤ volume grid + volume (⋃ m, window m) := measure_union_le _ _
    _ = 0 := by simp [hgrid, hU]

/-- Where the upper right derivative is `⊤` and the lower left derivative is not `⊥`. -/
def infiniteUp (f : ℝ → ℝ) : Set ℝ :=
  {x | upperRightDiniDerivative f x = ⊤ ∧ lowerLeftDiniDerivative f x ≠ ⊥}

/-- A point of `infiniteUp` lies in some uniformly left-steep set. -/
lemma mem_leftSteep_of_infiniteUp {f : ℝ → ℝ} {x : ℝ} (hx : x ∈ infiniteUp f) :
    ∃ q : ℚ, ∃ n : ℕ, x ∈ leftSteep f q n := by
  have hbot : (⊥ : EReal) < lowerLeftDiniDerivative f x := (bot_lt_iff_ne_bot).2 hx.2
  obtain ⟨q, -, hq⟩ := EReal.exists_rat_btwn_of_lt hbot
  have hev : ∀ᶠ h in 𝓝[<] (0 : ℝ), (q : ℝ) < extendedDifferenceQuotient f x h :=
    eventually_lt_of_lt_liminf hq (diniQuotient_bddBelow f x _)
  rw [eventually_iff] at hev
  obtain ⟨εL, hεL, hsubL⟩ := (mem_nhdsLT_iff_exists_Ioo_subset (a := (0 : ℝ))).1 hev
  have hεLneg : εL < 0 := hεL
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / -εL)
  have hn0 : (0 : ℝ) < n := (one_div_pos.2 (neg_pos.2 hεLneg)).trans hn
  have hδ : (1 : ℝ) / (n + 1) < -εL := by
    have hstep : (1 : ℝ) / (n + 1) < 1 / n := by
      rw [one_div_lt_one_div (by linarith) hn0]
      linarith
    exact hstep.trans ((one_div_lt (neg_pos.2 hεLneg) hn0).1 hn)
  refine ⟨q, n, hx.1, ?_⟩
  intro h hhδ hh0
  have hge : εL < h := by
    have hε : εL < -((1 : ℝ) / (n + 1)) := by simpa using neg_lt_neg hδ
    have hlow : -((1 : ℝ) / (n + 1)) ≤ h := by
      rw [neg_div ((n : ℝ) + 1) (1 : ℝ)] at hhδ
      exact hhδ
    exact lt_of_lt_of_le hε hlow
  have hquot := hsubL ⟨hge, hh0⟩
  unfold extendedDifferenceQuotient at hquot
  exact (EReal.coe_lt_coe_iff).1 hquot

/-- The upper-right infinite mismatch is null. -/
theorem volume_infiniteUp (f : ℝ → ℝ) : volume (infiniteUp f) = 0 := by
  have hsub : infiniteUp f ⊆ ⋃ q : ℚ, ⋃ n : ℕ, leftSteep f q n := by
    intro x hx
    obtain ⟨q, n, hxS⟩ := mem_leftSteep_of_infiniteUp hx
    exact mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨n, hxS⟩⟩
  refine measure_mono_null hsub ?_
  rw [measure_iUnion_null_iff]
  intro q
  rw [measure_iUnion_null_iff]
  intro n
  exact volume_leftSteep_eq_zero f q n

/-- Where the lower left derivative is `⊥` and the upper right derivative is not `⊤`. -/
def infiniteDown (f : ℝ → ℝ) : Set ℝ :=
  {x | lowerLeftDiniDerivative f x = ⊥ ∧ upperRightDiniDerivative f x ≠ ⊤}

/-- Reflection identifies the lower-left mismatch with the upper-right mismatch. -/
lemma infiniteDown_eq_preimage (f : ℝ → ℝ) :
    infiniteDown f = Neg.neg ⁻¹' infiniteUp (fun t => f (-t)) := by
  ext x
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · rw [upperRightDiniDerivative_comp_neg, neg_neg, hx.1, EReal.neg_bot]
    · intro h
      rw [lowerLeftDiniDerivative_comp_neg, neg_neg, EReal.neg_eq_bot_iff] at h
      exact hx.2 h
  · intro hx
    refine ⟨?_, ?_⟩
    · have h := hx.1
      rw [upperRightDiniDerivative_comp_neg, neg_neg] at h
      exact EReal.neg_eq_top_iff.1 h
    · intro h
      have h' := hx.2
      rw [lowerLeftDiniDerivative_comp_neg, neg_neg] at h'
      exact h' (EReal.neg_eq_bot_iff.2 h)

/-- The lower-left infinite mismatch is null. -/
theorem volume_infiniteDown (f : ℝ → ℝ) : volume (infiniteDown f) = 0 := by
  rw [infiniteDown_eq_preimage, Measure.measure_preimage_neg]
  exact volume_infiniteUp fun t => f (-t)

end CKMA
