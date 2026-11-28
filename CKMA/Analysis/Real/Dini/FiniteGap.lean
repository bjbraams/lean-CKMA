/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Real.Dini.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

import CKMA.Analysis.Real.Dini.Infinite
import CKMA.Analysis.Real.Dini.Covering
import Mathlib.MeasureTheory.Covering.OneDim
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Finite gaps between opposite Dini derivatives

On a short interval whose endpoints lie in a set of uniformly bounded slopes, a direct Vitali
packing and the same packing for the reflected function force the outer measure to be a definite
fraction of the length. Lebesgue density points then make each such set null, and a countable
union absorbs every point at which the lower left derivative is finite, strictly below the upper
right derivative, and the upper right derivative is finite. Source: GAPS 05.10.

## Main definitions

* `CKMA.Dini.finiteGap`: points with uniform slope bounds and a rational gap between lower left
  and upper right Dini derivatives.
* `CKMA.Dini.finiteStrict`: countable union of all rational-witness `finiteGap` sets.

## Main results

* `CKMA.Dini.volume_finiteStrict`: `finiteStrict f` has Lebesgue measure zero.
* `CKMA.Dini.mem_finiteStrict_of_lt`: any finite strict inequality between lower left and upper
  right Dini derivatives lies in `finiteStrict f`.

## Implementation notes

The private lemma `finiteGap_volume_le` bounds the outer measure of `finiteGap f p r s q n` on a
short interval with both endpoints in the set by the fraction `(p - q) / ((p - q) + (r - s))`
of its length, from the packing of `f` and of its reflection. Lebesgue's density theorem then
makes each `finiteGap` set null.
-/

public section

noncomputable section

namespace CKMA.Dini

open Set Filter Topology MeasureTheory IsUnifLocDoublingMeasure
open scoped ENNReal

/-- A left increment flatter than `s` exists at every negative scale below the liminf. -/
private lemma exists_left_slope_lt (f : ℝ → ℝ) (x s ε : ℝ)
    (hs : lowerLeftDiniDerivative f x < (s : EReal)) (hε : ε < 0) :
    ∃ h, ε < h ∧ h < 0 ∧ (f (x + h) - f x) / h < s := by
  have hfreq : ∃ᶠ h in 𝓝[<] (0 : ℝ), extendedDifferenceQuotient f x h < (s : EReal) :=
    frequently_lt_of_liminf_lt (hu := isCobounded_ge_of_top) hs
  have hmem : Ioo ε (0 : ℝ) ∈ 𝓝[<] 0 := by
    rw [mem_nhdsLT_iff_exists_Ioo_subset]
    exact ⟨ε, hε, subset_rfl⟩
  have hsmall : ∀ᶠ h in 𝓝[<] (0 : ℝ), ε < h ∧ h < 0 :=
    eventually_of_mem hmem fun h hh => ⟨hh.1, hh.2⟩
  obtain ⟨h, hhE, hh⟩ := (hfreq.and_eventually hsmall).exists
  refine ⟨h, hh.1, hh.2, ?_⟩
  unfold extendedDifferenceQuotient at hhE
  exact (EReal.coe_lt_coe_iff).1 hhE

/-- Reflection through a point preserves Lebesgue outer measure. -/
private lemma volume_preimage_reflect (c : ℝ) (s : Set ℝ) :
    volume ((fun x => c - x) ⁻¹' s) = volume s := by
  have hcomp : (fun x : ℝ => c - x) = (fun x => c + x) ∘ Neg.neg := by
    ext x
    simp [Function.comp, sub_eq_add_neg]
  rw [hcomp, preimage_comp, Measure.measure_preimage_neg, measure_preimage_add]

/-- Reflection through the centre preserves the outer measure of a set inside `(a, b)`. -/
private lemma volume_reflect_inter {E : Set ℝ} {a b : ℝ} :
    volume ({x | a + b - x ∈ E} ∩ Ioo a b) = volume (E ∩ Ioo a b) := by
  have hpre : (fun x => a + b - x) ⁻¹' (E ∩ Ioo a b) =
      {x | a + b - x ∈ E} ∩ Ioo a b := by
    ext x
    simp only [mem_preimage, mem_inter_iff, mem_Ioo, mem_ofPred_eq]
    constructor
    · intro hx
      exact ⟨hx.1, by linarith [hx.2.1, hx.2.2], by linarith [hx.2.1, hx.2.2]⟩
    · intro hx
      exact ⟨hx.1, by linarith [hx.2.1, hx.2.2], by linarith [hx.2.1, hx.2.2]⟩
  rw [← hpre]
  exact volume_preimage_reflect (a + b) (E ∩ Ioo a b)

/-- Points with uniform slope bounds and a finite gap between the lower left and upper right
derivatives. `n` fixes the scale `1 / (n + 1)`. -/
@[expose]
def finiteGap (f : ℝ → ℝ) (p r s q : ℚ) (n : ℕ) : Set ℝ :=
  {x |
    (∀ h, 0 < h → h ≤ (1 : ℝ) / (n + 1) → (f (x + h) - f x) / h < (p : ℝ)) ∧
    (∀ h, -(1 : ℝ) / (n + 1) ≤ h → h < 0 → (q : ℝ) < (f (x + h) - f x) / h) ∧
    ((r : ℝ) : EReal) < upperRightDiniDerivative f x ∧
    lowerLeftDiniDerivative f x < ((s : ℝ) : EReal)}

/-- Membership in `finiteGap f p r s q n`. -/
lemma mem_finiteGap_iff {f : ℝ → ℝ} {p r s q : ℚ} {n : ℕ} {x : ℝ} :
    x ∈ finiteGap f p r s q n ↔
      (∀ h, 0 < h → h ≤ (1 : ℝ) / (n + 1) → (f (x + h) - f x) / h < (p : ℝ)) ∧
      (∀ h, -(1 : ℝ) / (n + 1) ≤ h → h < 0 → (q : ℝ) < (f (x + h) - f x) / h) ∧
      ((r : ℝ) : EReal) < upperRightDiniDerivative f x ∧
      lowerLeftDiniDerivative f x < ((s : ℝ) : EReal) :=
  Iff.rfl

/-- The direct packing: steep right increments above `r` against left slopes above `q`, with
the right endpoint in `finiteGap`. -/
private lemma finiteGap_pack_right (f : ℝ → ℝ) {p r s q : ℚ} {n : ℕ} {a b : ℝ}
    (hqr : (q : ℝ) < r) (hab : a < b) (hlen : b - a < (1 : ℝ) / (n + 1))
    (hb : b ∈ finiteGap f p r s q n) :
    ((r : ℝ) - q) * (volume (finiteGap f p r s q n ∩ Ioo a b)).toReal ≤
      (f b - f a) - q * (b - a) := by
  refine slopePacking_volume_le f _ hqr hab hlen hb ?_ ?_
  · intro x hx u hu hux
    have hge : -(1 : ℝ) / (n + 1) ≤ u - x := by
      rw [neg_div]
      linarith
    have hs := hx.2.1 (u - x) hge (by linarith)
    rwa [add_sub_cancel, ← neg_div_neg_eq, neg_sub, neg_sub] at hs
  · intro x hx ε hε
    obtain ⟨h, hh0, hhε, hhs⟩ := exists_right_slope_gt f x r (min ε (b - x)) hx.1.2.2.1
      (lt_min hε (sub_pos.2 hx.2.2))
    refine ⟨x + h, by linarith, ?_, ?_, ?_⟩
    · linarith [min_le_right ε (b - x)]
    · rw [add_sub_cancel_left]
      exact hhε.trans_le (min_le_left _ _)
    · rwa [add_sub_cancel_left]

/-- The reflected packing: the packing for `t ↦ f (a + b - t)`, with the left endpoint in
`finiteGap`. -/
private lemma finiteGap_pack_left (f : ℝ → ℝ) {p r s q : ℚ} {n : ℕ} {a b : ℝ}
    (hsp : (s : ℝ) < p) (hab : a < b) (hlen : b - a < (1 : ℝ) / (n + 1))
    (ha : a ∈ finiteGap f p r s q n) :
    ((p : ℝ) - s) * (volume (finiteGap f p r s q n ∩ Ioo a b)).toReal ≤
      (f a - f b) + p * (b - a) := by
  set E := finiteGap f p r s q n
  let g : ℝ → ℝ := fun t => f (a + b - t)
  have hleft' : ∀ x ∈ {t | a + b - t ∈ E}, ∀ u, x - (1 : ℝ) / (n + 1) < u → u < x →
      -(p : ℝ) < (g x - g u) / (x - u) := by
    intro x hx u hu hux
    have hs := (show a + b - x ∈ E from hx).1 (x - u) (by linarith) (by linarith)
    rw [show (a + b - x) + (x - u) = a + b - u by ring] at hs
    rw [show (g x - g u) / (x - u) = -((f (a + b - u) - f (a + b - x)) / (x - u)) by
      rw [← neg_div, neg_sub]]
    exact neg_lt_neg hs
  have hfine' : ∀ x ∈ {t | a + b - t ∈ E} ∩ Ioo a b, ∀ ε > 0, ∃ y, x < y ∧ y ≤ b ∧
      y - x < ε ∧ -(s : ℝ) < (g y - g x) / (y - x) := by
    intro x hx ε hε
    obtain ⟨h, hhε, hh0, hhs⟩ := exists_left_slope_lt f (a + b - x) (s : ℝ) (-min ε (b - x))
      (show a + b - x ∈ E from hx.1).2.2.2 (neg_lt_zero.2 (lt_min hε (sub_pos.2 hx.2.2)))
    have hden : (x - h) - x = -h := by ring
    refine ⟨x - h, by linarith, ?_, ?_, ?_⟩
    · linarith [min_le_right ε (b - x)]
    · rw [hden]
      linarith [min_le_left ε (b - x)]
    · have hquot : (g (x - h) - g x) / ((x - h) - x) =
          -((f ((a + b - x) + h) - f (a + b - x)) / h) := by
        simp only [g]
        rw [hden, show a + b - (x - h) = (a + b - x) + h by ring, div_neg]
      rw [hquot]
      exact neg_lt_neg hhs
  have hpack := slopePacking_volume_le g {t | a + b - t ∈ E} (neg_lt_neg hsp) hab hlen
    (show a + b - b ∈ E by simpa using ha) hleft' hfine'
  rw [volume_reflect_inter, show g b - g a = f a - f b by simp [g]] at hpack
  linarith

/-- Both endpoints in `finiteGap` give an outer-measure bound by the gap ratio. -/
private lemma finiteGap_volume_le (f : ℝ → ℝ) {p r s q : ℚ} {n : ℕ} {a b : ℝ}
    (hqr : (q : ℝ) < r) (hsp : (s : ℝ) < p)
    (hab : a < b) (hlen : b - a < (1 : ℝ) / (n + 1))
    (ha : a ∈ finiteGap f p r s q n) (hb : b ∈ finiteGap f p r s q n) :
    (volume (finiteGap f p r s q n ∩ Ioo a b)).toReal ≤
      ((p - q) / ((p - q) + (r - s))) * (b - a) := by
  have h1 := finiteGap_pack_right f hqr hab hlen hb
  have h2 := finiteGap_pack_left f hsp hab hlen ha
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  linarith

/-- Short intervals with an endpoint ratio bound have small outer measure up to the right end. -/
private lemma volume_Icc_le_of_endpoint_ratio {E : Set ℝ} {δ ρ y x : ℝ}
    (hρ : 0 ≤ ρ) (hlen : x - y < δ) (hx : x ∈ E)
    (hbound : ∀ a b, a ∈ E → b ∈ E → a < b → b - a < δ →
      (volume (E ∩ Ioo a b)).toReal ≤ ρ * (b - a)) :
    volume (E ∩ Icc y x) ≤ ENNReal.ofReal (ρ * (x - y)) := by
  rw [← measure_congr (EventuallyEqSet.inter (by rfl : E =ᵐ[volume] E) Ioo_ae_eq_Icc)]
  set S := E ∩ Ioo y x
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS, measure_empty]
    exact zero_le
  have hBdd : BddBelow S := ⟨y, fun z hz => hz.2.1.le⟩
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  -- Points of `S` left of `z` lie in `[inf S, z]`, an interval of length below `ε`.
  obtain ⟨z, hzS, hz⟩ := exists_lt_of_csInf_lt hS
    (lt_add_of_pos_right (sInf S) (NNReal.coe_pos.2 hε))
  have hsub : S ⊆ Icc (sInf S) z ∪ (E ∩ Ioo z x) := fun w hw =>
    (le_or_gt w z).imp (fun hwz => ⟨csInf_le hBdd hw, hwz⟩) fun hzw => ⟨hw.1, hzw, hw.2.2⟩
  have hfin : volume (E ∩ Ioo z x) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((measure_mono inter_subset_right).trans_eq Real.volume_Ioo)
  have hright : volume (E ∩ Ioo z x) ≤ ENNReal.ofReal (ρ * (x - y)) := by
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal ((hbound z x hzS.1 hx hzS.2.2 (by linarith [hzS.2.1])).trans
      (mul_le_mul_of_nonneg_left (by linarith [hzS.2.1]) hρ))
  have hleft : volume (Icc (sInf S) z) ≤ ε := Real.volume_Icc.trans_le
    (ENNReal.ofReal_le_of_le_toReal (by rw [ENNReal.coe_toReal]; linarith))
  calc volume S ≤ volume (Icc (sInf S) z) + volume (E ∩ Ioo z x) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (ρ * (x - y)) + ε := by rw [add_comm]; exact add_le_add hright hleft

/-- A uniform positive-density failure on the left forces the outer measure to vanish. -/
private lemma volume_eq_zero_of_short_ratio {E : Set ℝ} {δ ρ : ℝ}
    (hδ : 0 < δ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hbound : ∀ a b, a ∈ E → b ∈ E → a < b → b - a < δ →
      (volume (E ∩ Ioo a b)).toReal ≤ ρ * (b - a)) :
    volume E = 0 := by
  let v := vitaliFamily (volume : Measure ℝ) 1
  have hden := v.ae_tendsto_measure_inter_div E
  have hfail : ∀ x ∈ E, ¬ Tendsto (fun a => volume (E ∩ a) / volume a)
      (v.filterAt x) (𝓝 1) := by
    intro x hx htend
    have hcomp := htend.comp (Real.tendsto_Icc_vitaliFamily_left x)
    obtain ⟨θ, hθρ, hθ1⟩ := exists_between hρ1
    have hclose : ∀ᶠ y in 𝓝[<] x,
        ENNReal.ofReal θ < volume (E ∩ Icc y x) / volume (Icc y x) :=
      (tendsto_order.1 hcomp).1 _ ((ENNReal.ofReal_lt_one).2 hθ1)
    rw [eventually_iff] at hclose
    obtain ⟨ε, hε, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset (a := x)).1 hclose
    have hmax : max ε (x - δ) < x := max_lt hε (sub_lt_self x hδ)
    set y := (max ε (x - δ) + x) / 2
    have hyL : max ε (x - δ) < y := by
      unfold y
      linarith [hmax]
    have hyU : y < x := by
      unfold y
      linarith [hmax]
    have hyθ := hsub ⟨lt_of_le_of_lt (le_max_left _ _) hyL, hyU⟩
    have hpos : 0 < x - y := sub_pos.2 hyU
    have hlen : x - y < δ := by
      unfold y
      nlinarith [le_max_right ε (x - δ), hδ]
    have hvolI : volume (Icc y x) = ENNReal.ofReal (x - y) := Real.volume_Icc
    have hne0 : volume (Icc y x) ≠ 0 := by
      rw [hvolI, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hpos
    have hnetop : volume (Icc y x) ≠ ⊤ := by
      rw [hvolI]
      exact ENNReal.ofReal_ne_top
    have hgt : ENNReal.ofReal (θ * (x - y)) < volume (E ∩ Icc y x) := by
      have hmul := (ENNReal.lt_div_iff_mul_lt (Or.inl hne0) (Or.inl hnetop)).1 hyθ
      rw [hvolI, ← ENNReal.ofReal_mul (lt_of_le_of_lt hρ hθρ).le] at hmul
      exact hmul
    have hupper := volume_Icc_le_of_endpoint_ratio hρ hlen hx hbound
    have hcmp : ENNReal.ofReal (ρ * (x - y)) < ENNReal.ofReal (θ * (x - y)) :=
      (ENNReal.ofReal_lt_ofReal_iff (mul_pos (lt_of_le_of_lt hρ hθρ) hpos)).2
        (mul_lt_mul_of_pos_right hθρ hpos)
    exact lt_irrefl _ (lt_trans (lt_of_lt_of_le hgt hupper) hcmp)
  have hnull : (volume.restrict E) {x | ¬ Tendsto (fun a => volume (E ∩ a) / volume a)
      (v.filterAt x) (𝓝 1)} = 0 := (ae_iff).1 hden
  have hsub : E ⊆ {x | ¬ Tendsto (fun a => volume (E ∩ a) / volume a)
      (v.filterAt x) (𝓝 1)} := fun x hx => hfail x hx
  have hle : volume E ≤ 0 := by
    rw [← Measure.restrict_apply_self]
    exact (measure_mono hsub).trans_eq hnull
  exact le_antisymm hle bot_le

/-- Each uniformly gapped set with `q < s < r < p` is null. -/
private theorem volume_finiteGap_eq_zero (f : ℝ → ℝ) {p r s q : ℚ} {n : ℕ}
    (hqs : (q : ℝ) < s) (hsr : (s : ℝ) < r) (hrp : (r : ℝ) < p) :
    volume (finiteGap f p r s q n) = 0 := by
  set ρ : ℝ := (p - q) / ((p - q) + (r - s))
  have hρ : 0 ≤ ρ := div_nonneg (by linarith) (by linarith)
  have hρ1 : ρ < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  refine volume_eq_zero_of_short_ratio (δ := (1 : ℝ) / (n + 1)) (by positivity) hρ hρ1 ?_
  intro a b ha hb hab hlen
  exact finiteGap_volume_le f (by linarith) (by linarith) hab hlen ha hb

/-- Points at which a finite lower left derivative lies strictly below a finite upper right
derivative, witnessed by rational bounds. -/
@[expose]
def finiteStrict (f : ℝ → ℝ) : Set ℝ :=
  ⋃ p : ℚ, ⋃ r : ℚ, ⋃ s : ℚ, ⋃ q : ℚ, ⋃ n : ℕ,
    {x | (q : ℝ) < s ∧ (s : ℝ) < r ∧ (r : ℝ) < p ∧ x ∈ finiteGap f p r s q n}

/-- Membership in `finiteStrict f`. -/
lemma mem_finiteStrict_iff {f : ℝ → ℝ} {x : ℝ} :
    x ∈ finiteStrict f ↔ ∃ p r s q : ℚ, ∃ n : ℕ,
      (q : ℝ) < s ∧ (s : ℝ) < r ∧ (r : ℝ) < p ∧ x ∈ finiteGap f p r s q n := by
  simp only [finiteStrict, mem_iUnion, mem_ofPred_eq]

/-- The finite strict gap between the lower left and upper right derivatives is null. -/
theorem volume_finiteStrict (f : ℝ → ℝ) : volume (finiteStrict f) = 0 := by
  rw [finiteStrict, measure_iUnion_null_iff]
  intro p
  rw [measure_iUnion_null_iff]
  intro r
  rw [measure_iUnion_null_iff]
  intro s
  rw [measure_iUnion_null_iff]
  intro q
  rw [measure_iUnion_null_iff]
  intro n
  by_cases h : (q : ℝ) < s ∧ (s : ℝ) < r ∧ (r : ℝ) < p
  · exact measure_mono_null (fun x hx => hx.2.2.2)
      (volume_finiteGap_eq_zero f h.1 h.2.1 h.2.2)
  · refine measure_mono_null ?_ (by simp : volume (∅ : Set ℝ) = 0)
    intro x hx
    exact absurd ⟨hx.1, hx.2.1, hx.2.2.1⟩ h

/-- A finite strict inequality `lowerLeft < upperRight` lies in `finiteStrict`. -/
lemma mem_finiteStrict_of_lt {f : ℝ → ℝ} {x : ℝ}
    (hURtop : upperRightDiniDerivative f x ≠ ⊤)
    (hURbot : upperRightDiniDerivative f x ≠ ⊥)
    (hLLtop : lowerLeftDiniDerivative f x ≠ ⊤)
    (hLLbot : lowerLeftDiniDerivative f x ≠ ⊥)
    (hlt : lowerLeftDiniDerivative f x < upperRightDiniDerivative f x) :
    x ∈ finiteStrict f := by
  have hUR : ((upperRightDiniDerivative f x).toReal : EReal) =
      upperRightDiniDerivative f x := EReal.coe_toReal hURtop hURbot
  have hLL : ((lowerLeftDiniDerivative f x).toReal : EReal) =
      lowerLeftDiniDerivative f x := EReal.coe_toReal hLLtop hLLbot
  have hltR : (lowerLeftDiniDerivative f x).toReal <
      (upperRightDiniDerivative f x).toReal := by
    rw [← EReal.coe_lt_coe_iff, hLL, hUR]
    exact hlt
  obtain ⟨q, hqL⟩ := exists_rat_lt (lowerLeftDiniDerivative f x).toReal
  obtain ⟨s, hsL, hsU⟩ := exists_rat_btwn hltR
  obtain ⟨r, hrL, hrU⟩ := exists_rat_btwn hsU
  obtain ⟨p, hpU⟩ := exists_rat_gt (upperRightDiniDerivative f x).toReal
  have hURlt : upperRightDiniDerivative f x < (p : ℝ) := by
    rw [← hUR]
    exact EReal.coe_lt_coe_iff.2 hpU
  have hLLgt : ((q : ℝ) : EReal) < lowerLeftDiniDerivative f x := by
    rw [← hLL]
    exact EReal.coe_lt_coe_iff.2 hqL
  have hR : ∀ᶠ h in 𝓝[>] (0 : ℝ), extendedDifferenceQuotient f x h < (p : ℝ) :=
    eventually_lt_of_limsup_lt hURlt (isBoundedUnder_le_extendedDifferenceQuotient f x _)
  have hL : ∀ᶠ h in 𝓝[<] (0 : ℝ), (q : ℝ) < extendedDifferenceQuotient f x h :=
    eventually_lt_of_lt_liminf hLLgt (isBoundedUnder_ge_extendedDifferenceQuotient f x _)
  rw [eventually_iff] at hR hL
  obtain ⟨εR, hεR, hsubR⟩ := (mem_nhdsGT_iff_exists_Ioo_subset (a := (0 : ℝ))).1 hR
  obtain ⟨εL, hεL, hsubL⟩ := (mem_nhdsLT_iff_exists_Ioo_subset (a := (0 : ℝ))).1 hL
  obtain ⟨n, hδ⟩ := exists_nat_one_div_lt (lt_min hεR (neg_pos.2 hεL))
  have hxGap : x ∈ finiteGap f p r s q n := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h hh0 hhδ
      have hmem : h ∈ Ioo (0 : ℝ) εR :=
        ⟨hh0, lt_of_le_of_lt hhδ (hδ.trans_le (min_le_left _ _))⟩
      have hquot := hsubR hmem
      unfold extendedDifferenceQuotient at hquot
      exact (EReal.coe_lt_coe_iff).1 hquot
    · intro h hhδ hh0
      have hδL : (1 : ℝ) / (n + 1) < -εL := hδ.trans_le (min_le_right _ _)
      have hge : εL < h := by
        have hε : εL < -((1 : ℝ) / (n + 1)) := by simpa using neg_lt_neg hδL
        have hlow : -((1 : ℝ) / (n + 1)) ≤ h := by
          rw [neg_div ((n : ℝ) + 1) (1 : ℝ)] at hhδ
          exact hhδ
        exact lt_of_lt_of_le hε hlow
      have hquot := hsubL ⟨hge, hh0⟩
      unfold extendedDifferenceQuotient at hquot
      exact (EReal.coe_lt_coe_iff).1 hquot
    · rw [← hUR]
      exact EReal.coe_lt_coe_iff.2 hrU
    · rw [← hLL]
      exact EReal.coe_lt_coe_iff.2 hsL
  have hqs : (q : ℝ) < s := hqL.trans hsL
  have hsr : (s : ℝ) < r := hrL
  have hrp : (r : ℝ) < p := hrU.trans hpU
  exact mem_finiteStrict_iff.2 ⟨p, r, s, q, n, hqs, hsr, hrp, hxGap⟩

end CKMA.Dini
