/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Slope packing for Dini derivatives

A uniform lower bound on short left increments, together with a fine cover by steep right
increments, controls the Lebesgue outer measure of an arbitrary set on a short interval.
The estimate is the telescope used by Hanson for the Denjoy–Young–Saks theorem: selected
intervals contribute the steep slope and the complementary gaps contribute the left slope.
The sets need not be measurable. Source: GAPS 05.10.

## Main results

* `CKMA.Dini.slopePacking_volume_le`: outer-measure bound from a left slope and steep right cover.
* `CKMA.Dini.volume_eq_zero_of_arbitrarily_steep`: vanishing outer measure when arbitrarily steep
  right increments are available.

## Implementation notes

The private set `steepRight f E k a b` consists of the pairs `(x, y)` with `x ∈ E`,
`a < x < y ≤ b` and slope above `k`. Vitali's covering theorem selects a countable disjoint
subfamily covering `E ∩ (a, b)` up to a null set, and the private lemma `finset_packing_lower`
telescopes every finite subfamily against the left slope bound.
-/

public section

noncomputable section

namespace CKMA.Dini

open Set Filter Topology MeasureTheory Metric
open scoped BigOperators ENNReal NNReal

/-- A strict slope bound is a strict bound on the increment. -/
private lemma mul_lt_of_lt_slope {x y c : ℝ} {f : ℝ → ℝ} (hxy : x < y)
    (h : c < (f y - f x) / (y - x)) : c * (y - x) < f y - f x :=
  (lt_div_iff₀ (sub_pos.2 hxy)).1 h

/-- Disjoint nonempty closed intervals, ordered from the left, have a gap between them. -/
private lemma disjoint_Icc_right_lt {p q : ℝ × ℝ} (hp : p.1 < p.2) (hq : q.1 < q.2)
    (hle : p.1 ≤ q.1) (hdis : Disjoint (Icc p.1 p.2) (Icc q.1 q.2)) : p.2 < q.1 := by
  have hlt : p.1 < q.1 := by
    refine lt_of_le_of_ne hle ?_
    intro heq
    exact (not_disjoint_iff_nonempty_inter.2
      ⟨p.1, left_mem_Icc.2 hp.le, by simpa [heq] using left_mem_Icc.2 hq.le⟩) hdis
  refine lt_of_not_ge ?_
  intro hge
  have hinter : q.1 ∈ Icc p.1 p.2 ∩ Icc q.1 q.2 := by
    refine ⟨?_, left_mem_Icc.2 hq.le⟩
    exact ⟨hlt.le, hge⟩
  exact (not_disjoint_iff_nonempty_inter.2 ⟨q.1, hinter⟩) hdis

/-- Inductive telescoping lower bound for finite disjoint steep intervals. -/
private lemma finset_packing_lower_aux (f : ℝ → ℝ) (E : Set ℝ) (c k δ fin : ℝ)
    (hleft : ∀ x ∈ E, ∀ u, x - δ < u → u < x → c < (f x - f u) / (x - u))
    (hfin : fin ∈ E) :
    ∀ t : Finset (ℝ × ℝ), ∀ a, a < fin → fin - a < δ →
      PairwiseDisjoint (t : Set (ℝ × ℝ)) (fun p => Icc p.1 p.2) →
      (∀ p ∈ t, p.1 ∈ E ∧ a < p.1 ∧ p.1 < p.2 ∧ p.2 ≤ fin) →
      (∀ p ∈ t, k < (f p.2 - f p.1) / (p.2 - p.1)) →
      c * (fin - a) + (k - c) * ∑ p ∈ t, (p.2 - p.1) < f fin - f a := by
  classical
  have : DecidableEq ℝ := Classical.decEq ℝ
  have : DecidableRel (α := ℝ) (· ≤ ·) := Classical.decRel _
  have : DecidableEq (ℝ × ℝ) := Classical.decEq _
  refine Finset.eraseInduction ?_
  intro t ih a ha hlen hdisj hmem hsteep
  rcases t.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.sum_empty, mul_zero, add_zero]
    exact mul_lt_of_lt_slope ha (hleft fin hfin a (by linarith) ha)
  · obtain ⟨p, hp, hmin⟩ := t.exists_min_image (fun q => q.1) hne
    have hpm := hmem p hp
    have hgap : c * (p.1 - a) < f p.1 - f a :=
      mul_lt_of_lt_slope hpm.2.1 (hleft p.1 hpm.1 a (by linarith) hpm.2.1)
    have hrise : k * (p.2 - p.1) < f p.2 - f p.1 :=
      mul_lt_of_lt_slope hpm.2.2.1 (hsteep p hp)
    have hsum : (p.2 - p.1) + ∑ q ∈ t.erase p, (q.2 - q.1) = ∑ q ∈ t, (q.2 - q.1) :=
      Finset.add_sum_erase t (fun q : ℝ × ℝ => q.2 - q.1) hp
    rcases eq_or_lt_of_le hpm.2.2.2 with hpeq | hplt
    · have hempty : t.erase p = ∅ := by
        rcases (t.erase p).eq_empty_or_nonempty with hempty | hne'
        · exact hempty
        · obtain ⟨q, hq⟩ := hne'
          obtain ⟨hqne, hqt⟩ := Finset.mem_erase.mp hq
          have hqmem := hmem q hqt
          have hltq : p.2 < q.1 := disjoint_Icc_right_lt hpm.2.2.1 hqmem.2.2.1 (hmin q hqt)
            (hdisj.disjoint_of_ne hp hqt hqne.symm)
          linarith [hpeq, hqmem.2.2.2, hqmem.2.2.1]
      simp only [hempty, Finset.sum_empty, add_zero] at hsum
      subst hpeq
      rw [← hsum]
      nlinarith [hgap, hrise]
    · have hdis' : PairwiseDisjoint ((t.erase p) : Set (ℝ × ℝ))
          (fun q => Icc q.1 q.2) := by
        intro q hq r hr hqr
        obtain ⟨_, hqt⟩ := Finset.mem_erase.mp hq
        obtain ⟨_, hrt⟩ := Finset.mem_erase.mp hr
        exact hdisj.disjoint_of_ne hqt hrt hqr
      have hmem' : ∀ q ∈ t.erase p, q.1 ∈ E ∧ p.2 < q.1 ∧ q.1 < q.2 ∧ q.2 ≤ fin := by
        intro q hq
        obtain ⟨hqne, hqt⟩ := Finset.mem_erase.mp hq
        have hqmem := hmem q hqt
        exact ⟨hqmem.1, disjoint_Icc_right_lt hpm.2.2.1 hqmem.2.2.1 (hmin q hqt)
          (hdisj.disjoint_of_ne hp hqt hqne.symm), hqmem.2.2.1, hqmem.2.2.2⟩
      have hsteep' : ∀ q ∈ t.erase p, k < (f q.2 - f q.1) / (q.2 - q.1) :=
        fun q hq => hsteep q (Finset.mem_erase.mp hq).2
      have hIH := ih p hp p.2 hplt (by linarith) hdis' hmem' hsteep'
      rw [← hsum]
      nlinarith [hgap, hrise, hIH]

/-- Finite disjoint steep intervals and left-sloping gaps telescope on `(a, fin]`. -/
private theorem finset_packing_lower (f : ℝ → ℝ) (E : Set ℝ) {c k δ a fin : ℝ}
    (hleft : ∀ x ∈ E, ∀ u, x - δ < u → u < x → c < (f x - f u) / (x - u))
    (ha : a < fin) (hlen : fin - a < δ) (hfin : fin ∈ E) (t : Finset (ℝ × ℝ))
    (hdisj : PairwiseDisjoint (t : Set (ℝ × ℝ)) fun p => Icc p.1 p.2)
    (hmem : ∀ p ∈ t, p.1 ∈ E ∧ a < p.1 ∧ p.1 < p.2 ∧ p.2 ≤ fin)
    (hsteep : ∀ p ∈ t, k < (f p.2 - f p.1) / (p.2 - p.1)) :
    c * (fin - a) + (k - c) * ∑ p ∈ t, (p.2 - p.1) < f fin - f a :=
  finset_packing_lower_aux f E c k δ fin hleft hfin t a ha hlen hdisj hmem hsteep

/-- Pairs in `(a, b]` based at `E` whose right increment is steeper than `k`. -/
private def steepRight (f : ℝ → ℝ) (E : Set ℝ) (k a b : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ E ∧ a < p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b ∧ k < (f p.2 - f p.1) / (p.2 - p.1)}

/-- A countable disjoint family of steep right intervals covers `E ∩ (a, b)` up to a null set, so
the outer measure of `E ∩ (a, b)` is at most the total length of the family. -/
private lemma exists_steepRight_cover (f : ℝ → ℝ) (E : Set ℝ) {k a b : ℝ}
    (hfine : ∀ x ∈ E ∩ Ioo a b, ∀ ε > 0, ∃ y, x < y ∧ y ≤ b ∧ y - x < ε ∧
      k < (f y - f x) / (y - x)) :
    ∃ u ⊆ steepRight f E k a b, PairwiseDisjoint u (fun p => Icc p.1 p.2) ∧
      volume (E ∩ Ioo a b) ≤ ∑' p : u, ENNReal.ofReal (p.1.2 - p.1.1) := by
  have hμ : ∀ p ∈ steepRight f E k a b, volume (closedBall p.1 (3 * (p.2 - p.1))) ≤
      (6 : ℝ≥0) * volume (Icc p.1 p.2) := by
    intro p _
    rw [Real.closedBall_eq_Icc, Real.volume_Icc, Real.volume_Icc,
      show (p.1 + 3 * (p.2 - p.1)) - (p.1 - 3 * (p.2 - p.1)) = 6 * (p.2 - p.1) by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
    simp
  obtain ⟨u, hut, hucount, hudisj, hcover⟩ :=
    Vitali.exists_disjoint_covering_ae (μ := volume) (E ∩ Ioo a b) (steepRight f E k a b)
      (C := 6) (r := fun p => p.2 - p.1) (c := fun p => p.1) (fun p => Icc p.1 p.2)
      (fun p hp z hz => by
        rcases hp with ⟨-, -, hplt, -, -⟩
        rw [Real.closedBall_eq_Icc]
        exact ⟨by linarith [hz.1, hplt.le], by linarith [hz.2]⟩)
      hμ
      (fun p hp => by
        rcases hp with ⟨-, -, hplt, -, -⟩
        rw [interior_Icc]
        exact nonempty_Ioo.2 hplt)
      (fun _ _ => isClosed_Icc)
      (fun x hx ε hε => by
        obtain ⟨y, hyx, hyb, hylen, hyslope⟩ := hfine x hx ε hε
        exact ⟨(x, y), ⟨hx.1, hx.2.1, hyx, hyb, hyslope⟩, hylen.le, rfl⟩)
  refine ⟨u, hut, hudisj, (measure_mono_ae (ae_subset.2 hcover)).trans_eq ?_⟩
  rw [measure_biUnion hucount hudisj (fun _ _ => measurableSet_Icc)]
  exact tsum_congr fun p => Real.volume_Icc

/-- Outer measure of `E` on a short interval, from a left slope and a steep right cover. -/
theorem slopePacking_volume_le (f : ℝ → ℝ) (E : Set ℝ) {c k δ a b : ℝ} (hkc : c < k)
    (hab : a < b) (hlen : b - a < δ) (hb : b ∈ E)
    (hleft : ∀ x ∈ E, ∀ u, x - δ < u → u < x → c < (f x - f u) / (x - u))
    (hfine : ∀ x ∈ E ∩ Ioo a b, ∀ ε > 0, ∃ y, x < y ∧ y ≤ b ∧ y - x < ε ∧
      k < (f y - f x) / (y - x)) :
    (k - c) * (volume (E ∩ Ioo a b)).toReal ≤ (f b - f a) - c * (b - a) := by
  classical
  obtain ⟨u, hut, hudisj, hle⟩ := exists_steepRight_cover f E hfine
  have hkc' : 0 < k - c := sub_pos.2 hkc
  have hRHS : 0 ≤ ((f b - f a) - c * (b - a)) / (k - c) :=
    div_nonneg (by linarith [mul_lt_of_lt_slope hab (hleft b hb a (by linarith) hab)]) hkc'.le
  -- Each finite subfamily packs into `(a, b]` by the telescoping bound.
  have hsum : ∀ tF : Finset u,
      ∑ i ∈ tF, (i.1.2 - i.1.1) ≤ ((f b - f a) - c * (b - a)) / (k - c) := by
    intro tF
    let e : u ↪ ℝ × ℝ := ⟨Subtype.val, Subtype.val_injective⟩
    have hpack := finset_packing_lower f E hleft hab hlen hb (tF.map e)
      (fun p hp q hq hpq => by
        obtain ⟨ip, -, rfl⟩ := Finset.mem_map.mp hp
        obtain ⟨iq, -, rfl⟩ := Finset.mem_map.mp hq
        exact hudisj.disjoint_of_ne ip.2 iq.2 hpq)
      (fun p hp => by
        obtain ⟨ip, -, rfl⟩ := Finset.mem_map.mp hp
        rcases hut ip.2 with ⟨hpE, hpa, hplt, hpb, -⟩
        exact ⟨hpE, hpa, hplt, hpb⟩)
      (fun p hp => by
        obtain ⟨ip, -, rfl⟩ := Finset.mem_map.mp hp
        exact (hut ip.2).2.2.2.2)
    simp only [Finset.sum_map, e, Function.Embedding.coeFn_mk] at hpack
    rw [le_div_iff₀ hkc']
    linarith
  have htsum : ∑' p : u, ENNReal.ofReal (p.1.2 - p.1.1) ≤
      ENNReal.ofReal (((f b - f a) - c * (b - a)) / (k - c)) := by
    rw [tsum_eq_iSup_sum]
    refine iSup_le fun tF => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => sub_nonneg.2 (hut i.2).2.2.1.le]
    exact ENNReal.ofReal_le_ofReal (hsum tF)
  rw [← le_div_iff₀' hkc']
  exact ENNReal.toReal_le_of_le_ofReal hRHS (hle.trans htsum)

/-- If right increments of every height are available, the outer measure on `(a, b)` vanishes. -/
theorem volume_eq_zero_of_arbitrarily_steep (f : ℝ → ℝ) (E : Set ℝ) {c δ a b : ℝ}
    (hab : a < b) (hlen : b - a < δ) (hb : b ∈ E)
    (hleft : ∀ x ∈ E, ∀ u, x - δ < u → u < x → c < (f x - f u) / (x - u))
    (hfine : ∀ k, c < k → ∀ x ∈ E ∩ Ioo a b, ∀ ε > 0, ∃ y,
      x < y ∧ y ≤ b ∧ y - x < ε ∧ k < (f y - f x) / (y - x)) :
    volume (E ∩ Ioo a b) = 0 := by
  set σ : ℝ := (volume (E ∩ Ioo a b)).toReal
  set RHS : ℝ := (f b - f a) - c * (b - a)
  have hbound : ∀ n : ℕ, ((n : ℝ) + 1) * σ ≤ RHS := by
    intro n
    have hk : c < c + (n + 1) := by linarith
    have hpack := slopePacking_volume_le f E hk hab hlen hb hleft (hfine (c + (n + 1)) hk)
    simpa [RHS, add_sub_cancel_left] using hpack
  have hσ0 : σ ≤ 0 := by
    by_contra hpos
    have hσpos : 0 < σ := lt_of_not_ge hpos
    obtain ⟨n, hn⟩ := exists_nat_gt (RHS / σ)
    have hn1 : RHS / σ < (n : ℝ) + 1 := by linarith
    have : RHS < ((n : ℝ) + 1) * σ := by
      calc RHS = (RHS / σ) * σ := by field_simp
        _ < ((n : ℝ) + 1) * σ := mul_lt_mul_of_pos_right hn1 hσpos
    linarith [hbound n]
  have hσnonneg : 0 ≤ σ := ENNReal.toReal_nonneg
  have hσeq : σ = 0 := le_antisymm hσ0 hσnonneg
  have hvolfin : volume (E ∩ Ioo a b) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((measure_mono (inter_subset_right : E ∩ Ioo a b ⊆ Ioo a b)).trans_eq Real.volume_Ioo)
  rcases (ENNReal.toReal_eq_zero_iff (volume (E ∩ Ioo a b))).1 hσeq with h0 | htop
  · exact h0
  · exact absurd htop hvolfin

end CKMA.Dini
