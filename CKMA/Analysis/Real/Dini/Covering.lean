/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic
public import Mathlib.Topology.Order.DenselyOrdered

/-!
# Slope packing for Dini derivatives

A uniform lower bound on short left increments, together with a fine cover by steep right
increments, controls the Lebesgue outer measure of an arbitrary set on a short interval.
The estimate is the telescope used by Hanson for the Denjoy–Young–Saks theorem: selected
intervals contribute the steep slope and the complementary gaps contribute the left slope.
The sets need not be measurable. Source: GAPS 05.10.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Set Filter Topology MeasureTheory Metric
open scoped BigOperators ENNReal NNReal

/-- A strict slope bound is a strict bound on the increment. -/
lemma mul_lt_of_lt_slope {x y c : ℝ} {f : ℝ → ℝ} (hxy : x < y)
    (h : c < (f y - f x) / (y - x)) : c * (y - x) < f y - f x :=
  (lt_div_iff₀ (sub_pos.2 hxy)).1 h

/-- Disjoint nonempty closed intervals, ordered from the left, have a gap between them. -/
lemma disjoint_Icc_right_lt {p q : ℝ × ℝ} (hp : p.1 < p.2) (hq : q.1 < q.2)
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

/-- Summing a nonnegative real function past a real threshold below its extended sum. -/
lemma exists_finset_sum_gt {ι : Type*} (φ : ι → ℝ) (hφ : ∀ i, 0 ≤ φ i)
    (hσ : ∑' i, ENNReal.ofReal (φ i) ≠ ⊤) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < (∑' i, ENNReal.ofReal (φ i)).toReal) :
    ∃ t : Finset ι, s < ∑ i ∈ t, φ i := by
  have hpos : 0 < (∑' i, ENNReal.ofReal (φ i)).toReal := hs0.trans_lt hs
  have hlt : ENNReal.ofReal s < ∑' i, ENNReal.ofReal (φ i) := by
    rw [← ENNReal.ofReal_toReal hσ]
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).2 hs
  rw [ENNReal.tsum_eq_iSup_sum] at hlt
  obtain ⟨t, ht⟩ := lt_iSup_iff.mp hlt
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hφ i)] at ht
  exact ⟨t, ((ENNReal.ofReal_lt_ofReal_iff').1 ht).1⟩

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
theorem finset_packing_lower (f : ℝ → ℝ) (E : Set ℝ) {c k δ a fin : ℝ}
    (hleft : ∀ x ∈ E, ∀ u, x - δ < u → u < x → c < (f x - f u) / (x - u))
    (ha : a < fin) (hlen : fin - a < δ) (hfin : fin ∈ E) (t : Finset (ℝ × ℝ))
    (hdisj : PairwiseDisjoint (t : Set (ℝ × ℝ)) fun p => Icc p.1 p.2)
    (hmem : ∀ p ∈ t, p.1 ∈ E ∧ a < p.1 ∧ p.1 < p.2 ∧ p.2 ≤ fin)
    (hsteep : ∀ p ∈ t, k < (f p.2 - f p.1) / (p.2 - p.1)) :
    c * (fin - a) + (k - c) * ∑ p ∈ t, (p.2 - p.1) < f fin - f a :=
  finset_packing_lower_aux f E c k δ fin hleft hfin t a ha hlen hdisj hmem hsteep

/-- Pairs in `(a, b]` based at `E` whose right increment is steeper than `k`. -/
def steepRight (f : ℝ → ℝ) (E : Set ℝ) (k a b : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ E ∧ a < p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b ∧ k < (f p.2 - f p.1) / (p.2 - p.1)}

/-- Outer measure of `E` on a short interval, from a left slope and a steep right cover. -/
theorem slopePacking_volume_le (f : ℝ → ℝ) (E : Set ℝ) {c k δ a b : ℝ} (hkc : c < k)
    (hab : a < b) (hlen : b - a < δ) (hb : b ∈ E)
    (hleft : ∀ x ∈ E, ∀ u, x - δ < u → u < x → c < (f x - f u) / (x - u))
    (hfine : ∀ x ∈ E ∩ Ioo a b, ∀ ε > 0, ∃ y, x < y ∧ y ≤ b ∧ y - x < ε ∧
      k < (f y - f x) / (y - x)) :
    (k - c) * (volume (E ∩ Ioo a b)).toReal ≤ (f b - f a) - c * (b - a) := by
  classical
  have : DecidableEq (ℝ × ℝ) := Classical.decEq _
  let t := steepRight f E k a b
  let B : ℝ × ℝ → Set ℝ := fun p => Icc p.1 p.2
  let s := E ∩ Ioo a b
  have hμ : ∀ p ∈ t, volume (closedBall p.1 (3 * (p.2 - p.1))) ≤
      (6 : ℝ≥0) * volume (B p) := by
    intro p hp
    rcases hp with ⟨-, -, hplt, -, -⟩
    have hr0 : 0 ≤ p.2 - p.1 := sub_nonneg.2 hplt.le
    rw [Real.closedBall_eq_Icc, Real.volume_Icc, Real.volume_Icc]
    have hlen6 : (p.1 + 3 * (p.2 - p.1)) - (p.1 - 3 * (p.2 - p.1)) =
        6 * (p.2 - p.1) := by ring
    rw [hlen6, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
    have h6 : ENNReal.ofReal (6 : ℝ) = (6 : ℝ≥0) := by
      simp
    rw [h6]
  obtain ⟨u, hut, hucount, hudisj, hcover⟩ :=
    Vitali.exists_disjoint_covering_ae (μ := volume) s t (C := 6)
      (r := fun p => p.2 - p.1) (c := fun p => p.1) B
      (fun p hp => by
        rcases hp with ⟨-, -, hplt, -, -⟩
        rw [Real.closedBall_eq_Icc]
        intro z hz
        refine ⟨?_, ?_⟩
        · linarith [hz.1, hplt.le]
        · linarith [hz.2])
      hμ
      (fun p hp => by
        rcases hp with ⟨-, -, hplt, -, -⟩
        rw [interior_Icc]
        exact nonempty_Ioo.2 hplt)
      (fun _ _ => isClosed_Icc)
      (fun x hx ε hε => by
        obtain ⟨y, hyx, hyb, hylen, hyslope⟩ := hfine x hx ε hε
        refine ⟨(x, y), ?_, hylen.le, rfl⟩
        exact ⟨hx.1, hx.2.1, hyx, hyb, hyslope⟩)
  have hunion : volume (⋃ p ∈ u, B p) = ∑' p : u, ENNReal.ofReal (p.1.2 - p.1.1) := by
    rw [measure_biUnion hucount hudisj (fun _ _ => measurableSet_Icc)]
    refine tsum_congr fun p => ?_
    rw [Real.volume_Icc]
  have hsubU : ⋃ p ∈ u, B p ⊆ Icc a b := by
    intro z hz
    simp only [mem_iUnion] at hz
    obtain ⟨p, hp, hzI⟩ := hz
    rcases hut hp with ⟨-, hpa, -, hpb, -⟩
    exact ⟨hpa.le.trans hzI.1, hzI.2.trans hpb⟩
  have hτfin : ∑' p : u, ENNReal.ofReal (p.1.2 - p.1.1) ≠ ⊤ := by
    rw [← hunion]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((measure_mono hsubU).trans_eq Real.volume_Icc)
  have hle : volume s ≤ ∑' p : u, ENNReal.ofReal (p.1.2 - p.1.1) := by
    have hcover' : s ⊆ (s \ ⋃ p ∈ u, B p) ∪ ⋃ p ∈ u, B p := by
      intro z hz
      by_cases hzu : z ∈ ⋃ p ∈ u, B p
      · exact Or.inr hzu
      · exact Or.inl ⟨hz, hzu⟩
    calc volume s
        ≤ volume ((s \ ⋃ p ∈ u, B p) ∪ ⋃ p ∈ u, B p) := measure_mono hcover'
      _ ≤ volume (s \ ⋃ p ∈ u, B p) + volume (⋃ p ∈ u, B p) := measure_union_le _ _
      _ = volume (⋃ p ∈ u, B p) := by rw [hcover, zero_add]
      _ = ∑' p : u, ENNReal.ofReal (p.1.2 - p.1.1) := hunion
  set σ : ℝ := (volume s).toReal
  set RHS : ℝ := (f b - f a) - c * (b - a)
  have hgapb : c * (b - a) < f b - f a :=
    mul_lt_of_lt_slope hab (hleft b hb a (by linarith) hab)
  have hRHS : 0 < RHS := by linarith
  have hσle : σ ≤ (∑' p : u, ENNReal.ofReal (p.1.2 - p.1.1)).toReal :=
    ENNReal.toReal_mono hτfin hle
  apply le_of_forall_pos_le_add
  intro ε hε
  by_cases hσ0 : σ = 0
  · rw [hσ0, mul_zero]
    linarith
  · have hσpos : 0 < σ := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hσ0)
    let ε' : ℝ := min (σ / 2) (ε / (k - c))
    have hε'pos : 0 < ε' := lt_min (half_pos hσpos) (div_pos hε (sub_pos.2 hkc))
    have hbelow : 0 ≤ σ - ε' := by
      have : ε' ≤ σ / 2 := min_le_left _ _
      linarith
    have hstrict : σ - ε' < (∑' p : u, ENNReal.ofReal (p.1.2 - p.1.1)).toReal := by
      exact (sub_lt_self σ hε'pos).trans_le hσle
    obtain ⟨tF, htF⟩ := exists_finset_sum_gt (fun i : u => i.1.2 - i.1.1)
      (fun i => sub_nonneg.2 (hut i.2).2.2.1.le) hτfin hbelow hstrict
    let e : u ↪ ℝ × ℝ := ⟨Subtype.val, Subtype.val_injective⟩
    let sP : Finset (ℝ × ℝ) := tF.map e
    have hdisjP : PairwiseDisjoint (sP : Set (ℝ × ℝ)) (fun p => Icc p.1 p.2) := by
      intro p hp q hq hpq
      obtain ⟨ip, hip, rfl⟩ := Finset.mem_map.mp hp
      obtain ⟨iq, hiq, rfl⟩ := Finset.mem_map.mp hq
      have hine : (ip : ℝ × ℝ) ≠ iq := hpq
      exact hudisj.disjoint_of_ne ip.2 iq.2 hine
    have hmemP : ∀ p ∈ sP, p.1 ∈ E ∧ a < p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b := by
      intro p hp
      obtain ⟨ip, -, rfl⟩ := Finset.mem_map.mp hp
      rcases hut ip.2 with ⟨hpE, hpa, hplt, hpb, -⟩
      exact ⟨hpE, hpa, hplt, hpb⟩
    have hsteepP : ∀ p ∈ sP, k < (f p.2 - f p.1) / (p.2 - p.1) := by
      intro p hp
      obtain ⟨ip, -, rfl⟩ := Finset.mem_map.mp hp
      exact (hut ip.2).2.2.2.2
    have hpack := finset_packing_lower f E hleft hab hlen hb sP hdisjP hmemP hsteepP
    have hlenP : σ - ε' < ∑ p ∈ sP, (p.2 - p.1) := by
      rw [Finset.sum_map]
      exact htF
    have hmul : (k - c) * (σ - ε') < RHS := by
      have hlt : (k - c) * (σ - ε') < (k - c) * ∑ p ∈ sP, (p.2 - p.1) :=
        mul_lt_mul_of_pos_left hlenP (sub_pos.2 hkc)
      linarith
    have hε'le : (k - c) * ε' ≤ ε := by
      have hle' : ε' ≤ ε / (k - c) := min_le_right _ _
      have hkpos : 0 < k - c := sub_pos.2 hkc
      calc (k - c) * ε' ≤ (k - c) * (ε / (k - c)) := mul_le_mul_of_nonneg_left hle' hkpos.le
        _ = ε := by field_simp
    linarith

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
      have hnpos : 0 < (n : ℝ) + 1 := by positivity
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

end CKMA
