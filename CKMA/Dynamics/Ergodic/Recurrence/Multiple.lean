/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Combinatorics.Additive.Corner.Roth
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Logic.Function.Iterate
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.Filter.IsBounded
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Instances.ENNReal.Lemmas

import Mathlib.Tactic

/-!
# Multiple recurrence from progression counts

An initial orbit segment that meets a positive-measure set in positive density contains
many arithmetic progressions, once a Szemerédi count is available. Integrating those
progressions bounds the Cesàro means of the corresponding return intersections from below.

Roth's theorem supplies the quadratic count for progressions of length three. The same
averaging applies to every longer progression.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Finset MeasureTheory Filter Topology Asymptotics Function
open scoped ENNReal BigOperators

attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Pairs `(a, d)` indexing a nontrivial `L`-term progression inside `{0, …, N - 1}`. -/
def apParams (L N : ℕ) : Finset (ℕ × ℕ) :=
  (range N ×ˢ range N).filter fun p => 0 < p.2 ∧ p.1 + (L - 1) * p.2 < N

/-- Nontrivial `L`-term progressions lying in `S` and in `{0, …, N - 1}`. -/
def progressionCount (L N : ℕ) (S : Finset ℕ) : ℕ :=
  ((apParams L N).filter fun p => ∀ j ∈ range L, p.1 + j * p.2 ∈ S).card

/-- A subset of an initial interval denser than its Roth number contains a 3-term progression. -/
private lemma exists_threeAP_of_gt_roth {M : ℕ} {B : Finset ℕ}
    (hB : B ⊆ range M) (hcard : rothNumberNat M < B.card) :
    ∃ a d, 0 < d ∧ a + 2 * d < M ∧ a ∈ B ∧ a + d ∈ B ∧ a + 2 * d ∈ B := by
  have hnot : ¬ ThreeAPFree (B : Set ℕ) := by
    intro hfree
    exact (hfree.le_rothNumberNat B (fun x hx => mem_range.mp (hB hx)) rfl).not_gt hcard
  rw [ThreeAPFree] at hnot
  push Not at hnot
  obtain ⟨a, ha, b, hb, c, hc, hsum, hne⟩ := hnot
  have haM : a < M := mem_range.mp (hB ha)
  have hcM : c < M := mem_range.mp (hB hc)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmid_eq : a + (b - a) = b := Nat.add_sub_of_le hlt.le
    have hend_eq : a + 2 * (b - a) = c := by omega
    refine ⟨a, b - a, Nat.sub_pos_of_lt hlt, ?_, ha, ?_, ?_⟩
    · rw [hend_eq]; exact hcM
    · rw [hmid_eq]; exact hb
    · rw [hend_eq]; exact hc
  · have hmid_eq : c + (a - b) = b := by omega
    have hend_eq : c + 2 * (a - b) = a := by omega
    refine ⟨c, a - b, Nat.sub_pos_of_lt hgt, ?_, hc, ?_, ?_⟩
    · rw [hend_eq]; exact haM
    · rw [hmid_eq]; exact hb
    · rw [hend_eq]; exact ha

/-- Every nonempty initial interval has Roth number at least one. -/
private lemma one_le_rothNumberNat {M : ℕ} (hM : 1 ≤ M) : 1 ≤ rothNumberNat M := by
  have hfree : ThreeAPFree (({0} : Finset ℕ) : Set ℕ) := by
    intro a ha b hb c hc _
    simp only [mem_coe, mem_singleton] at ha hb
    rw [ha, hb]
  have hlt : ∀ x ∈ ({0} : Finset ℕ), x < M := by
    intro x hx
    simp only [mem_singleton] at hx
    omega
  exact hfree.le_rothNumberNat ({0} : Finset ℕ) hlt (by simp)

/-- A scale on which subsets denser than `ε` contain a 3-term progression. -/
private lemma exists_roth_scale {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, 1 ≤ M ∧ (rothNumberNat M : ℝ) ≤ ε * (M : ℝ) := by
  have hev := (isLittleO_iff.mp rothNumberNat_isLittleO_id hε)
  rw [eventually_atTop] at hev
  obtain ⟨M0, hM0⟩ := hev
  refine ⟨max M0 1, le_max_right _ _, ?_⟩
  have hle := hM0 (max M0 1) (le_max_left _ _)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hle
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)] at hle
  exact hle

/-- Windows `(t, s)` of length `M` and step `s ≤ R` contained in `{0, …, N - 1}`. -/
def windowParams (M N R : ℕ) : Finset (ℕ × ℕ) :=
  (range N ×ˢ Icc 1 R).filter fun p => p.1 + (M - 1) * p.2 < N

/-- Indices at which a window meets `S`. -/
def windowHits (S : Finset ℕ) (M : ℕ) (p : ℕ × ℕ) : Finset ℕ :=
  (range M).filter fun i => p.1 + i * p.2 ∈ S

/-- The starts of one fixed step, as pairs. -/
private def windowSlice (M N s : ℕ) : Finset (ℕ × ℕ) :=
  (range (N - (M - 1) * s)).map
    ⟨fun t => (t, s), fun _ _ h => congrArg Prod.fst h⟩

/-- Slices of distinct steps are disjoint. -/
private lemma windowSlice_pairwise (M N : ℕ) :
    (Set.univ : Set ℕ).PairwiseDisjoint (windowSlice M N) := by
  intro s _ t _ hst
  change Disjoint (windowSlice M N s) (windowSlice M N t)
  rw [Finset.disjoint_left]
  intro p hp hq
  obtain ⟨t1, -, rfl⟩ := Finset.mem_map.mp hp
  obtain ⟨t2, -, ht⟩ := Finset.mem_map.mp hq
  exact hst (congrArg Prod.snd ht).symm

/-- Every admissible window belongs to the slice of its step. -/
private lemma windowParams_eq_biUnion (M N R : ℕ) :
    windowParams M N R = (Icc 1 R).biUnion (windowSlice M N) := by
  ext p
  constructor
  · intro hp
    simp only [windowParams, mem_filter, mem_product] at hp
    obtain ⟨⟨ht, hs⟩, hfit⟩ := hp
    rw [mem_biUnion]
    refine ⟨p.2, hs, ?_⟩
    rw [windowSlice, Finset.mem_map]
    refine ⟨p.1, ?_, rfl⟩
    rw [mem_range] at ht ⊢
    exact Nat.lt_sub_of_add_lt hfit
  · intro hp
    rw [mem_biUnion] at hp
    obtain ⟨s, hs, hp⟩ := hp
    rw [windowSlice, Finset.mem_map] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    simp only [windowParams, mem_filter, mem_product, mem_range] at ht ⊢
    refine ⟨⟨?_, hs⟩, ?_⟩
    · exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (Nat.add_lt_of_lt_sub ht)
    · exact Nat.add_lt_of_lt_sub ht

/-- The number of windows is the sum, over steps, of the number of admissible starts. -/
private lemma card_windowParams (M N R : ℕ) :
    (windowParams M N R).card = ∑ s ∈ Icc 1 R, (N - (M - 1) * s) := by
  have hpw : ((Icc 1 R) : Set ℕ).PairwiseDisjoint (windowSlice M N) :=
    Set.PairwiseDisjoint.subset (windowSlice_pairwise M N) (Set.subset_univ _)
  rw [windowParams_eq_biUnion, card_biUnion hpw]
  refine sum_congr rfl fun s _ => ?_
  rw [windowSlice, card_map, card_range]

/-- If every step up to `R` advances by at most `bnd`, at least `R * (N - bnd)` windows exist. -/
private lemma card_windowParams_ge {M N R bnd : ℕ}
    (hstep : ∀ s, s ≤ R → (M - 1) * s ≤ bnd) (_hbnd : bnd ≤ N) :
    R * (N - bnd) ≤ (windowParams M N R).card := by
  rw [card_windowParams]
  have hcard : #(Icc 1 R) = R := by rw [Nat.card_Icc]; omega
  have hsum : ∑ s ∈ Icc 1 R, (N - bnd) = #(Icc 1 R) * (N - bnd) :=
    sum_const_nat (fun _ _ => rfl)
  calc
    R * (N - bnd) = ∑ s ∈ Icc 1 R, (N - bnd) := by rw [hsum, hcard]
    _ ≤ ∑ s ∈ Icc 1 R, (N - (M - 1) * s) := by
      refine sum_le_sum fun s hs => ?_
      have hmul : (M - 1) * s ≤ bnd := hstep s (mem_Icc.mp hs).2
      exact Nat.sub_le_sub_left hmul N

/-- The window count is at most `R * N`. -/
private lemma card_windowParams_le (M N R : ℕ) :
    (windowParams M N R).card ≤ R * N := by
  rw [card_windowParams]
  have hcard : #(Icc 1 R) = R := by rw [Nat.card_Icc]; omega
  calc
    ∑ s ∈ Icc 1 R, (N - (M - 1) * s) ≤ ∑ s ∈ Icc 1 R, N := by
      refine sum_le_sum fun _ _ => Nat.sub_le _ _
    _ = R * N := by rw [sum_const_nat (fun _ _ => rfl), hcard]

/-- A short step from a divisor of `bnd` stays inside `bnd`. -/
private lemma step_mul_le {M bnd s R : ℕ} (hR : R = bnd / M) (hs : s ≤ R) :
    (M - 1) * s ≤ bnd := by
  calc
    (M - 1) * s ≤ (M - 1) * R := Nat.mul_le_mul_left _ hs
    _ = (M - 1) * (bnd / M) := by rw [hR]
    _ ≤ M * (bnd / M) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ = bnd / M * M := Nat.mul_comm _ _
    _ ≤ bnd := Nat.div_mul_le_self _ _

/-- A point of the middle interval lies on a window of every admissible step and offset. -/
private lemma middle_windows {M N bnd R : ℕ} (hR : R = bnd / M) (_hbnd : bnd ≤ N)
    {y i s : ℕ} (hy1 : bnd ≤ y) (hy2 : y + bnd < N) (hyN : y < N)
    (hi : i < M) (hs : s ∈ Icc 1 R) :
    i * s ≤ y ∧ y - i * s + (M - 1) * s < N ∧
      (y - i * s, s) ∈ windowParams M N R := by
  have hsR : s ≤ R := (mem_Icc.mp hs).2
  have hmul : (M - 1) * s ≤ bnd := step_mul_le hR hsR
  have hi_le : i ≤ M - 1 := Nat.le_sub_one_of_lt hi
  have his_le : i * s ≤ (M - 1) * s := Nat.mul_le_mul_right _ hi_le
  have hys : i * s ≤ y := his_le.trans (hmul.trans hy1)
  have hsum : y + (M - 1) * s < N := by
    exact (Nat.add_le_add_left hmul y).trans_lt hy2
  have heq : y - i * s + (M - 1) * s = y + ((M - 1) * s - i * s) := by
    calc
      y - i * s + (M - 1) * s
          = y - i * s + (i * s + ((M - 1) * s - i * s)) := by
            congr 1
            exact (Nat.add_sub_of_le his_le).symm
      _ = y - i * s + i * s + ((M - 1) * s - i * s) := by rw [← Nat.add_assoc]
      _ = y + ((M - 1) * s - i * s) := by rw [Nat.sub_add_cancel hys]
  have hfit : y - i * s + (M - 1) * s < N := by
    rw [heq]
    exact (Nat.add_le_add_left (Nat.sub_le _ _) y).trans_lt hsum
  refine ⟨hys, hfit, ?_⟩
  refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr ?_, hs⟩, hfit⟩
  exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hyN

/-- Hits along a window are indices in `{0, …, M - 1}`. -/
private lemma windowHits_subset (S : Finset ℕ) (M : ℕ) (p : ℕ × ℕ) :
    windowHits S M p ⊆ range M :=
  filter_subset _ _

/-- An index progression in a window produces an ambient progression in `S`. -/
private lemma ambient_of_window {S : Finset ℕ} {M N R t s i u : ℕ}
    (hw : (t, s) ∈ windowParams M N R) (hu : 0 < u) (hiu : i + 2 * u < M)
    (hi : i ∈ windowHits S M (t, s)) (hmid : i + u ∈ windowHits S M (t, s))
    (hend : i + 2 * u ∈ windowHits S M (t, s)) :
    0 < u * s ∧ t + i * s + 2 * (u * s) < N ∧ t + i * s ∈ S ∧
      t + i * s + u * s ∈ S ∧ t + i * s + 2 * (u * s) ∈ S := by
  have hs0 : 0 < s := (mem_Icc.mp (mem_product.mp (mem_filter.mp hw).1).2).1
  have hd : 0 < u * s := Nat.mul_pos hu hs0
  have hfit : t + (M - 1) * s < N := (mem_filter.mp hw).2
  have hpoint (j) (hj : j ∈ windowHits S M (t, s)) : t + j * s ∈ S := (mem_filter.mp hj).2
  have heq2 : t + i * s + 2 * (u * s) = t + (i + 2 * u) * s := by ring
  have heq1 : t + i * s + u * s = t + (i + u) * s := by ring
  have hle : (i + 2 * u) * s ≤ (M - 1) * s :=
    Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt hiu)
  have hlt : t + i * s + 2 * (u * s) < N := by
    rw [heq2]
    exact (Nat.add_le_add_left hle t).trans_lt hfit
  refine ⟨hd, hlt, hpoint i hi, ?_, ?_⟩
  · rw [heq1]; exact hpoint (i + u) hmid
  · rw [heq2]; exact hpoint (i + 2 * u) hend

/-- Indices of a nontrivial 3-term progression inside `{0, …, M - 1}`. -/
private structure IndexAP (M : ℕ) where
  i : ℕ
  u : ℕ
  hu : 0 < u
  hiu : i + 2 * u < M

/-- A window whose hit set exceeds the Roth number carries a 3-term progression of `S`. -/
private lemma exists_indexAP_of_window {S : Finset ℕ} {M N R : ℕ} {δ : ℝ}
    (hroth : (rothNumberNat M : ℝ) ≤ (δ / 8) * (M : ℝ)) (hM : 1 ≤ M)
    {p : ℕ × ℕ} (hp : p ∈ windowParams M N R)
    (hhits : Nat.ceil ((δ / 4) * (M : ℝ)) ≤ (windowHits S M p).card) :
    ∃ w : IndexAP M, 0 < p.2 ∧ 0 < w.u * p.2 ∧
      p.1 + w.i * p.2 + 2 * (w.u * p.2) < N ∧ p.1 + w.i * p.2 ∈ S ∧
      p.1 + w.i * p.2 + w.u * p.2 ∈ S ∧
      p.1 + w.i * p.2 + 2 * (w.u * p.2) ∈ S := by
  let B := windowHits S M p
  have hgt : rothNumberNat M < B.card := by
    have h2 : (2 * rothNumberNat M : ℝ) ≤ (B.card : ℝ) := by
      calc
        (2 * rothNumberNat M : ℝ) = 2 * (rothNumberNat M : ℝ) := rfl
        _ ≤ 2 * ((δ / 8) * (M : ℝ)) := by gcongr
        _ = (δ / 4) * (M : ℝ) := by ring
        _ ≤ (Nat.ceil ((δ / 4) * (M : ℝ)) : ℝ) := Nat.le_ceil _
        _ ≤ (B.card : ℝ) := by exact_mod_cast hhits
    have hnat : 2 * rothNumberNat M ≤ B.card := by exact_mod_cast h2
    have hone : 1 ≤ rothNumberNat M := one_le_rothNumberNat hM
    omega
  obtain ⟨i, u, hu, hiu, hi, hmid, hend⟩ :=
    exists_threeAP_of_gt_roth (windowHits_subset S M p) hgt
  have hs0 : 0 < p.2 := (mem_Icc.mp (mem_product.mp (mem_filter.mp hp).1).2).1
  have hamb := ambient_of_window hp hu hiu hi hmid hend
  exact ⟨⟨i, u, hu, hiu⟩, hs0, hamb⟩

/-- Comparing a hit-sum with a cap on the poor windows produces many rich windows. -/
private lemma good_ratio {δ M cap P G H : ℝ} (hM : 0 < M) (_hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hcap : cap < (δ / 4) * M) (hsum : (δ / 2) * M * P ≤ H)
    (hbound : H ≤ G * M + (P - G) * cap) :
    ((δ / 2) * M - cap) / (M - cap) * P ≤ G := by
  have hden : 0 < M - cap := by
    have hM4 : (δ / 4) * M ≤ M / 4 := by nlinarith [hδ1, hM]
    linarith [hcap, hM4]
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  linarith [hsum, hbound]

/-- Points of `S` outside the middle interval of width `bnd`. -/
private lemma outside_card_le {N bnd : ℕ} (S : Finset ℕ) (hS : S ⊆ range N) (hbnd : bnd ≤ N) :
    #(S.filter fun y => ¬ (bnd ≤ y ∧ y + bnd < N)) ≤ 2 * bnd := by
  have hpred : ∀ y, ¬ (bnd ≤ y ∧ y + bnd < N) ↔ y < bnd ∨ N ≤ y + bnd := by
    intro y
    rw [not_and_or, not_le, not_lt]
  let outside := (range N).filter fun y => y < bnd ∨ N ≤ y + bnd
  have hsub : S.filter (fun y => ¬ (bnd ≤ y ∧ y + bnd < N)) ⊆ outside := by
    intro y hy
    rw [mem_filter] at hy
    exact mem_filter.mpr ⟨hS hy.1, (hpred y).mp hy.2⟩
  have hleft : #((range N).filter fun y => y < bnd) = bnd := by
    have : (range N).filter (fun y => y < bnd) = range bnd := by
      ext y
      simp only [mem_filter, mem_range]
      constructor
      · intro hy
        exact hy.2
      · intro hy
        exact ⟨hy.trans_le hbnd, hy⟩
    simp [this, card_range]
  have hright : #((range N).filter fun y => N ≤ y + bnd) = bnd := by
    have : (range N).filter (fun y => N ≤ y + bnd) = Ico (N - bnd) N := by
      ext y
      simp only [mem_filter, mem_range, mem_Ico]
      constructor
      · intro ⟨hyN, hyb⟩
        exact ⟨by omega, hyN⟩
      · intro ⟨hyl, hyN⟩
        exact ⟨hyN, by omega⟩
    rw [this, Nat.card_Ico, Nat.sub_sub_self hbnd]
  have hunion :
      outside ⊆ (range N).filter (fun y => y < bnd) ∪
        (range N).filter fun y => N ≤ y + bnd := by
    intro y hy
    rw [mem_union, mem_filter, mem_filter]
    rw [mem_filter] at hy
    rcases hy.2 with hlt | hge
    · exact Or.inl ⟨hy.1, hlt⟩
    · exact Or.inr ⟨hy.1, hge⟩
  calc
    #(S.filter fun y => ¬ (bnd ≤ y ∧ y + bnd < N)) ≤ #outside := card_le_card hsub
    _ ≤ #((range N).filter fun y => y < bnd) +
        #((range N).filter fun y => N ≤ y + bnd) := (card_le_card hunion).trans (card_union_le _ _)
    _ = 2 * bnd := by omega

/-- Each middle point of `S` sits on `M * R` windows, at distinct hit indices. -/
private lemma incidence_ge {S : Finset ℕ} {M N bnd R : ℕ} (hR : R = bnd / M) (hbnd : bnd ≤ N)
    (middle : Finset ℕ) (hmiddle : middle ⊆ S) (hmidN : middle ⊆ range N)
    (hmem : ∀ y ∈ middle, bnd ≤ y ∧ y + bnd < N) :
    middle.card * M * #(Icc 1 R) ≤
      ∑ p ∈ windowParams M N R, (windowHits S M p).card := by
  let trips := middle ×ˢ (range M ×ˢ Icc 1 R)
  let σ := (windowParams M N R).sigma fun p => windowHits S M p
  have hσ : #σ = ∑ p ∈ windowParams M N R, (windowHits S M p).card := by
    rw [card_eq_sum_ones, sum_sigma]
    refine sum_congr rfl fun _ _ => (card_eq_sum_ones _).symm
  have htrips : #trips = middle.card * M * #(Icc 1 R) := by
    rw [card_product, card_product, card_range, mul_assoc]
  rw [← htrips, ← hσ]
  let φ : ℕ × (ℕ × ℕ) → Σ _ : ℕ × ℕ, ℕ :=
    fun yis => ⟨(yis.1 - yis.2.1 * yis.2.2, yis.2.2), yis.2.1⟩
  refine card_le_card_of_injOn (s := trips) (t := σ) φ ?_ ?_
  · intro yis hyis
    rw [mem_coe, mem_product] at hyis
    obtain ⟨hy, hi⟩ := hyis
    rw [mem_product] at hi
    obtain ⟨hiM, hs⟩ := hi
    rw [mem_range] at hiM
    have hyN : yis.1 < N := mem_range.mp (hmidN hy)
    have hybnd := hmem _ hy
    have hw := middle_windows hR hbnd hybnd.1 hybnd.2 hyN hiM hs
    rw [mem_coe, mem_sigma]
    refine ⟨hw.2.2, ?_⟩
    rw [windowHits, mem_filter, mem_range]
    refine ⟨hiM, ?_⟩
    have hcancel : yis.1 - yis.2.1 * yis.2.2 + yis.2.1 * yis.2.2 = yis.1 :=
      Nat.sub_add_cancel hw.1
    rw [hcancel]
    exact hmiddle hy
  · intro yis hyis yis' hyis' heq
    rw [mem_coe] at hyis hyis'
    have hwit (z) (hz : z ∈ trips) :
        z.2.1 * z.2.2 ≤ z.1 := by
      rw [mem_product] at hz
      obtain ⟨hy, hi⟩ := hz
      rw [mem_product] at hi
      obtain ⟨hiM, hs⟩ := hi
      rw [mem_range] at hiM
      exact (middle_windows hR hbnd (hmem _ hy).1 (hmem _ hy).2 (mem_range.mp (hmidN hy))
        hiM hs).1
    have hpair := congrArg Sigma.fst heq
    have hidx := congrArg Sigma.snd heq
    dsimp [φ] at hpair hidx
    obtain ⟨ht0, hs0⟩ := Prod.ext_iff.mp hpair
    have ht : yis.1 - yis.2.1 * yis.2.2 = yis'.1 - yis'.2.1 * yis'.2.2 := by
      change _ = _ at ht0
      exact ht0
    have hs : yis.2.2 = yis'.2.2 := by
      change _ = _ at hs0
      exact hs0
    have hi : yis.2.1 = yis'.2.1 := hidx
    have hy : yis.1 = yis.1 - yis.2.1 * yis.2.2 + yis.2.1 * yis.2.2 :=
      (Nat.sub_add_cancel (hwit yis hyis)).symm
    have hy' : yis'.1 = yis'.1 - yis'.2.1 * yis'.2.2 + yis'.2.1 * yis'.2.2 :=
      (Nat.sub_add_cancel (hwit yis' hyis')).symm
    refine Prod.ext ?_ (Prod.ext hi hs)
    calc
      yis.1 = yis.1 - yis.2.1 * yis.2.2 + yis.2.1 * yis.2.2 := hy
      _ = yis'.1 - yis'.2.1 * yis'.2.2 + yis.2.1 * yis.2.2 := by rw [ht]
      _ = yis'.1 - yis'.2.1 * yis'.2.2 + yis'.2.1 * yis'.2.2 := by rw [hi, hs]
      _ = yis'.1 := hy'.symm

/-- Positive-density subsets of long intervals contain quadratically many 3-term progressions. -/
private lemma numerous_progression_three {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ S : Finset ℕ,
      S ⊆ range N → δ * (N : ℝ) ≤ (S.card : ℝ) →
      c * (N : ℝ) ^ 2 ≤ (progressionCount 3 N S : ℝ) := by
  by_cases hδ1 : 1 < δ
  · refine ⟨1, by positivity, 1, ?_⟩
    intro N hN S hS hdense
    have hcard : (S.card : ℝ) ≤ N := by
      exact_mod_cast card_le_card hS |>.trans_eq (card_range N)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.succ_le_iff.mp hN
    have hlt : (N : ℝ) < δ * N := by nlinarith
    exact absurd (hdense.trans hcard) hlt.not_ge
  · have hδle : δ ≤ 1 := le_of_not_gt hδ1
    obtain ⟨M, hM, hroth⟩ := exists_roth_scale (show 0 < δ / 8 by positivity)
    have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.succ_le_iff.mp hM
    let η : ℝ := δ / 4
    have hη : 0 < η := by positivity
    let cap : ℝ := (Nat.ceil ((δ / 4) * (M : ℝ)) : ℝ) - 1
    have hcap : cap < (δ / 4) * (M : ℝ) := by
      have hnonneg : 0 ≤ (δ / 4) * (M : ℝ) := by positivity
      linarith [Nat.ceil_lt_add_one hnonneg]
    let c0 : ℝ := ((δ / 2) * (M : ℝ) - cap) / ((M : ℝ) - cap)
    let c : ℝ := c0 * η / (8 * (M : ℝ) ^ 3)
    have hc0 : 0 < c0 := by
      have hden : 0 < (M : ℝ) - cap := by
        have hfrac : (δ / 4) * (M : ℝ) ≤ (M : ℝ) / 4 := by nlinarith
        linarith
      have hnum : 0 < (δ / 2) * (M : ℝ) - cap := by linarith
      exact div_pos hnum hden
    have hc : 0 < c := by positivity
    let N0 : ℕ := Nat.ceil ((4 * (M : ℝ)) / η)
    refine ⟨c, hc, N0, ?_⟩
    intro N hN S hS hdense
    have hNpos : (0 : ℝ) < N := by
      have hN0 : 0 < N0 := by
        have : (0 : ℝ) < (4 * (M : ℝ)) / η := by positivity
        exact Nat.ceil_pos.mpr this
      exact_mod_cast lt_of_lt_of_le hN0 hN
    have hscale : 4 * (M : ℝ) ≤ η * N := by
      have hceil : (4 * (M : ℝ)) / η ≤ (N0 : ℝ) := Nat.le_ceil _
      have hcast : (N0 : ℝ) ≤ N := by exact_mod_cast hN
      have hmul : 4 * (M : ℝ) ≤ (N : ℝ) * η := (div_le_iff₀ hη).mp (hceil.trans hcast)
      rw [mul_comm (N : ℝ) η] at hmul
      exact hmul
    let bnd : ℕ := Nat.floor (η * N)
    let R : ℕ := bnd / M
    have hbndR : (bnd : ℝ) ≤ η * N := Nat.floor_le (by positivity)
    have hηle : η ≤ 1 / 4 := by
      dsimp [η]
      nlinarith [hδle]
    have hbndN : bnd ≤ N := by
      have : (bnd : ℝ) ≤ N := hbndR.trans (by nlinarith [hηle])
      exact_mod_cast this
    have hRdef : R = bnd / M := rfl
    have hstep : ∀ s, s ≤ R → (M - 1) * s ≤ bnd := fun s hs => step_mul_le hRdef hs
    let middle := S.filter fun y => bnd ≤ y ∧ y + bnd < N
    have hmidS : middle ⊆ S := filter_subset _ _
    have hmidN : middle ⊆ range N := hmidS.trans hS
    have hmidmem : ∀ y ∈ middle, bnd ≤ y ∧ y + bnd < N := by
      intro y hy
      exact (mem_filter.mp hy).2
    have hsplit := card_filter_add_card_filter_not (s := S)
      (fun y => bnd ≤ y ∧ y + bnd < N)
    have hout := outside_card_le S hS hbndN
    have hmidreal : (δ / 2) * N ≤ (middle.card : ℝ) := by
      have hsum : (S.card : ℝ) = (middle.card : ℝ) +
          ((S.filter fun y => ¬ (bnd ≤ y ∧ y + bnd < N)).card : ℝ) := by
        exact_mod_cast hsplit.symm
      have houtR : ((S.filter fun y => ¬ (bnd ≤ y ∧ y + bnd < N)).card : ℝ) ≤
          2 * (bnd : ℝ) := by exact_mod_cast hout
      dsimp [η] at hbndR
      nlinarith [hdense, hbndR]
    have hinc := incidence_ge (S := S) hRdef hbndN middle hmidS hmidN hmidmem
    have hIcc : #(Icc 1 R) = R := by rw [Nat.card_Icc, Nat.add_sub_cancel]
    have hinc' : middle.card * M * R ≤
        ∑ p ∈ windowParams M N R, (windowHits S M p).card := by
      rwa [hIcc] at hinc
    let H : ℝ := ∑ p ∈ windowParams M N R, ((windowHits S M p).card : ℝ)
    have hH : (middle.card : ℝ) * (M : ℝ) * (R : ℝ) ≤ H := by
      have hcast := (Nat.cast_le (α := ℝ)).mpr hinc'
      have hleft : ↑(middle.card * M * R) =
          (middle.card : ℝ) * (M : ℝ) * (R : ℝ) := by simp only [Nat.cast_mul]
      have hright : ↑(∑ p ∈ windowParams M N R, (windowHits S M p).card) = H := by
        rw [Nat.cast_sum]
      rw [hleft, hright] at hcast
      exact hcast
    have hHδ : (δ / 2) * (N : ℝ) * (M : ℝ) * (R : ℝ) ≤ H := by
      have hnonneg : (0 : ℝ) ≤ (M : ℝ) * (R : ℝ) := by positivity
      have hmul : (δ / 2) * (N : ℝ) * ((M : ℝ) * (R : ℝ)) ≤
          (middle.card : ℝ) * ((M : ℝ) * (R : ℝ)) :=
        mul_le_mul_of_nonneg_right hmidreal hnonneg
      have hre1 : (δ / 2) * (N : ℝ) * ((M : ℝ) * (R : ℝ)) =
          (δ / 2) * (N : ℝ) * (M : ℝ) * (R : ℝ) := by ring
      have hre2 : (middle.card : ℝ) * ((M : ℝ) * (R : ℝ)) =
          (middle.card : ℝ) * (M : ℝ) * (R : ℝ) := by ring
      rw [hre1, hre2] at hmul
      exact hmul.trans hH
    have hPle : (windowParams M N R).card ≤ R * N := card_windowParams_le M N R
    let P : ℝ := (windowParams M N R).card
    have hPR : P ≤ (R : ℝ) * (N : ℝ) := by
      have hcast : ((windowParams M N R).card : ℝ) ≤ ((R * N : ℕ) : ℝ) :=
        Nat.cast_le.mpr hPle
      rwa [Nat.cast_mul] at hcast
    have hPδ : (δ / 2) * (M : ℝ) * P ≤ H := by
      calc
        (δ / 2) * (M : ℝ) * P ≤ (δ / 2) * (M : ℝ) * ((R : ℝ) * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hPR (by positivity)
        _ = (δ / 2) * (N : ℝ) * (M : ℝ) * (R : ℝ) := by ring
        _ ≤ H := hHδ
    let threshold : ℕ := Nat.ceil ((δ / 4) * (M : ℝ))
    have hthreshold : 1 ≤ threshold := by
      have : 0 < (δ / 4) * (M : ℝ) := by positivity
      exact Nat.one_le_of_lt (Nat.ceil_pos.mpr this)
    let good := (windowParams M N R).filter fun p =>
      threshold ≤ (windowHits S M p).card
    let bad := (windowParams M N R).filter fun p =>
      ¬ threshold ≤ (windowHits S M p).card
    have hdisj : Disjoint good bad := disjoint_filter_filter_not _ _ _
    have hunion : good ∪ bad = windowParams M N R :=
      filter_union_filter_not_eq
        (p := fun q => threshold ≤ (windowHits S M q).card) (windowParams M N R)
    have hsumH : H = ∑ p ∈ good, ((windowHits S M p).card : ℝ) +
        ∑ p ∈ bad, ((windowHits S M p).card : ℝ) := by
      rw [← Finset.sum_union hdisj, hunion]
    have hgoodle : ∑ p ∈ good, ((windowHits S M p).card : ℝ) ≤ (good.card : ℝ) * M := by
      calc
        ∑ p ∈ good, ((windowHits S M p).card : ℝ) ≤ ∑ p ∈ good, (M : ℝ) := by
          refine sum_le_sum fun p hp => ?_
          have hsub : windowHits S M p ⊆ range M := windowHits_subset S M p
          exact_mod_cast card_le_card hsub |>.trans_eq (card_range M)
        _ = (good.card : ℝ) * M := by rw [sum_const, nsmul_eq_mul]
    have hbadle : ∑ p ∈ bad, ((windowHits S M p).card : ℝ) ≤ (bad.card : ℝ) * cap := by
      calc
        ∑ p ∈ bad, ((windowHits S M p).card : ℝ) ≤ ∑ p ∈ bad, cap := by
          refine sum_le_sum fun p hp => ?_
          have hlt : (windowHits S M p).card ≤ threshold - 1 := by
            have hnot : (windowHits S M p).card < threshold :=
              Nat.lt_of_not_ge (mem_filter.mp hp).2
            omega
          have hcap' : ((threshold - 1 : ℕ) : ℝ) = cap := by
            rw [Nat.cast_sub hthreshold, Nat.cast_one]
          have hreal : ((windowHits S M p).card : ℝ) ≤ ((threshold - 1 : ℕ) : ℝ) :=
            Nat.cast_le.mpr hlt
          exact hreal.trans_eq hcap'
        _ = (bad.card : ℝ) * cap := by
          rw [sum_const]
          simp [nsmul_eq_mul]
    have hbadcard : (bad.card : ℝ) = P - (good.card : ℝ) := by
      have hadd : good.card + bad.card = (windowParams M N R).card := by
        rw [← card_union_of_disjoint hdisj, hunion]
      have hnat : bad.card = (windowParams M N R).card - good.card :=
        Nat.eq_sub_of_add_eq' hadd
      have hgle : good.card ≤ (windowParams M N R).card := by
        rw [← hadd]
        exact Nat.le_add_right _ _
      have hcast := congrArg (Nat.cast : ℕ → ℝ) hnat
      rwa [Nat.cast_sub hgle] at hcast
    let G : ℝ := good.card
    have hbound : H ≤ G * (M : ℝ) + (P - G) * cap := by
      rw [hsumH]
      calc
        ∑ p ∈ good, ((windowHits S M p).card : ℝ) +
            ∑ p ∈ bad, ((windowHits S M p).card : ℝ) ≤
            (good.card : ℝ) * (M : ℝ) + (bad.card : ℝ) * cap :=
          add_le_add hgoodle hbadle
        _ = G * (M : ℝ) + (P - G) * cap := by rw [hbadcard]
    have hratio := good_ratio hMpos hδ hδle hcap hPδ hbound
    have hfloor : η * N - 1 < (bnd : ℝ) := by
      have := Nat.lt_floor_add_one (η * N)
      linarith
    have hbndhalf : η * (N : ℝ) / 2 ≤ (bnd : ℝ) := by
      have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
      have h4 : (4 : ℝ) ≤ η * (N : ℝ) := by
        have hmul : (4 : ℝ) * 1 ≤ 4 * (M : ℝ) :=
          mul_le_mul_of_nonneg_left hM1 (by norm_num)
        linarith [hscale]
      have htwo : (2 : ℝ) ≤ η * (N : ℝ) := by linarith
      have hlow : η * (N : ℝ) / 2 ≤ η * (N : ℝ) - 1 := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
        linarith
      exact hlow.trans (le_of_lt hfloor)
    have hx : (2 : ℝ) ≤ (bnd : ℝ) / M := by
      rw [le_div_iff₀ hMpos]
      nlinarith [hbndhalf, hscale, hMpos]
    have hRreal : (bnd : ℝ) / (2 * M) ≤ R := by
      have hM0 : 0 < M := Nat.succ_le_iff.mp hM
      have hlt : bnd < M * (R + 1) := by simpa [hRdef] using Nat.lt_mul_div_succ bnd hM0
      have hcast : (bnd : ℝ) < (M : ℝ) * ((R : ℝ) + 1) := by exact_mod_cast hlt
      have hsub : (bnd : ℝ) / M - 1 < R := by
        have hdiv : (bnd : ℝ) / M < (R : ℝ) + 1 := by rwa [div_lt_iff₀ hMpos, mul_comm]
        linarith
      have hhalf : (bnd : ℝ) / (2 * M) ≤ (bnd : ℝ) / M - 1 := by
        have heq : (bnd : ℝ) / (2 * M) = (bnd : ℝ) / M / 2 := by
          rw [show (2 : ℝ) * M = M * 2 by ring, ← div_div]
        rw [heq]
        linarith [hx]
      exact le_of_lt (lt_of_le_of_lt hhalf hsub)
    have hPge : R * (N - bnd) ≤ (windowParams M N R).card :=
      card_windowParams_ge hstep hbndN
    have hNsub : (N : ℝ) / 2 ≤ ↑(N - bnd) := by
      rw [Nat.cast_sub hbndN, le_sub_iff_add_le]
      have hbnd4 : (bnd : ℝ) ≤ (N : ℝ) / 4 := by
        have hηN : η * (N : ℝ) ≤ (1 / 4) * (N : ℝ) :=
          mul_le_mul_of_nonneg_right hηle (by positivity)
        linarith [hbndR]
      have hsum : (N : ℝ) / 2 + (N : ℝ) / 4 ≤ N := by
        have hre : (N : ℝ) / 2 + (N : ℝ) / 4 = (3 / 4) * N := by ring
        have h34 : (3 / 4 : ℝ) ≤ 1 := by norm_num
        have hmul : (3 / 4) * (N : ℝ) ≤ 1 * (N : ℝ) :=
          mul_le_mul_of_nonneg_right h34 (by positivity)
        linarith
      linarith
    have hRcast : (R : ℝ) * ↑(N - bnd) ≤ P := by
      have hle : ((R * (N - bnd) : ℕ) : ℝ) ≤ P := Nat.cast_le.mpr hPge
      simpa [Nat.cast_mul] using hle
    have hRlow : η * (N : ℝ) / (4 * (M : ℝ)) ≤ (R : ℝ) := by
      have hre : η * (N : ℝ) / (4 * (M : ℝ)) =
          (η * (N : ℝ) / 2) / (2 * (M : ℝ)) := by ring
      have hdiv : (η * (N : ℝ) / 2) / (2 * (M : ℝ)) ≤
          (bnd : ℝ) / (2 * (M : ℝ)) :=
        div_le_div_of_nonneg_right hbndhalf (by positivity)
      rw [hre]
      exact hdiv.trans hRreal
    have hPquad : η * (N : ℝ) ^ 2 / (8 * (M : ℝ)) ≤ P := by
      have hre : η * (N : ℝ) ^ 2 / (8 * (M : ℝ)) =
          (η * (N : ℝ) / (4 * (M : ℝ))) * ((N : ℝ) / 2) := by ring
      have hmul : (η * (N : ℝ) / (4 * (M : ℝ))) * ((N : ℝ) / 2) ≤
          (R : ℝ) * ↑(N - bnd) :=
        mul_le_mul hRlow hNsub (by positivity) (by positivity)
      rw [← hre] at hmul
      exact hmul.trans hRcast
    have hG : c0 * η * (N : ℝ) ^ 2 / (8 * (M : ℝ)) ≤ G := by
      have hratio' : c0 * P ≤ G := hratio
      have hmul : c0 * (η * (N : ℝ) ^ 2 / (8 * (M : ℝ))) ≤ c0 * P :=
        mul_le_mul_of_nonneg_left hPquad hc0.le
      have hre : c0 * (η * (N : ℝ) ^ 2 / (8 * (M : ℝ))) =
          c0 * η * (N : ℝ) ^ 2 / (8 * (M : ℝ)) := by ring
      rw [hre] at hmul
      exact hmul.trans hratio'
    have hprog : ∀ p ∈ good, ∃ w : IndexAP M, 0 < p.2 ∧ 0 < w.u * p.2 ∧
        p.1 + w.i * p.2 + 2 * (w.u * p.2) < N ∧ p.1 + w.i * p.2 ∈ S ∧
        p.1 + w.i * p.2 + w.u * p.2 ∈ S ∧
        p.1 + w.i * p.2 + 2 * (w.u * p.2) ∈ S := by
      intro p hp
      exact exists_indexAP_of_window hroth hM (mem_filter.mp hp).1 (mem_filter.mp hp).2
    let f : ℕ × ℕ → ℕ × ℕ := fun p =>
      if h : p ∈ good then
        let w := Classical.choose (hprog p h)
        (p.1 + w.i * p.2, w.u * p.2)
      else
        (0, 0)
    have hfiber : ∀ q ∈ good.image f, #{p ∈ good | f p = q} ≤ M * M := by
      intro q hq
      let fiber := good.filter fun p => f p = q
      let ψ : ℕ × ℕ → ℕ × ℕ := fun p =>
        ((q.1 - p.1) / p.2, q.2 / p.2)
      suffices #fiber ≤ M * M by simpa [fiber] using this
      calc
        #fiber ≤ #(range M ×ˢ range M) :=
          card_le_card_of_injOn (s := fiber) (t := range M ×ˢ range M) ψ ?_ ?_
        _ = M * M := by rw [card_product, card_range]
      · intro p hp
        rw [mem_coe] at hp
        have hpg : p ∈ good := (mem_filter.mp hp).1
        have hfeq : f p = q := (mem_filter.mp hp).2
        have hw := Classical.choose_spec (hprog p hpg)
        have hdif : f p = (p.1 + (Classical.choose (hprog p hpg)).i * p.2,
            (Classical.choose (hprog p hpg)).u * p.2) := by simp [f, hpg]
        rw [hfeq] at hdif
        have hs0 : 0 < p.2 := hw.1
        have hi : (q.1 - p.1) / p.2 = (Classical.choose (hprog p hpg)).i := by
          have ha : q.1 = p.1 + (Classical.choose (hprog p hpg)).i * p.2 :=
            congrArg Prod.fst hdif
          rw [ha, Nat.add_sub_cancel_left, Nat.mul_div_cancel _ hs0]
        have hu : q.2 / p.2 = (Classical.choose (hprog p hpg)).u := by
          have hd : q.2 = (Classical.choose (hprog p hpg)).u * p.2 := congrArg Prod.snd hdif
          rw [hd, Nat.mul_div_cancel _ hs0]
        rw [mem_coe, mem_product]
        dsimp [ψ]
        rw [hi, hu, mem_range, mem_range]
        have hiu := (Classical.choose (hprog p hpg)).hiu
        have hu0 := (Classical.choose (hprog p hpg)).hu
        constructor
        · exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hiu
        · exact Nat.lt_of_le_of_lt
            ((Nat.le_mul_of_pos_left _ (by decide : 0 < 2)).trans
              (Nat.le_add_left _ _)) hiu
      · intro p hp p' hp' heq
        rw [mem_coe] at hp hp'
        have hpg : p ∈ good := (mem_filter.mp hp).1
        have hpg' : p' ∈ good := (mem_filter.mp hp').1
        have hfeq : f p = q := (mem_filter.mp hp).2
        have hfeq' : f p' = q := (mem_filter.mp hp').2
        have hw := Classical.choose_spec (hprog p hpg)
        have hw' := Classical.choose_spec (hprog p' hpg')
        set w := Classical.choose (hprog p hpg)
        set w' := Classical.choose (hprog p' hpg')
        have hdif : q = (p.1 + w.i * p.2, w.u * p.2) := by
          have : f p = (p.1 + w.i * p.2, w.u * p.2) := by simp [f, hpg, w]
          rw [← this, hfeq]
        have hdif' : q = (p'.1 + w'.i * p'.2, w'.u * p'.2) := by
          have : f p' = (p'.1 + w'.i * p'.2, w'.u * p'.2) := by simp [f, hpg', w']
          rw [← this, hfeq']
        have hi : (q.1 - p.1) / p.2 = w.i := by
          have ha : q.1 = p.1 + w.i * p.2 := congrArg Prod.fst hdif
          rw [ha, Nat.add_sub_cancel_left, Nat.mul_div_cancel _ hw.1]
        have hu : q.2 / p.2 = w.u := by
          have hd : q.2 = w.u * p.2 := congrArg Prod.snd hdif
          rw [hd, Nat.mul_div_cancel _ hw.1]
        have hi' : (q.1 - p'.1) / p'.2 = w'.i := by
          have ha : q.1 = p'.1 + w'.i * p'.2 := congrArg Prod.fst hdif'
          rw [ha, Nat.add_sub_cancel_left, Nat.mul_div_cancel _ hw'.1]
        have hu' : q.2 / p'.2 = w'.u := by
          have hd : q.2 = w'.u * p'.2 := congrArg Prod.snd hdif'
          rw [hd, Nat.mul_div_cancel _ hw'.1]
        have hiu : w.i = w'.i ∧ w.u = w'.u := by
          have hψ := heq
          dsimp only [ψ] at hψ
          refine ⟨?_, ?_⟩
          · exact hi.symm.trans ((congrArg Prod.fst hψ).trans hi')
          · exact hu.symm.trans ((congrArg Prod.snd hψ).trans hu')
        have hs0 : 0 < w.u := w.hu
        have hstep : p.2 = p'.2 := by
          have hleft : q.2 = w.u * p.2 := congrArg Prod.snd hdif
          have hright : q.2 = w.u * p'.2 := by
            have h0 : q.2 = w'.u * p'.2 := congrArg Prod.snd hdif'
            rwa [← hiu.2] at h0
          exact Nat.eq_of_mul_eq_mul_left hs0 (hleft.symm.trans hright)
        have ht : p.1 = p'.1 := by
          have hleft : q.1 = p.1 + w.i * p.2 := congrArg Prod.fst hdif
          have hright : q.1 = p'.1 + w.i * p.2 := by
            have h0 : q.1 = p'.1 + w'.i * p'.2 := congrArg Prod.fst hdif'
            rw [← hiu.1, ← hstep] at h0
            exact h0
          exact Nat.add_right_cancel (hleft.symm.trans hright)
        exact Prod.ext ht hstep
    have himage : good.image f ⊆ (apParams 3 N).filter fun q =>
        ∀ j ∈ range 3, q.1 + j * q.2 ∈ S := by
      intro q hq
      rw [mem_image] at hq
      obtain ⟨p, hp, rfl⟩ := hq
      have hw := Classical.choose_spec (hprog p hp)
      have hfp : f p = (p.1 + (Classical.choose (hprog p hp)).i * p.2,
          (Classical.choose (hprog p hp)).u * p.2) := by simp [f, hp]
      rw [mem_filter]
      refine ⟨?_, ?_⟩
      · rw [apParams, mem_filter, mem_product, hfp]
        set w := Classical.choose (hprog p hp)
        have ha : p.1 + w.i * p.2 < N :=
          Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hw.2.2.1
        have hd : w.u * p.2 < N := by
          have : w.u * p.2 ≤ 2 * (w.u * p.2) := Nat.le_mul_of_pos_left _ (by decide : 0 < 2)
          exact Nat.lt_of_le_of_lt this (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hw.2.2.1)
        refine ⟨⟨mem_range.mpr ha, mem_range.mpr hd⟩, hw.2.1, ?_⟩
        simpa [Nat.mul_comm] using hw.2.2.1
      · intro j hj
        rw [hfp]
        set w := Classical.choose (hprog p hp)
        rw [mem_range] at hj
        interval_cases j
        · simpa using hw.2.2.2.1
        · have : p.1 + w.i * p.2 + 1 * (w.u * p.2) =
              p.1 + w.i * p.2 + w.u * p.2 := by ring
          simpa [this] using hw.2.2.2.2.1
        · simpa using hw.2.2.2.2.2
    have hmul : good.card ≤ M * M * #(good.image f) :=
      card_le_mul_card_image good (M * M) hfiber
    have hcount : #(good.image f) ≤ progressionCount 3 N S := by
      simpa [progressionCount] using card_le_card himage
    have hGcount : G ≤ (M * M : ℝ) * (progressionCount 3 N S : ℝ) := by
      have hnat : good.card ≤ M * M * progressionCount 3 N S :=
        hmul.trans (Nat.mul_le_mul_left _ hcount)
      have hcast := (Nat.cast_le (α := ℝ)).mpr hnat
      have hsplit : ((M * M * progressionCount 3 N S : ℕ) : ℝ) =
          (M : ℝ) * (M : ℝ) * (progressionCount 3 N S : ℝ) := by
        simp only [Nat.cast_mul]
      rw [hsplit] at hcast
      exact hcast
    have hdiv : G / (M * M : ℝ) ≤ progressionCount 3 N S := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < M * M)]
      simpa [mul_comm] using hGcount
    have hfinal : c * N ^ 2 ≤ G / (M * M : ℝ) := by
      have hMpow : (M : ℝ) ^ 3 = M * (M * M) := by ring
      calc
        c * N ^ 2 = c0 * η / (8 * (M : ℝ) ^ 3) * N ^ 2 := rfl
        _ = c0 * η * N ^ 2 / (8 * M) / (M * M) := by rw [hMpow]; ring
        _ ≤ G / (M * M) := by
          rw [div_le_div_iff_of_pos_right (by positivity)]
          exact hG
    exact hfinal.trans hdiv

/-- Every positive-density subset of a long interval contains quadratically many
nontrivial arithmetic progressions of length `L ≥ 4`. -/
private lemma numerous_progression_long {L : ℕ} (hL : 4 ≤ L) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ S : Finset ℕ,
      S ⊆ range N → δ * (N : ℝ) ≤ (S.card : ℝ) →
      c * (N : ℝ) ^ 2 ≤ (progressionCount L N S : ℝ) := by
  sorry

variable {T : Ω → Ω} {A : Set Ω}

/-- The cast `ℕ → ℝ≥0∞` preserves the order. -/
private lemma ennreal_nat_le {a b : ℕ} (h : a ≤ b) : (a : ℝ≥0∞) ≤ b := by
  rw [← ENNReal.ofReal_natCast a, ← ENNReal.ofReal_natCast b]
  exact ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr h)

/-- Times in `{0, …, N - 1}` at which the orbit of `x` meets `A`. -/
private def orbitVisits (T : Ω → Ω) (A : Set Ω) (N : ℕ) (x : Ω) : Finset ℕ :=
  (range N).filter fun m => T^[m] x ∈ A

/-- Points whose first `N` iterates meet `A` with density at least `θ`. -/
private def denseVisits (T : Ω → Ω) (A : Set Ω) (θ : ℝ) (N : ℕ) : Set Ω :=
  {x | θ * (N : ℝ) ≤ ((orbitVisits T A N x).card : ℝ)}

omit [MeasurableSpace Ω] in
/-- The visit count is the sum of the indicators of the first `N` preimages. -/
private lemma orbitVisits_card_eq (T : Ω → Ω) (A : Set Ω) (N : ℕ) (x : Ω) :
    ((orbitVisits T A N x).card : ℝ≥0∞) =
      ∑ m ∈ range N, Set.indicator ((T^[m]) ⁻¹' A) (fun _ => (1 : ℝ≥0∞)) x := by
  rw [orbitVisits, card_filter, Nat.cast_sum]
  refine sum_congr rfl fun m _ => ?_
  by_cases hx : T^[m] x ∈ A
  · have hmem : x ∈ (T^[m]) ⁻¹' A := hx
    simp [ite_eq_left hx, Set.indicator_of_mem hmem]
  · have hnmem : x ∉ (T^[m]) ⁻¹' A := hx
    simp [ite_eq_right hx, Set.indicator_of_notMem hnmem]

/-- Integrating visit counts recovers `N` times the measure of `A`. -/
private lemma lintegral_orbitVisits (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A)
    (N : ℕ) :
    ∫⁻ x, ((orbitVisits T A N x).card : ℝ≥0∞) ∂μ = (N : ℝ≥0∞) * μ A := by
  rw [lintegral_congr fun x => orbitVisits_card_eq T A N x]
  have hnull : ∀ m, NullMeasurableSet ((T^[m]) ⁻¹' A) μ :=
    fun m => (hT.iterate m).aemeasurable.nullMeasurableSet_preimage hA
  rw [lintegral_finsetSum' (range N) fun m _ => aemeasurable_const.indicator₀ (hnull m)]
  have hterm : ∀ m ∈ range N,
      ∫⁻ a, ((T^[m]) ⁻¹' A).indicator (fun _ => (1 : ℝ≥0∞)) a ∂μ = μ A := by
    intro m _
    rw [lintegral_indicator_const₀ (hnull m) 1, one_mul]
    exact (hT.iterate m).measure_preimage hA.nullMeasurableSet
  rw [sum_congr rfl hterm, sum_const, card_range, nsmul_eq_mul]

/-- The visit-count function is almost everywhere measurable. -/
private lemma aemeasurable_orbitCard (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A)
    (N : ℕ) : AEMeasurable (fun x => ((orbitVisits T A N x).card : ℝ≥0∞)) μ := by
  have hsum : AEMeasurable (fun x => ∑ m ∈ range N,
      Set.indicator ((T^[m]) ⁻¹' A) (fun _ => (1 : ℝ≥0∞)) x) μ :=
    (range N).aemeasurable_fun_sum fun m _ =>
      aemeasurable_const.indicator₀
        ((hT.iterate m).aemeasurable.nullMeasurableSet_preimage hA)
  exact hsum.congr (ae_of_all μ fun x => (orbitVisits_card_eq T A N x).symm)

/-- The set of densely visiting points is null measurable. -/
private lemma nullMeasurable_denseVisits (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A)
    (θ : ℝ) (N : ℕ) : NullMeasurableSet (denseVisits T A θ N) μ := by
  have hset : denseVisits T A θ N =
      (fun x => ((orbitVisits T A N x).card : ℝ≥0∞)) ⁻¹'
        Set.Ici (ENNReal.ofReal (θ * (N : ℝ))) := by
    ext x
    rw [denseVisits, Set.mem_ofPred, Set.mem_preimage, Set.mem_Ici]
    simp
  rw [hset]
  exact (aemeasurable_orbitCard hT hA N).nullMeasurableSet_preimage measurableSet_Ici

/-- A positive-measure set forces a uniformly positive mass of dense orbit segments. -/
private lemma denseVisits_measure_ge [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    (hA : MeasurableSet A) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {N : ℕ} (hN : 0 < N) :
    ENNReal.ofReal (((μ A).toReal - θ) / (1 - θ)) ≤ μ (denseVisits T A θ N) := by
  let f : Ω → ℝ≥0∞ := fun x => ((orbitVisits T A N x).card : ℝ≥0∞)
  let G := denseVisits T A θ N
  have hG : NullMeasurableSet G μ := nullMeasurable_denseVisits hT hA θ N
  have hint : ∫⁻ x, f x ∂μ = (N : ℝ≥0∞) * μ A := lintegral_orbitVisits hT hA N
  have hsplit : ∫⁻ x in G, f x ∂μ + ∫⁻ x in Gᶜ, f x ∂μ = ∫⁻ x, f x ∂μ :=
    lintegral_add_compl₀ f hG
  have hleG : ∫⁻ x in G, f x ∂μ ≤ (N : ℝ≥0∞) * μ G := by
    calc
      ∫⁻ x in G, f x ∂μ ≤ ∫⁻ _ in G, (N : ℝ≥0∞) ∂μ := by
        refine setLIntegral_mono measurable_const fun x _ => ?_
        dsimp only [f]
        refine ennreal_nat_le ?_
        rw [orbitVisits]
        exact (card_filter_le (range N) fun m => T^[m] x ∈ A).trans (le_of_eq (card_range N))
      _ = (N : ℝ≥0∞) * μ G := setLIntegral_const G _
  have hleGc : ∫⁻ x in Gᶜ, f x ∂μ ≤ ENNReal.ofReal (θ * (N : ℝ)) * μ Gᶜ := by
    calc
      ∫⁻ x in Gᶜ, f x ∂μ ≤ ∫⁻ _ in Gᶜ, ENNReal.ofReal (θ * (N : ℝ)) ∂μ := by
        refine setLIntegral_mono measurable_const fun x hx => ?_
        have hnot : ¬ θ * (N : ℝ) ≤ ((orbitVisits T A N x).card : ℝ) := by
          simpa [G, denseVisits, Set.mem_ofPred] using hx
        dsimp only [f]
        rw [← ENNReal.ofReal_natCast (orbitVisits T A N x).card]
        exact ENNReal.ofReal_le_ofReal (lt_of_not_ge hnot).le
      _ = ENNReal.ofReal (θ * (N : ℝ)) * μ Gᶜ := setLIntegral_const Gᶜ _
  have hθN : ENNReal.ofReal (θ * (N : ℝ)) = ENNReal.ofReal θ * (N : ℝ≥0∞) := by
    rw [ENNReal.ofReal_mul hθ0, ENNReal.ofReal_natCast]
  have hsum : (N : ℝ≥0∞) * μ A ≤
      (N : ℝ≥0∞) * (μ G + ENNReal.ofReal θ * μ Gᶜ) := by
    calc
      (N : ℝ≥0∞) * μ A = ∫⁻ x in G, f x ∂μ + ∫⁻ x in Gᶜ, f x ∂μ := by
        rw [← hint, ← hsplit]
      _ ≤ (N : ℝ≥0∞) * μ G + ENNReal.ofReal (θ * (N : ℝ)) * μ Gᶜ := add_le_add hleG hleGc
      _ = (N : ℝ≥0∞) * μ G + (ENNReal.ofReal θ * (N : ℝ≥0∞)) * μ Gᶜ := by rw [hθN]
      _ = (N : ℝ≥0∞) * μ G + (N : ℝ≥0∞) * (ENNReal.ofReal θ * μ Gᶜ) := by
        rw [mul_comm (ENNReal.ofReal θ) (N : ℝ≥0∞), mul_assoc]
      _ = (N : ℝ≥0∞) * (μ G + ENNReal.ofReal θ * μ Gᶜ) := by rw [mul_add]
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN.ne'
  have hcancel : μ A ≤ μ G + ENNReal.ofReal θ * μ Gᶜ :=
    (ENNReal.mul_le_mul_iff_right hN0 (ENNReal.natCast_ne_top N)).mp hsum
  have hGfin : μ G ≠ ∞ := measure_ne_top μ G
  have hGcfin : μ Gᶜ ≠ ∞ := measure_ne_top μ Gᶜ
  have hprod : ENNReal.ofReal θ * μ Gᶜ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGcfin
  have hto : (μ A).toReal ≤ (μ G).toReal + θ * (μ Gᶜ).toReal := by
    have hmono := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hGfin, hprod⟩) hcancel
    rw [ENNReal.toReal_add hGfin hprod, ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ0] at hmono
    exact hmono
  have hcompl : (μ Gᶜ).toReal = 1 - (μ G).toReal := by
    rw [prob_compl_eq_one_sub₀ hG, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
  have hden : 0 < 1 - θ := sub_pos.mpr hθ1
  have hdiv : ((μ A).toReal - θ) / (1 - θ) ≤ (μ G).toReal := by
    rw [div_le_iff₀ hden]
    have hlin : (μ A).toReal ≤ (μ G).toReal * (1 - θ) + θ := by
      have hrewrite : (μ G).toReal + θ * (1 - (μ G).toReal) =
          (μ G).toReal * (1 - θ) + θ := by ring
      rw [hcompl] at hto
      linarith
    linarith
  exact (ENNReal.ofReal_le_iff_le_toReal hGfin).mpr hdiv

/-- Points whose orbit meets `A` along the progression with start `p.1` and gap `p.2`. -/
private def progressionHit (T : Ω → Ω) (A : Set Ω) (L : ℕ) (p : ℕ × ℕ) : Set Ω :=
  {x | ∀ j ∈ range L, T^[p.1 + j * p.2] x ∈ A}

omit [MeasurableSpace Ω] in
/-- A progression hit is the intersection of the corresponding preimages. -/
private lemma progressionHit_eq (T : Ω → Ω) (A : Set Ω) (L : ℕ) (p : ℕ × ℕ) :
    progressionHit T A L p = ⋂ j ∈ range L, (T^[p.1 + j * p.2]) ⁻¹' A := by
  ext x
  constructor
  · intro hx
    refine Set.mem_iInter₂.mpr fun j hj => ?_
    rw [Set.mem_preimage]
    exact hx j (mem_coe.mp hj)
  · intro hx j hj
    have hxj := Set.mem_iInter₂.mp hx j (mem_coe.mpr hj)
    rw [Set.mem_preimage] at hxj
    exact hxj

/-- Each progression hit is null measurable. -/
private lemma progressionHit_nullMeasurable (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A)
    (L : ℕ) (p : ℕ × ℕ) : NullMeasurableSet (progressionHit T A L p) μ := by
  rw [progressionHit_eq]
  exact NullMeasurableSet.biInter (Finset.countable_toSet (range L)) fun j _ =>
    (hT.iterate (p.1 + j * p.2)).aemeasurable.nullMeasurableSet_preimage hA

/-- Every term of a progression indexed by `apParams` lies in `{0, …, N - 1}`. -/
private lemma progression_index_lt {L N : ℕ} {p : ℕ × ℕ} (hp : p ∈ apParams L N) {j : ℕ}
    (hj : j ∈ range L) : p.1 + j * p.2 < N := by
  have hlast : p.1 + (L - 1) * p.2 < N := (mem_filter.mp hp).2.2
  have hjle : j ≤ L - 1 := by
    have hjlt : j < L := mem_range.mp hj
    omega
  exact Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_right p.2 hjle) _) hlast

omit [MeasurableSpace Ω] in
/-- Membership in a progression hit is membership of its times in the visit set. -/
private lemma mem_progressionHit_iff (T : Ω → Ω) (A : Set Ω) {L N : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ apParams L N) (x : Ω) :
    x ∈ progressionHit T A L p ↔
      ∀ j ∈ range L, p.1 + j * p.2 ∈ orbitVisits T A N x := by
  constructor
  · intro hx j hj
    rw [orbitVisits, mem_filter, mem_range]
    exact ⟨progression_index_lt hp hj, hx j hj⟩
  · intro hx j hj
    exact (mem_filter.mp (hx j hj)).2

omit [MeasurableSpace Ω] in
/-- The progression count is the sum of the indicators of the progression hits. -/
private lemma progressionCount_indicator (T : Ω → Ω) (A : Set Ω) (L N : ℕ) (x : Ω) :
    (progressionCount L N (orbitVisits T A N x) : ℝ≥0∞) =
      ∑ p ∈ apParams L N,
        Set.indicator (progressionHit T A L p) (fun _ => (1 : ℝ≥0∞)) x := by
  rw [progressionCount, card_filter, Nat.cast_sum]
  refine sum_congr rfl fun p hp => ?_
  by_cases hx : x ∈ progressionHit T A L p
  · have hvisit : ∀ j ∈ range L, p.1 + j * p.2 ∈ orbitVisits T A N x :=
      (mem_progressionHit_iff T A hp x).1 hx
    rw [ite_eq_left (hc := hvisit), Nat.cast_one, Set.indicator_of_mem hx]
  · have hnot : ¬ ∀ j ∈ range L, p.1 + j * p.2 ∈ orbitVisits T A N x :=
      fun h => hx ((mem_progressionHit_iff T A hp x).2 h)
    rw [ite_eq_right (hnc := hnot), Nat.cast_zero, Set.indicator_of_notMem hx]

omit [MeasurableSpace Ω] in
/-- Shifting a progression hit by its start is one application of `T`. -/
private lemma progressionHit_shift (T : Ω → Ω) (A : Set Ω) (L a d : ℕ) :
    progressionHit T A L (a, d) = (T^[a]) ⁻¹' progressionHit T A L (0, d) := by
  ext x
  simp only [progressionHit, Set.mem_ofPred, Set.mem_preimage]
  constructor
  · intro hx j hj
    have h := hx j hj
    rw [Nat.add_comm a (j * d), iterate_add_apply] at h
    simpa [Nat.zero_add] using h
  · intro hx j hj
    have h := hx j hj
    rw [Nat.zero_add] at h
    rw [Nat.add_comm a (j * d), iterate_add_apply]
    exact h

/-- A measure-preserving map leaves the measure of a progression hit unchanged. -/
private lemma measure_progressionHit_shift (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A)
    (L a d : ℕ) :
    μ (progressionHit T A L (a, d)) = μ (progressionHit T A L (0, d)) := by
  rw [progressionHit_shift]
  exact (hT.iterate a).measure_preimage (progressionHit_nullMeasurable hT hA L (0, d))

/-- The integrated progression count is the sum of the measures of the hits. -/
private lemma lintegral_progressionCount (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A)
    (L N : ℕ) :
    ∫⁻ x, (progressionCount L N (orbitVisits T A N x) : ℝ≥0∞) ∂μ =
      ∑ p ∈ apParams L N, μ (progressionHit T A L p) := by
  rw [lintegral_congr fun x => progressionCount_indicator T A L N x]
  have hnull : ∀ p ∈ apParams L N, NullMeasurableSet (progressionHit T A L p) μ :=
    fun p _ => progressionHit_nullMeasurable hT hA L p
  rw [lintegral_finsetSum' (apParams L N) fun p hp => aemeasurable_const.indicator₀ (hnull p hp)]
  refine sum_congr rfl fun p hp => ?_
  rw [lintegral_indicator_const₀ (hnull p hp) 1, one_mul]

/-- Gaps of indexed progressions lie in `{1, …, N}`. -/
private lemma apParams_snd_mem_Icc {L N : ℕ} (hL : 3 ≤ L) {p : ℕ × ℕ} (hp : p ∈ apParams L N) :
    p.2 ∈ Icc 1 N := by
  have hp' := mem_filter.mp hp
  have hlast : p.1 + (L - 1) * p.2 < N := hp'.2.2
  have hL1 : 0 < L - 1 := by omega
  have hdlt : p.2 < N := by
    have hdmul : p.2 ≤ (L - 1) * p.2 := Nat.le_mul_of_pos_left p.2 hL1
    exact Nat.lt_of_le_of_lt (hdmul.trans (Nat.le_add_left _ p.1)) hlast
  rw [mem_Icc]
  exact ⟨Nat.succ_le_of_lt hp'.2.1, le_of_lt hdlt⟩

/-- At most `N` indexed progressions share a fixed positive gap. -/
private lemma fiber_card_le (L N d : ℕ) : #{p ∈ apParams L N | p.2 = d} ≤ N := by
  refine (card_le_card_of_injOn (s := (apParams L N).filter fun p => p.2 = d) (t := range N)
      Prod.fst ?_ ?_).trans (le_of_eq (card_range N))
  · intro p hp
    rw [mem_coe, mem_filter] at hp
    rw [mem_coe, mem_range]
    have hlast : p.1 + (L - 1) * p.2 < N := (mem_filter.mp hp.1).2.2
    exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hlast
  · intro p hp q hq hfst
    rw [mem_coe, mem_filter] at hp hq
    exact Prod.ext hfst (hp.2.trans hq.2.symm)

/-- Summing hit measures by gap costs at most a factor `N`. -/
private lemma sum_progressionHit_le (hT : MeasurePreserving T μ μ) (hA : MeasurableSet A)
    {L N : ℕ} (hL : 3 ≤ L) :
    ∑ p ∈ apParams L N, μ (progressionHit T A L p) ≤
      (N : ℝ≥0∞) * ∑ d ∈ Icc 1 N, μ (progressionHit T A L (0, d)) := by
  have hmaps : ∀ p ∈ apParams L N, p.2 ∈ Icc 1 N := fun p hp => apParams_snd_mem_Icc hL hp
  have hfib := sum_fiberwise_of_maps_to' (s := apParams L N) (t := Icc 1 N) (g := Prod.snd)
    hmaps fun d => μ (progressionHit T A L (0, d))
  have hshift : ∑ p ∈ apParams L N, μ (progressionHit T A L (0, p.2)) =
      ∑ p ∈ apParams L N, μ (progressionHit T A L p) := by
    refine sum_congr rfl fun p _ => (measure_progressionHit_shift hT hA L p.1 p.2).symm
  have hcardμ : ∑ d ∈ Icc 1 N,
      ∑ p ∈ apParams L N with p.2 = d, μ (progressionHit T A L (0, d)) =
      ∑ d ∈ Icc 1 N, (#{p ∈ apParams L N | p.2 = d} : ℝ≥0∞) *
        μ (progressionHit T A L (0, d)) := by
    refine sum_congr rfl fun _ _ => ?_
    rw [sum_const, nsmul_eq_mul]
  rw [← hshift, ← hfib, hcardμ]
  calc
    ∑ d ∈ Icc 1 N, (#{p ∈ apParams L N | p.2 = d} : ℝ≥0∞) *
        μ (progressionHit T A L (0, d))
      ≤ ∑ d ∈ Icc 1 N, (N : ℝ≥0∞) * μ (progressionHit T A L (0, d)) := by
        refine sum_le_sum fun d _ => ?_
        exact mul_le_mul' (ennreal_nat_le (fiber_card_le L N d)) le_rfl
    _ = (N : ℝ≥0∞) * ∑ d ∈ Icc 1 N, μ (progressionHit T A L (0, d)) := by
        rw [mul_sum]

/-- Cesàro means of the `L`-fold return intersections along positive gaps. -/
private def progressionReturnAverage (μ : Measure Ω) (T : Ω → Ω) (A : Set Ω) (L N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ range N,
    (μ (⋂ j ∈ range L, (T^[j * (n + 1)]) ⁻¹' A)).toReal

/-- Each return average is at most one. -/
private lemma progressionReturnAverage_le_one [IsProbabilityMeasure μ] (T : Ω → Ω) (A : Set Ω)
    (L N : ℕ) : progressionReturnAverage μ T A L N ≤ 1 := by
  by_cases hN : N = 0
  · simp [progressionReturnAverage, hN, range_zero, sum_empty, inv_zero]
  · have hpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    have hsum : ∑ n ∈ range N,
        (μ (⋂ j ∈ range L, (T^[j * (n + 1)]) ⁻¹' A)).toReal ≤ (N : ℝ) := by
      calc
        ∑ n ∈ range N, (μ (⋂ j ∈ range L, (T^[j * (n + 1)]) ⁻¹' A)).toReal
          ≤ ∑ n ∈ range N, (1 : ℝ) := sum_le_sum fun _ _ => measureReal_le_one
        _ = (N : ℝ) := by rw [sum_const, card_range, nsmul_eq_mul, mul_one]
    rw [progressionReturnAverage, inv_mul_le_iff₀ hpos, mul_one]
    exact hsum

/-- A quadratic progression count yields a uniform positive lower bound on return averages. -/
private lemma progressionReturnAverage_ge [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    (hA : MeasurableSet A) {L : ℕ} (hL : 3 ≤ L) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hθδ : θ ≤ (μ A).toReal) {c : ℝ} (hc : 0 < c) {N0 : ℕ}
    (hcount : ∀ N, N0 ≤ N → ∀ S : Finset ℕ, S ⊆ range N → θ * (N : ℝ) ≤ (S.card : ℝ) →
      c * (N : ℝ) ^ 2 ≤ (progressionCount L N S : ℝ))
    {N : ℕ} (hN : max N0 1 ≤ N) :
    c * (((μ A).toReal - θ) / (1 - θ)) ≤ progressionReturnAverage μ T A L N := by
  have hNpos : 0 < N := Nat.succ_le_iff.mp (le_trans (Nat.le_max_right _ _) hN)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  set γ : ℝ := ((μ A).toReal - θ) / (1 - θ)
  have hden : 0 < 1 - θ := sub_pos.mpr hθ1
  have hγ0 : 0 ≤ γ := div_nonneg (sub_nonneg.mpr hθδ) hden.le
  let G := denseVisits T A θ N
  have hG : NullMeasurableSet G μ := nullMeasurable_denseVisits hT hA θ N
  have hμG : ENNReal.ofReal γ ≤ μ G := denseVisits_measure_ge hT hA hθ0.le hθ1 hNpos
  let cN : ℝ≥0∞ := ENNReal.ofReal (c * (N : ℝ) ^ 2)
  have hpoint : G.indicator (fun _ => cN) ≤
      fun x => (progressionCount L N (orbitVisits T A N x) : ℝ≥0∞) := by
    intro x
    by_cases hx : x ∈ G
    · rw [Set.indicator_of_mem hx]
      have hsub : orbitVisits T A N x ⊆ range N := by
        rw [orbitVisits]
        exact filter_subset (fun m => T^[m] x ∈ A) (range N)
      have hdense : θ * (N : ℝ) ≤ ((orbitVisits T A N x).card : ℝ) := by
        simpa [G, denseVisits, Set.mem_ofPred] using hx
      have hnum := hcount N (le_trans (Nat.le_max_left _ _) hN) _ hsub hdense
      change ENNReal.ofReal (c * (N : ℝ) ^ 2) ≤
        (progressionCount L N (orbitVisits T A N x) : ℝ≥0∞)
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hnum
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  have hint := lintegral_mono (μ := μ) hpoint
  rw [lintegral_indicator_const₀ hG cN] at hint
  have hmul : cN * ENNReal.ofReal γ ≤ cN * μ G := mul_le_mul' le_rfl hμG
  have hcN : 0 ≤ c * (N : ℝ) ^ 2 := mul_nonneg hc.le (pow_nonneg (Nat.cast_nonneg _) _)
  have hprod : cN * ENNReal.ofReal γ = ENNReal.ofReal (c * (N : ℝ) ^ 2 * γ) := by
    unfold cN
    rw [← ENNReal.ofReal_mul hcN]
  have hintW := lintegral_progressionCount hT hA L N
  have hWle := sum_progressionHit_le hT hA hL (N := N)
  have hlow : ENNReal.ofReal (c * (N : ℝ) ^ 2 * γ) ≤
      (N : ℝ≥0∞) * ∑ d ∈ Icc 1 N, μ (progressionHit T A L (0, d)) := by
    calc
      ENNReal.ofReal (c * (N : ℝ) ^ 2 * γ) = cN * ENNReal.ofReal γ := hprod.symm
      _ ≤ cN * μ G := hmul
      _ ≤ ∫⁻ x, (progressionCount L N (orbitVisits T A N x) : ℝ≥0∞) ∂μ := hint
      _ = ∑ p ∈ apParams L N, μ (progressionHit T A L p) := hintW
      _ ≤ (N : ℝ≥0∞) * ∑ d ∈ Icc 1 N, μ (progressionHit T A L (0, d)) := hWle
  set S : ℝ≥0∞ := ∑ d ∈ Icc 1 N, μ (progressionHit T A L (0, d)) with hSdef
  have hSfin : S ≠ ∞ := ENNReal.sum_ne_top.mpr fun _ _ => measure_ne_top μ _
  have hNSfin : (N : ℝ≥0∞) * S ≠ ∞ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) hSfin
  have hnn : 0 ≤ c * (N : ℝ) ^ 2 * γ := mul_nonneg hcN hγ0
  have hreal : c * (N : ℝ) ^ 2 * γ ≤ (N : ℝ) * S.toReal := by
    have hmono := ENNReal.toReal_mono hNSfin hlow
    rw [ENNReal.toReal_ofReal hnn, ENNReal.toReal_mul, ENNReal.toReal_natCast] at hmono
    exact hmono
  have hsq : c * (N : ℝ) ^ 2 * γ = c * γ * N * N := by ring
  have hcancel : c * γ * N ≤ S.toReal := by
    rw [hsq, mul_comm (N : ℝ) S.toReal] at hreal
    exact (mul_le_mul_iff_left₀ hNreal).mp hreal
  have hIcc : ∑ d ∈ Icc 1 N, (μ (progressionHit T A L (0, d))).toReal =
      ∑ n ∈ range N, (μ (⋂ j ∈ range L, (T^[j * (n + 1)]) ⁻¹' A)).toReal := by
    refine (sum_nbij' (fun n => n + 1) (fun d => d - 1)
      (fun n hn => ?_) (fun d hd => ?_) (fun n _ => ?_) (fun d hd => ?_)
      (fun n _ => ?_)).symm
    · rw [mem_range] at hn
      rw [mem_Icc]
      omega
    · rw [mem_Icc] at hd
      rw [mem_range]
      omega
    · exact Nat.add_sub_cancel n 1
    · rw [mem_Icc] at hd
      exact Nat.sub_add_cancel hd.1
    · have hhit := progressionHit_eq T A L (0, n + 1)
      simp only [Nat.zero_add] at hhit
      exact (congrArg (fun s => (μ s).toReal) hhit).symm
  have hSreal : S.toReal = ∑ n ∈ range N,
      (μ (⋂ j ∈ range L, (T^[j * (n + 1)]) ⁻¹' A)).toReal := by
    rw [hSdef, ENNReal.toReal_sum fun _ _ => measure_ne_top μ _, hIcc]
  have hdiv : c * γ ≤ progressionReturnAverage μ T A L N := by
    rw [progressionReturnAverage, ← hSreal, inv_mul_eq_div, le_div_iff₀ hNreal]
    exact hcancel
  exact hdiv

/-- A uniform positive lower bound on the return averages forces a positive liminf. -/
private lemma liminf_of_numerous [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    (hA : MeasurableSet A) (hpos : 0 < μ A) {L : ℕ} (hL : 3 ≤ L)
    (hnum : ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ S : Finset ℕ,
      S ⊆ range N → δ * (N : ℝ) ≤ (S.card : ℝ) →
      c * (N : ℝ) ^ 2 ≤ (progressionCount L N S : ℝ)) :
    0 < liminf (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ range N,
      (μ (⋂ j ∈ range L, (T^[j * (n + 1)]) ⁻¹' A)).toReal) atTop := by
  set δ : ℝ := (μ A).toReal
  have hδ : 0 < δ := ENNReal.toReal_pos hpos.ne' (measure_ne_top μ A)
  have hδ1 : δ ≤ 1 := by
    have hle : μ A ≤ ENNReal.ofReal 1 := by simpa [ENNReal.ofReal_one] using (prob_le_one : μ A ≤ 1)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one hle
  set θ : ℝ := δ / 2 with hθdef
  have hθ : 0 < θ := by rw [hθdef]; exact half_pos hδ
  have hθ1 : θ < 1 := by rw [hθdef]; linarith
  have hθδ : θ ≤ δ := by rw [hθdef]; exact half_le_self hδ.le
  obtain ⟨c, hc, N0, hcount⟩ := hnum θ hθ
  have hden : 0 < 1 - θ := sub_pos.mpr hθ1
  have hratio : (δ - θ) / (1 - θ) = θ / (1 - θ) := by rw [hθdef]; ring
  have hκ : 0 < c * (θ / (1 - θ)) := mul_pos hc (div_pos hθ hden)
  have hev : ∀ᶠ N in atTop, c * (θ / (1 - θ)) ≤ progressionReturnAverage μ T A L N := by
    filter_upwards [eventually_ge_atTop (max N0 1)] with N hN
    have havg := progressionReturnAverage_ge hT hA hL hθ hθ1 hθδ hc hcount hN
    rw [hratio] at havg
    exact havg
  have hcob : IsCoboundedUnder (· ≥ ·) atTop (progressionReturnAverage μ T A L) :=
    isCoboundedUnder_ge_of_eventually_le atTop
      (Eventually.of_forall fun N => progressionReturnAverage_le_one T A L N)
  have hlim : c * (θ / (1 - θ)) ≤ liminf (progressionReturnAverage μ T A L) atTop :=
    le_liminf_of_le hcob hev
  unfold progressionReturnAverage at hlim
  exact lt_of_lt_of_le hκ hlim

/-- Positive measure yields a positive liminf of multiple-return averages. -/
theorem multiple_recurrence_liminf [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) (hpos : 0 < μ A)
    {k : ℕ} (hk : 2 ≤ k) :
    0 < liminf (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      (μ (⋂ j ∈ Finset.range (k + 1), (T^[j * (n + 1)]) ⁻¹' A)).toReal) atTop := by
  rcases eq_or_lt_of_le hk with rfl | hgt
  · exact liminf_of_numerous hT hA hpos le_rfl fun δ hδ => numerous_progression_three hδ
  · exact liminf_of_numerous hT hA hpos (by omega) fun δ hδ =>
      numerous_progression_long (by omega) hδ

end CKMA

