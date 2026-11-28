/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat

import Mathlib.Combinatorics.Additive.Corner.Roth
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.ReduceModChar

/-!
# Varnavides window counting for arithmetic progressions

Finitary window-counting combinatorics deducing quadratic lower bounds on the number of
arithmetic progressions in dense subsets of `{0, …, N - 1}` from Roth's theorem.

## Main definitions

* `CKMA.apParams`: Pairs `(a, d)` indexing a nontrivial `L`-term progression in `{0, …, N - 1}`.
* `CKMA.progressionCount`: Number of nontrivial `L`-term progressions in `S ∩ {0, …, N - 1}`.
* `CKMA.windowParams`: Windows `(t, s)` of length `M` and step `s ≤ R` in `{0, …, N - 1}`.
* `CKMA.windowHits`: Indices at which a window meets `S`.

## Main results

* `CKMA.exists_pos_mul_sq_le_progressionCount`: for `L ≥ 3`, positive-density subsets of long
  intervals contain quadratically many `L`-term progressions. The case `L = 3` follows from
  Roth's theorem, the case `L ≥ 4` from
  `CKMA.exists_pos_mul_sq_le_progressionCount_of_four_le` (Szemerédi's theorem with Varnavides
  averaging).
-/

public section

noncomputable section

namespace CKMA

open Finset Filter Topology Asymptotics Function
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Pairs `(a, d)` indexing a nontrivial `L`-term progression inside `{0, …, N - 1}`. -/
@[expose]
def apParams (L N : ℕ) : Finset (ℕ × ℕ) :=
  (range N ×ˢ range N).filter fun p => 0 < p.2 ∧ p.1 + (L - 1) * p.2 < N

/-- Membership in `apParams`. -/
lemma mem_apParams_iff {L N : ℕ} {p : ℕ × ℕ} :
    p ∈ apParams L N ↔ p.1 < N ∧ p.2 < N ∧ 0 < p.2 ∧ p.1 + (L - 1) * p.2 < N := by
  simp [apParams, and_assoc]

/-- Nontrivial `L`-term progressions lying in `S` and in `{0, …, N - 1}`. -/
@[expose]
def progressionCount (L N : ℕ) (S : Finset ℕ) : ℕ :=
  ((apParams L N).filter fun p => ∀ j ∈ range L, p.1 + j * p.2 ∈ S).card

/-- Defining equation of `progressionCount`. -/
lemma progressionCount_def (L N : ℕ) (S : Finset ℕ) :
    progressionCount L N S =
      ((apParams L N).filter fun p => ∀ j ∈ range L, p.1 + j * p.2 ∈ S).card :=
  rfl

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
@[expose]
def windowParams (M N R : ℕ) : Finset (ℕ × ℕ) :=
  (range N ×ˢ Icc 1 R).filter fun p => p.1 + (M - 1) * p.2 < N

/-- Membership in `windowParams`. -/
theorem mem_windowParams {M N R : ℕ} {p : ℕ × ℕ} :
    p ∈ windowParams M N R ↔ p.1 < N ∧ 1 ≤ p.2 ∧ p.2 ≤ R ∧ p.1 + (M - 1) * p.2 < N := by
  simp [windowParams, and_assoc]

/-- Indices at which a window meets `S`. -/
@[expose]
def windowHits (S : Finset ℕ) (M : ℕ) (p : ℕ × ℕ) : Finset ℕ :=
  (range M).filter fun i => p.1 + i * p.2 ∈ S

/-- Membership in `windowHits`. -/
lemma mem_windowHits_iff {S : Finset ℕ} {M : ℕ} {p : ℕ × ℕ} {i : ℕ} :
    i ∈ windowHits S M p ↔ i < M ∧ p.1 + i * p.2 ∈ S := by
  simp [windowHits]

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
    (hstep : ∀ s, s ≤ R → (M - 1) * s ≤ bnd) :
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
private lemma middle_windows {M N bnd R : ℕ} (hR : R = bnd / M)
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
  /-- Starting index of the progression. -/
  i : ℕ
  /-- Common difference of the progression. -/
  u : ℕ
  /-- Positivity of the common difference. -/
  hu : 0 < u
  /-- Bound ensuring the third term lies below `M`. -/
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
private lemma good_ratio {δ M cap P G H : ℝ} (hM : 0 < M) (hδ1 : δ ≤ 1)
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
private lemma incidence_ge {S : Finset ℕ} {M N bnd R : ℕ} (hR : R = bnd / M)
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
    have hw := middle_windows hR hybnd.1 hybnd.2 hyN hiM hs
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
      exact (middle_windows hR (hmem _ hy).1 (hmem _ hy).2 (mem_range.mp (hmidN hy))
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

/-- Each ambient 3-term progression comes from at most `M * M` rich windows, so the number of
rich windows is at most `M * M` times `progressionCount 3 N S`. -/
private lemma card_good_le_mul_progressionCount {M N : ℕ} {S : Finset ℕ} {good : Finset (ℕ × ℕ)}
    (hprog : ∀ p ∈ good, ∃ w : IndexAP M, 0 < p.2 ∧ 0 < w.u * p.2 ∧
      p.1 + w.i * p.2 + 2 * (w.u * p.2) < N ∧ p.1 + w.i * p.2 ∈ S ∧
      p.1 + w.i * p.2 + w.u * p.2 ∈ S ∧
      p.1 + w.i * p.2 + 2 * (w.u * p.2) ∈ S) :
    good.card ≤ M * M * progressionCount 3 N S := by
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
  exact hmul.trans (Nat.mul_le_mul_left _ hcount)

/-- Removing the two boundary strips of width `bnd ≤ (δ / 4) * N` from a set of density `δ`
leaves a middle part of density at least `δ / 2`. -/
private lemma card_middle_ge {N bnd : ℕ} {δ : ℝ} {S : Finset ℕ} (hS : S ⊆ range N)
    (hbndN : bnd ≤ N) (hbnd : (bnd : ℝ) ≤ δ / 4 * N) (hdense : δ * (N : ℝ) ≤ (S.card : ℝ)) :
    (δ / 2) * N ≤ ((S.filter fun y => bnd ≤ y ∧ y + bnd < N).card : ℝ) := by
  have hsum : (S.card : ℝ) = ((S.filter fun y => bnd ≤ y ∧ y + bnd < N).card : ℝ) +
      ((S.filter fun y => ¬ (bnd ≤ y ∧ y + bnd < N)).card : ℝ) := by
    exact_mod_cast (card_filter_add_card_filter_not (s := S)
      (fun y => bnd ≤ y ∧ y + bnd < N)).symm
  have hout : ((S.filter fun y => ¬ (bnd ≤ y ∧ y + bnd < N)).card : ℝ) ≤ 2 * (bnd : ℝ) := by
    exact_mod_cast outside_card_le S hS hbndN
  linarith

/-- Double counting: if the middle part of `S` has density `δ / 2`, then the total number of
hits over all windows is at least `(δ / 2) * M` times the number of windows. -/
private lemma mul_card_windowParams_le_sum_windowHits {S : Finset ℕ} {M N bnd R : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hR : R = bnd / M) (hS : S ⊆ range N)
    (hmid : (δ / 2) * N ≤ ((S.filter fun y => bnd ≤ y ∧ y + bnd < N).card : ℝ)) :
    (δ / 2) * (M : ℝ) * (windowParams M N R).card ≤
      ∑ p ∈ windowParams M N R, ((windowHits S M p).card : ℝ) := by
  have hmidS : (S.filter fun y => bnd ≤ y ∧ y + bnd < N) ⊆ S := filter_subset _ _
  have hinc := incidence_ge hR _ hmidS (hmidS.trans hS) fun y hy => (mem_filter.mp hy).2
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hinc
  have hH := (Nat.cast_le (α := ℝ)).mpr hinc
  push_cast at hH
  have hPR := (Nat.cast_le (α := ℝ)).mpr (card_windowParams_le M N R)
  push_cast at hPR
  calc (δ / 2) * (M : ℝ) * (windowParams M N R).card ≤ (δ / 2) * M * (R * N) :=
        mul_le_mul_of_nonneg_left hPR (by positivity)
    _ = (δ / 2) * N * (M * R) := by ring
    _ ≤ (S.filter fun y => bnd ≤ y ∧ y + bnd < N).card * (M * R) :=
        mul_le_mul_of_nonneg_right hmid (by positivity)
    _ = (S.filter fun y => bnd ≤ y ∧ y + bnd < N).card * M * R := by ring
    _ ≤ _ := hH

/-- Splitting a sum of values `f p ≤ M` at a threshold `t`: terms with `t ≤ f p` contribute
at most `M` each, the others at most `t - 1` each. -/
private lemma sum_le_card_filter_mul_add {ι : Type*} (W : Finset ι) (f : ι → ℕ) {M t : ℕ}
    (hf : ∀ p ∈ W, f p ≤ M) :
    ∑ p ∈ W, (f p : ℝ) ≤ ((W.filter fun p => t ≤ f p).card : ℝ) * M +
      (W.card - ((W.filter fun p => t ≤ f p).card : ℝ)) * ((t : ℝ) - 1) := by
  have hcard : ((W.filter fun p => t ≤ f p).card : ℝ) +
      ((W.filter fun p => ¬ t ≤ f p).card : ℝ) = W.card := by
    exact_mod_cast card_filter_add_card_filter_not (s := W) (fun p => t ≤ f p)
  have hgood : ∑ p ∈ W.filter (fun p => t ≤ f p), (f p : ℝ) ≤
      ((W.filter fun p => t ≤ f p).card : ℝ) * M := by
    calc ∑ p ∈ W.filter (fun p => t ≤ f p), (f p : ℝ)
        ≤ ∑ p ∈ W.filter (fun p => t ≤ f p), (M : ℝ) :=
          sum_le_sum fun p hp => by exact_mod_cast hf p (mem_filter.mp hp).1
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hbad : ∑ p ∈ W.filter (fun p => ¬ t ≤ f p), (f p : ℝ) ≤
      ((W.filter fun p => ¬ t ≤ f p).card : ℝ) * ((t : ℝ) - 1) := by
    calc ∑ p ∈ W.filter (fun p => ¬ t ≤ f p), (f p : ℝ)
        ≤ ∑ p ∈ W.filter (fun p => ¬ t ≤ f p), ((t : ℝ) - 1) :=
          sum_le_sum fun p hp => by
            have hlt : f p + 1 ≤ t := Nat.lt_of_not_ge (mem_filter.mp hp).2
            have hlt' : (f p : ℝ) + 1 ≤ t := by exact_mod_cast hlt
            linarith
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  rw [← sum_filter_add_sum_filter_not W (fun p => t ≤ f p)]
  have hsub : (W.card : ℝ) - ((W.filter fun p => t ≤ f p).card : ℝ) =
      ((W.filter fun p => ¬ t ≤ f p).card : ℝ) := by linarith
  rw [hsub]
  linarith

/-- With `bnd = ⌊η * N⌋₊`, steps up to `bnd / M`, `4 * M ≤ η * N` and `η ≤ 1 / 4`, there are
at least `η * N ^ 2 / (8 * M)` windows. -/
private lemma div_le_card_windowParams {M N : ℕ} {η : ℝ} (hM : 1 ≤ M) (hη : 0 < η)
    (hηle : η ≤ 1 / 4) (hscale : 4 * (M : ℝ) ≤ η * N) :
    η * (N : ℝ) ^ 2 / (8 * (M : ℝ)) ≤ (windowParams M N (⌊η * N⌋₊ / M)).card := by
  set bnd : ℕ := ⌊η * N⌋₊
  set R : ℕ := bnd / M with hRdef
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hbndR : (bnd : ℝ) ≤ η * N := Nat.floor_le (by positivity)
  have hbndN : bnd ≤ N := by
    have : (bnd : ℝ) ≤ N := hbndR.trans (by nlinarith)
    exact_mod_cast this
  have hfloor : η * N - 1 < (bnd : ℝ) := by
    have := Nat.lt_floor_add_one (η * N)
    linarith
  have hbndhalf : η * (N : ℝ) / 2 ≤ (bnd : ℝ) := by linarith
  have hRreal : (bnd : ℝ) / (2 * M) ≤ R := by
    have hlt : bnd < M * (R + 1) := Nat.lt_mul_div_succ bnd (by omega)
    have hcast : (bnd : ℝ) < M * ((R : ℝ) + 1) := by exact_mod_cast hlt
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hPge := (Nat.cast_le (α := ℝ)).mpr
    (card_windowParams_ge (N := N) fun s hs => step_mul_le (M := M) hRdef hs)
  rw [Nat.cast_mul] at hPge
  have hNsub : (N : ℝ) / 2 ≤ ((N - bnd : ℕ) : ℝ) := by
    rw [Nat.cast_sub hbndN]
    nlinarith
  have hRlow : η * (N : ℝ) / (4 * M) ≤ R := by
    calc η * (N : ℝ) / (4 * M) = (η * N / 2) / (2 * M) := by ring
      _ ≤ bnd / (2 * M) := div_le_div_of_nonneg_right hbndhalf (by positivity)
      _ ≤ R := hRreal
  calc η * (N : ℝ) ^ 2 / (8 * M) = (η * N / (4 * M)) * (N / 2) := by ring
    _ ≤ R * ((N - bnd : ℕ) : ℝ) := mul_le_mul hRlow hNsub (by positivity) (by positivity)
    _ ≤ _ := hPge

/-- Each rich window carries a 3-term progression of `S`, so the number of rich windows
divided by `M * M` is at most the progression count. -/
private lemma card_filter_div_le_progressionCount {S : Finset ℕ} {M N R : ℕ} {δ : ℝ}
    (hroth : (rothNumberNat M : ℝ) ≤ (δ / 8) * (M : ℝ)) (hM : 1 ≤ M) :
    (((windowParams M N R).filter fun p =>
        ⌈(δ / 4) * (M : ℝ)⌉₊ ≤ (windowHits S M p).card).card : ℝ) / (M * M) ≤
      progressionCount 3 N S := by
  have hnat := card_good_le_mul_progressionCount (N := N)
    (good := (windowParams M N R).filter fun p => ⌈(δ / 4) * (M : ℝ)⌉₊ ≤ (windowHits S M p).card)
    fun p hp => exists_indexAP_of_window (S := S) (N := N) (R := R) hroth hM
      (mem_filter.mp hp).1 (mem_filter.mp hp).2
  have hcast := (Nat.cast_le (α := ℝ)).mpr hnat
  push_cast at hcast
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  rw [div_le_iff₀ (mul_pos hMpos hMpos)]
  linarith

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
  have hδle : δ ≤ 1 := le_of_not_gt hδ1
  -- Choose the window length `M` from Roth's theorem and the constants of the count.
  obtain ⟨M, hM, hroth⟩ := exists_roth_scale (show 0 < δ / 8 by positivity)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.succ_le_iff.mp hM
  let η : ℝ := δ / 4
  have hη : 0 < η := by positivity
  have hηle : η ≤ 1 / 4 := by dsimp only [η]; linarith
  let cap : ℝ := (Nat.ceil ((δ / 4) * (M : ℝ)) : ℝ) - 1
  have hcap : cap < (δ / 4) * (M : ℝ) := by
    have hnonneg : 0 ≤ (δ / 4) * (M : ℝ) := by positivity
    linarith [Nat.ceil_lt_add_one hnonneg]
  let c0 : ℝ := ((δ / 2) * (M : ℝ) - cap) / ((M : ℝ) - cap)
  let c : ℝ := c0 * η / (8 * (M : ℝ) ^ 3)
  have hc0 : 0 < c0 := by
    have hfrac : (δ / 4) * (M : ℝ) ≤ (M : ℝ) / 4 := by nlinarith
    exact div_pos (by linarith) (by linarith)
  have hc : 0 < c := by positivity
  let N0 : ℕ := Nat.ceil ((4 * (M : ℝ)) / η)
  refine ⟨c, hc, N0, fun N hN S hS hdense => ?_⟩
  have hscale : 4 * (M : ℝ) ≤ η * N := by
    have hcast : (N0 : ℝ) ≤ N := by exact_mod_cast hN
    have hceil : (4 * (M : ℝ)) / η ≤ N := (Nat.le_ceil _).trans hcast
    rw [div_le_iff₀ hη] at hceil
    linarith
  -- Windows of length `M` and step at most `R` in the middle of `{0, …, N - 1}`.
  let bnd : ℕ := ⌊η * N⌋₊
  let R : ℕ := bnd / M
  have hbndR : (bnd : ℝ) ≤ η * N := Nat.floor_le (by positivity)
  have hbndN : bnd ≤ N := by
    have : (bnd : ℝ) ≤ N := hbndR.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
    exact_mod_cast this
  have hmid := card_middle_ge hS hbndN hbndR hdense
  have hPδ := mul_card_windowParams_le_sum_windowHits (R := R) hδ rfl hS hmid
  -- Many windows are rich, i.e. carry at least `⌈(δ / 4) * M⌉₊` hits.
  have hbound := sum_le_card_filter_mul_add (windowParams M N R)
    (fun p => (windowHits S M p).card) (t := ⌈(δ / 4) * (M : ℝ)⌉₊)
    fun p _ => card_le_card (windowHits_subset S M p) |>.trans_eq (card_range M)
  have hratio := good_ratio hMpos hδle hcap hPδ hbound
  have hG := (mul_le_mul_of_nonneg_left (div_le_card_windowParams hM hη hηle hscale)
    hc0.le).trans hratio
  -- Each rich window yields a 3-term progression of `S`.
  have hdiv := card_filter_div_le_progressionCount (N := N) (R := R) (S := S) hroth hM
  have hMpow : (M : ℝ) ^ 3 = M * (M * M) := by ring
  calc c * N ^ 2 = c0 * (η * (N : ℝ) ^ 2 / (8 * (M : ℝ))) / (M * M) := by
        dsimp only [c]; rw [hMpow]; ring
    _ ≤ _ := div_le_div_of_nonneg_right hG (by positivity)
    _ ≤ _ := hdiv

/-- **Szemerédi–Varnavides** for `L ≥ 4`: every positive-density subset of a long interval
contains quadratically many nontrivial arithmetic progressions of length `L`. -/
theorem exists_pos_mul_sq_le_progressionCount_of_four_le {L : ℕ} (hL : 4 ≤ L) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ S : Finset ℕ,
      S ⊆ range N → δ * (N : ℝ) ≤ (S.card : ℝ) →
      c * (N : ℝ) ^ 2 ≤ (progressionCount L N S : ℝ) := by
  sorry

/-- **Varnavides counting**: for `L ≥ 3`, every positive-density subset of a long interval
`{0, …, N - 1}` contains quadratically many nontrivial `L`-term arithmetic progressions. -/
theorem exists_pos_mul_sq_le_progressionCount {L : ℕ} (hL : 3 ≤ L) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ S : Finset ℕ,
      S ⊆ range N → δ * (N : ℝ) ≤ (S.card : ℝ) →
      c * (N : ℝ) ^ 2 ≤ (progressionCount L N S : ℝ) := by
  rcases eq_or_lt_of_le hL with rfl | hL
  · exact numerous_progression_three hδ
  · exact exists_pos_mul_sq_le_progressionCount_of_four_le hL hδ

end CKMA
