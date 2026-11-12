/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Metrizable.CompletelyMetrizable

import Mathlib.Tactic

import CKMA.Dynamics.Ergodic.Recurrence.Multiple

/-!
# Rokhlin towers and multiple recurrence (10)

`IsAperiodicModMeasure` and `towerLevel` describe finite measurable towers for an invertible
probability-preserving system. The Rokhlin statement controls disjointness and the measure
of the tower complement under the standard probability-space hypotheses.

The multiple-recurrence definitions record simultaneous return sets and their Cesàro
averages. Furstenberg's target supplies a positive limiting upper average for a positive
measure set, with the number of returns and averaging convention explicit.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Aperiodicity modulo the measure: every positive iterate has an a.e. empty fixed-point set. -/
def IsAperiodicModMeasure (T : Ω → Ω) (μ : Measure Ω) : Prop :=
  ∀ n : ℕ, 0 < n → μ {ω | (T^[n]) ω = ω} = 0

/-- Levels of a measurable Rokhlin tower of finite height. -/
def towerLevel (T : Ω → Ω) (B : Set Ω) (i : ℕ) : Set Ω := (T^[i]) '' B

section Rokhlin

set_option linter.unusedSectionVars false

variable [StandardBorelSpace Ω] [IsProbabilityMeasure μ] (T : Ω ≃ᵐ Ω)

open Set Function

omit [StandardBorelSpace Ω] [IsProbabilityMeasure μ] T in
/-- Strict decrease of `1 - ·` on `{x : ℝ≥0∞ | x ≤ 1}`. -/
private lemma one_sub_lt_one_sub {a b : ℝ≥0∞} (hb : b ≤ 1) (h : a < b) : 1 - b < 1 - a := by
  have ha : a ≤ 1 := h.le.trans hb
  have hb_top : b ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hb
  rw [ENNReal.sub_lt_iff_lt_right hb_top hb]
  have hcancel : (1 - a) + a = 1 := tsub_add_cancel_of_le ha
  have hlt : (1 - a) + a < (1 - a) + b :=
    ENNReal.add_lt_add_left (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self) h
  rwa [hcancel] at hlt

/-- Inverse iterates undo forward iterates. -/
private lemma symm_iterate_apply (i : ℕ) (x : Ω) : (T.symm^[i]) ((T^[i]) x) = x := by
  induction i with
  | zero => rfl
  | succ i ih =>
    calc
      (T.symm^[i + 1]) ((T^[i + 1]) x)
          = (T.symm^[i]) (T.symm ((T^[i + 1]) x)) := by rw [iterate_succ_apply]
      _ = (T.symm^[i]) (T.symm (T ((T^[i]) x))) := by rw [iterate_succ_apply']
      _ = (T.symm^[i]) ((T^[i]) x) := by rw [MeasurableEquiv.symm_apply_apply]
      _ = x := ih

/-- Forward iterates undo inverse iterates. -/
private lemma iterate_symm_apply (i : ℕ) (x : Ω) : (T^[i]) ((T.symm^[i]) x) = x := by
  induction i with
  | zero => rfl
  | succ i ih =>
    calc
      (T^[i + 1]) ((T.symm^[i + 1]) x)
          = (T^[i]) (T ((T.symm^[i + 1]) x)) := by rw [iterate_succ_apply]
      _ = (T^[i]) (T (T.symm ((T.symm^[i]) x))) := by rw [iterate_succ_apply']
      _ = (T^[i]) ((T.symm^[i]) x) := by rw [MeasurableEquiv.apply_symm_apply]
      _ = x := ih

/-- `(T^[a])` after `(T^[b])` is the iterate of length `b + a`. -/
private lemma iterate_apply_add (a b : ℕ) (x : Ω) :
    (T^[a]) ((T^[b]) x) = (T^[b + a]) x := by
  rw [(iterate_add_apply (⇑T) a b x).symm, Nat.add_comm]

/-- An iterate image is the preimage under the inverse iterate. -/
private lemma image_iterate_eq_preimage_symm (s : Set Ω) (i : ℕ) :
    (T^[i]) '' s = (T.symm^[i]) ⁻¹' s := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show (T.symm^[i]) ((T^[i]) y) ∈ s
    rw [symm_iterate_apply]
    exact hy
  · intro hx
    exact ⟨(T.symm^[i]) x, hx, iterate_symm_apply T i x⟩

/-- Preimages of a measurable set under iterates have the same measure. -/
private lemma measure_preimage_iterate (hT : MeasurePreserving T μ μ) {A : Set Ω}
    (hA : MeasurableSet A) (k : ℕ) : μ ((T^[k]) ⁻¹' A) = μ A :=
  (hT.iterate k).measure_preimage hA.nullMeasurableSet

/-- Images of a null set under iterates are null. -/
private lemma measure_image_iterate_null (hT : MeasurePreserving T μ μ) {A : Set Ω}
    (hA : μ A = 0) (k : ℕ) : μ ((T^[k]) '' A) = 0 := by
  rw [image_iterate_eq_preimage_symm]
  exact (hT.symm.iterate k).preimage_null hA

/-- A measurable set whose first `M` preimages under `T` are pairwise disjoint. -/
private def IsDisjointPreimage (M : ℕ) (A : Set Ω) : Prop :=
  MeasurableSet A ∧
    ∀ i j : ℕ, i < M → j < M → i ≠ j → Disjoint ((T^[i]) ⁻¹' A) ((T^[j]) ⁻¹' A)

/-- The empty set is a disjoint-preimage base of every height. -/
private lemma isDisjointPreimage_empty (M : ℕ) : IsDisjointPreimage T M ∅ := by
  refine ⟨MeasurableSet.empty, fun i j _ _ _ => ?_⟩
  simp

/-- Disjointness from the first `M` shifts implies disjoint preimages. -/
private lemma IsDisjointPreimage.of_shifts {M : ℕ} {A : Set Ω} (hA : MeasurableSet A)
    (h : ∀ k, 0 < k → k < M → Disjoint A ((T^[k]) ⁻¹' A)) : IsDisjointPreimage T M A := by
  refine ⟨hA, fun i j hi hj hij => ?_⟩
  have hshift : ∀ {i j}, i < j → i < M → j < M →
      Disjoint ((T^[i]) ⁻¹' A) ((T^[j]) ⁻¹' A) := by
    intro i j hlt hi hj
    have hd0 : 0 < j - i := Nat.sub_pos_of_lt hlt
    have hdM : j - i < M := (Nat.sub_le j i).trans_lt hj
    rw [disjoint_left]
    intro x hx hy
    have hxA : (T^[i]) x ∈ A := by simpa [mem_preimage] using hx
    have hyA : (T^[j]) x ∈ A := by simpa [mem_preimage] using hy
    have hcomp : (T^[j - i]) ((T^[i]) x) = (T^[j]) x := by
      rw [iterate_apply_add, Nat.add_sub_of_le hlt.le]
    have hmem : (T^[i]) x ∈ A ∩ ((T^[j - i]) ⁻¹' A) :=
      ⟨hxA, by simpa [mem_preimage, hcomp] using hyA⟩
    exact disjoint_left.mp (h _ hd0 hdM) hmem.1 hmem.2
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact hshift hlt hi hj
  · exact (hshift hlt hj hi).symm

/-- Points within time `M` of `P` under `T` or `T.symm`. -/
private def orbitNbhd (M : ℕ) (P : Set Ω) : Set Ω :=
  (⋃ d ∈ Finset.range M, (T^[d]) ⁻¹' P) ∪ (⋃ d ∈ Finset.range M, (T.symm^[d]) ⁻¹' P)

/-- `P` sits in its own time-`M` neighborhood once `M` is positive. -/
private lemma orbitNbhd_self {M : ℕ} (hM : 0 < M) (P : Set Ω) : P ⊆ orbitNbhd T M P := by
  intro x hx
  refine Or.inl (mem_iUnion₂.2 ⟨0, Finset.mem_range.mpr hM, ?_⟩)
  simpa using hx

/-- Disjoint preimage bases that avoid each other's `M`-neighborhood may be united. -/
private lemma IsDisjointPreimage.union_of_subset_compl {M : ℕ} {P A : Set Ω}
    (hP : IsDisjointPreimage T M P) (hA : IsDisjointPreimage T M A)
    (hsub : A ⊆ (orbitNbhd T M P)ᶜ) : IsDisjointPreimage T M (P ∪ A) := by
  refine ⟨hP.1.union hA.1, fun i j hi hj hij => ?_⟩
  have hshift : ∀ {i j}, i < j → i < M → j < M →
      Disjoint ((T^[i]) ⁻¹' (P ∪ A)) ((T^[j]) ⁻¹' (P ∪ A)) := by
    intro i j hlt hi hj
    set d := j - i
    have hd0 : 0 < d := Nat.sub_pos_of_lt hlt
    have hdM : d < M := (Nat.sub_le j i).trans_lt hj
    have hji : i + d = j := Nat.add_sub_of_le hlt.le
    rw [disjoint_left]
    intro x hx hy
    have hxU : (T^[i]) x ∈ P ∪ A := by simpa [mem_preimage] using hx
    have hyU : (T^[j]) x ∈ P ∪ A := by simpa [mem_preimage] using hy
    have hiter : (T^[d]) ((T^[i]) x) = (T^[j]) x := by
      rw [iterate_apply_add, hji]
    have hinv : (T.symm^[d]) ((T^[j]) x) = (T^[i]) x := by
      rw [← hiter, symm_iterate_apply]
    rcases hxU with hxP | hxA <;> rcases hyU with hyP | hyA
    · exact disjoint_left.mp (hP.2 i j hi hj (ne_of_lt hlt)) hxP hyP
    · have hyNbhd : (T^[j]) x ∈ orbitNbhd T M P :=
        Or.inr (mem_iUnion₂.2 ⟨d, Finset.mem_range.mpr hdM, by simpa [hinv] using hxP⟩)
      exact hsub hyA hyNbhd
    · have hxNbhd : (T^[i]) x ∈ orbitNbhd T M P := by
        refine Or.inl (mem_iUnion₂.2 ⟨d, Finset.mem_range.mpr hdM, ?_⟩)
        show (T^[d]) ((T^[i]) x) ∈ P
        rw [hiter]
        exact hyP
      exact hsub hxA hxNbhd
    · exact disjoint_left.mp (hA.2 i j hi hj (ne_of_lt hlt)) hxA hyA
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact hshift hlt hi hj
  · exact (hshift hlt hj hi).symm

/-- A disjoint-preimage base contained in the complement of the `M`-neighborhood of `P`. -/
private def IsAdmissible (M : ℕ) (P A : Set Ω) : Prop :=
  IsDisjointPreimage T M A ∧ A ⊆ (orbitNbhd T M P)ᶜ

/-- The empty set is admissible against every obstacle. -/
private lemma isAdmissible_empty (M : ℕ) (P : Set Ω) : IsAdmissible T M P ∅ :=
  ⟨isDisjointPreimage_empty T M, empty_subset _⟩

/-- Every admissible set has measure at most one. -/
private lemma measure_admissible_le_one {M : ℕ} {P A : Set Ω} (_hA : IsAdmissible T M P A) :
    μ A ≤ 1 := by
  calc
    μ A ≤ μ (Set.univ : Set Ω) := measure_mono (Set.subset_univ A)
    _ = 1 := measure_univ

/-- The set of measures of admissible bases is bounded above by one. -/
private lemma adm_bddAbove (M : ℕ) (P : Set Ω) :
    BddAbove (μ '' {A | IsAdmissible T M P A}) := by
  refine ⟨1, fun x hx => ?_⟩
  rcases hx with ⟨A, hA, hxμ⟩
  rw [← hxμ]
  exact measure_admissible_le_one T hA

/-- The supremum of admissible measures is at most one. -/
private lemma admSup_le_one (M : ℕ) (P : Set Ω) :
    sSup (μ '' {A | IsAdmissible T M P A}) ≤ 1 := by
  refine csSup_le' fun x hx => ?_
  rcases hx with ⟨A, hA, hxμ⟩
  rw [← hxμ]
  exact measure_admissible_le_one T hA

/-- An admissible base whose measure is at least half the supremum. -/
private lemma exists_halfPiece (M : ℕ) (P : Set Ω) :
    ∃ A, IsAdmissible T M P A ∧ sSup (μ '' {A | IsAdmissible T M P A}) ≤ 2 * μ A := by
  set S := μ '' {A | IsAdmissible T M P A}
  set α := sSup S
  have hα : α ≤ 1 := admSup_le_one T M P
  by_cases h0 : α = 0
  · exact ⟨∅, isAdmissible_empty T M P, by simp [h0]⟩
  · have htop : α ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hα
    have hhalf : α / 2 < α := ENNReal.half_lt_self h0 htop
    obtain ⟨r, hr, hlt⟩ := exists_lt_of_lt_csSup' hhalf
    obtain ⟨A, hA, hrμ⟩ := hr
    subst hrμ
    refine ⟨A, hA, ?_⟩
    calc
      α = 2 * (α / 2) := (ENNReal.mul_div_cancel (by simp) (by simp)).symm
      _ ≤ 2 * μ A :=
        le_of_lt (ENNReal.mul_lt_mul_right (by simp : (2 : ℝ≥0∞) ≠ 0) (by simp) hlt)

/-- A chosen admissible base capturing half the remaining supremum. -/
private noncomputable def halfPiece (M : ℕ) (P : Set Ω) : Set Ω :=
  Classical.choose (exists_halfPiece (μ := μ) T M P)

/-- The chosen half-piece is admissible and at least half-maximal. -/
private lemma halfPiece_spec (M : ℕ) (P : Set Ω) :
    IsAdmissible T M P (halfPiece (μ := μ) T M P) ∧
      sSup (μ '' {A | IsAdmissible T M P A}) ≤ 2 * μ (halfPiece (μ := μ) T M P) :=
  Classical.choose_spec (exists_halfPiece (μ := μ) T M P)

/-- Successive unions of half-pieces against the set already chosen. -/
private noncomputable def cum (M : ℕ) : ℕ → Set Ω
  | 0 => ∅
  | n + 1 => cum M n ∪ halfPiece (μ := μ) T M (cum M n)

/-- Each partial union is contained in the next one. -/
private lemma cum_succ_subset (M n : ℕ) : cum (μ := μ) T M n ⊆ cum (μ := μ) T M (n + 1) := by
  simp [cum, subset_union_left]

/-- The partial unions increase with the stage. -/
private lemma cum_mono (M) {a b : ℕ} (h : a ≤ b) : cum (μ := μ) T M a ⊆ cum (μ := μ) T M b := by
  induction b with
  | zero =>
    obtain rfl : a = 0 := Nat.eq_zero_of_le_zero h
    rfl
  | succ b ih =>
    rcases lt_or_eq_of_le h with hlt | rfl
    · exact (ih (Nat.le_of_lt_succ hlt)).trans (cum_succ_subset T M b)
    · exact subset_rfl

/-- Every partial union is a disjoint-preimage set. -/
private lemma cum_isDisjointPreimage (M n : ℕ) : IsDisjointPreimage T M (cum (μ := μ) T M n) := by
  induction n with
  | zero =>
    simpa [cum] using isDisjointPreimage_empty T M
  | succ n ih =>
    exact ih.union_of_subset_compl T
      (halfPiece_spec T M (cum (μ := μ) T M n)).1.1
      (halfPiece_spec T M (cum (μ := μ) T M n)).1.2

/-- A half-piece lies in the complement of the obstacle it was chosen against. -/
private lemma halfPiece_subset_compl {M : ℕ} (hM : 0 < M) (P : Set Ω) :
    halfPiece (μ := μ) T M P ⊆ Pᶜ := by
  intro x hx hxP
  exact (halfPiece_spec T M P).1.2 hx (orbitNbhd_self T hM P hxP)

/-- Half-pieces at distinct stages are disjoint. -/
private lemma halfPiece_pairwise (M : ℕ) (hM : 0 < M) :
    Pairwise (Disjoint on fun n => halfPiece (μ := μ) T M (cum (μ := μ) T M n)) := by
  intro a b hab
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · have hsub : halfPiece (μ := μ) T M (cum (μ := μ) T M a) ⊆ cum (μ := μ) T M b :=
      (subset_union_right).trans (cum_mono T M (Nat.succ_le_of_lt hlt))
    exact disjoint_of_subset hsub (halfPiece_subset_compl T hM _) disjoint_compl_right
  · have hsub : halfPiece (μ := μ) T M (cum (μ := μ) T M b) ⊆ cum (μ := μ) T M a :=
      (subset_union_right).trans (cum_mono T M (Nat.succ_le_of_lt hlt))
    exact (disjoint_of_subset hsub (halfPiece_subset_compl T hM _) disjoint_compl_right).symm

/-- The union of every half-piece. -/
private noncomputable def sweep (M : ℕ) : Set Ω :=
  ⋃ n, halfPiece (μ := μ) T M (cum (μ := μ) T M n)

/-- Each partial union is contained in the sweep. -/
private lemma cum_subset_sweep (M n : ℕ) : cum (μ := μ) T M n ⊆ sweep (μ := μ) T M := by
  induction n with
  | zero => simp [cum]
  | succ n ih =>
    intro x hx
    rw [cum] at hx
    rcases hx with hx | hx
    · exact ih hx
    · exact mem_iUnion.2 ⟨n, hx⟩

/-- The sweep is a disjoint-preimage set. -/
private lemma sweep_isDisjointPreimage (M : ℕ) (_hM : 0 < M) :
    IsDisjointPreimage T M (sweep (μ := μ) T M) := by
  refine ⟨MeasurableSet.iUnion fun n => (halfPiece_spec T M (cum (μ := μ) T M n)).1.1.1, ?_⟩
  intro i j hi hj hij
  rw [disjoint_left]
  intro x hxi hxj
  obtain ⟨a, ha⟩ := mem_iUnion.1 hxi
  obtain ⟨b, hb⟩ := mem_iUnion.1 hxj
  have haC : (T^[i]) x ∈ cum (μ := μ) T M (max a b + 1) :=
    (subset_union_right.trans (cum_mono T M (Nat.succ_le_succ (le_max_left a b)))) ha
  have hbC : (T^[j]) x ∈ cum (μ := μ) T M (max a b + 1) :=
    (subset_union_right.trans (cum_mono T M (Nat.succ_le_succ (le_max_right a b)))) hb
  exact disjoint_left.mp
    ((cum_isDisjointPreimage T M (max a b + 1)).2 i j hi hj hij) haC hbC

/-- `M` disjoint preimages bound the base by `1 / M`. -/
private lemma measure_le_inv (hT : MeasurePreserving T μ μ) {M : ℕ} (hM : 0 < M) {A : Set Ω}
    (hA : IsDisjointPreimage T M A) : μ A ≤ 1 / (M : ℝ≥0∞) := by
  have hd : PairwiseDisjoint (↑(Finset.range M)) (fun i => (T^[i]) ⁻¹' A) :=
    fun i hi j hj hij => hA.2 i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
  have hm : ∀ i ∈ Finset.range M, MeasurableSet ((T^[i]) ⁻¹' A) :=
    fun i _ => hA.1.preimage (T.measurable.iterate i)
  have hsum : (M : ℝ≥0∞) * μ A ≤ 1 := by
    rw [← nsmul_eq_mul, ← Finset.card_range M, ← Finset.sum_const]
    calc
      ∑ i ∈ Finset.range M, μ A
          = μ (⋃ i ∈ Finset.range M, (T^[i]) ⁻¹' A) := by
            rw [measure_biUnion_finset hd hm]
            refine Finset.sum_congr rfl fun i _ => ?_
            exact (measure_preimage_iterate T hT hA.1 i).symm
      _ ≤ μ (Set.univ : Set Ω) :=
        measure_mono (subset_univ (⋃ i ∈ Finset.range M, (T^[i]) ⁻¹' A))
      _ = 1 := measure_univ
  exact (ENNReal.le_div_iff_mul_le (Or.inl (Nat.cast_ne_zero.mpr hM.ne'))
    (Or.inr ENNReal.one_ne_top)).2 (by rwa [mul_comm] at hsum)

/-- Points that meet `A` under some nonnegative iterate of `f`. -/
private def forwardSat (f : Ω → Ω) (A : Set Ω) : Set Ω :=
  ⋃ k : ℕ, (f^[k]) ⁻¹' A

/-- The forward and backward saturation of `A`. -/
private def bilateral (A : Set Ω) : Set Ω :=
  forwardSat T A ∪ forwardSat (⇑T.symm) A

/-- First entrance of the orbit into `A`, at time `k`. -/
private def entrance (A : Set Ω) (k : ℕ) : Set Ω :=
  (T^[k]) ⁻¹' A \ ⋃ j ∈ Finset.range k, (T^[j]) ⁻¹' A

/-- Entrances at the positive multiples of the height. -/
private def skyscraper (A : Set Ω) (n : ℕ) : Set Ω :=
  ⋃ q : ℕ, entrance T A ((q + 1) * n)

/-- Shifting an entrance time by `d ≤ k` lands in the entrance at time `k - d`. -/
private lemma mem_entrance_iterate {A : Set Ω} {k d : ℕ} (hd : d ≤ k) {x : Ω}
    (hx : x ∈ entrance T A k) : (T^[d]) x ∈ entrance T A (k - d) := by
  have hxA : (T^[k]) x ∈ A := by simpa [mem_preimage] using hx.1
  have hxnot : x ∉ ⋃ j ∈ Finset.range k, (T^[j]) ⁻¹' A := hx.2
  refine ⟨?_, ?_⟩
  · change (T^[k - d]) ((T^[d]) x) ∈ A
    rw [iterate_apply_add, Nat.add_sub_of_le hd]
    exact hxA
  · intro hmem
    obtain ⟨j, hj, hjA⟩ := mem_iUnion₂.1 hmem
    have hjA' : (T^[j + d]) x ∈ A := by
      change (T^[j]) ((T^[d]) x) ∈ A at hjA
      rwa [iterate_apply_add, Nat.add_comm] at hjA
    have hjd : j + d < k := by
      have hj' : j < k - d := Finset.mem_range.mp hj
      omega
    exact hxnot (mem_iUnion₂.2 ⟨j + d, Finset.mem_range.mpr hjd, hjA'⟩)

/-- Distinct entrance times are disjoint. -/
private lemma disjoint_entrance {A : Set Ω} {k m : ℕ} (hkm : k ≠ m) :
    Disjoint (entrance T A k) (entrance T A m) := by
  rcases lt_or_gt_of_ne hkm with hlt | hlt
  · rw [disjoint_left]
    intro x hx hxm
    exact hxm.2 (mem_iUnion₂.2 ⟨k, Finset.mem_range.mpr hlt, hx.1⟩)
  · rw [disjoint_left]
    intro x hx hxm
    exact hx.2 (mem_iUnion₂.2 ⟨m, Finset.mem_range.mpr hlt, hxm.1⟩)

/-- Preimages of the skyscraper under distinct shifts of length less than `n` are disjoint. -/
private lemma disjoint_skyscraper_shifts {A : Set Ω} {n : ℕ} (_hn : 0 < n) {r s : ℕ}
    (hr : r < n) (hs : s < n) (hrs : r ≠ s) :
    Disjoint ((T^[r]) ⁻¹' skyscraper T A n) ((T^[s]) ⁻¹' skyscraper T A n) := by
  have hone : ∀ {r s}, r < s → s < n →
      Disjoint ((T^[r]) ⁻¹' skyscraper T A n) ((T^[s]) ⁻¹' skyscraper T A n) := by
    intro r s hlt hs
    rw [disjoint_left]
    intro x hx hy
    obtain ⟨q, hq⟩ := mem_iUnion.1 hx
    obtain ⟨p, hp⟩ := mem_iUnion.1 hy
    set d := s - r
    have hd0 : 0 < d := Nat.sub_pos_of_lt hlt
    have hdlt : d < n := by omega
    have hdle : d ≤ (q + 1) * n := by
      have hnle : n ≤ (q + 1) * n := Nat.le_mul_of_pos_left n (Nat.succ_pos q)
      exact le_trans (le_of_lt hdlt) hnle
    have hshift : (T^[s]) x ∈ entrance T A ((q + 1) * n - d) := by
      have hcalc : (T^[d]) ((T^[r]) x) = (T^[s]) x := by
        rw [iterate_apply_add, Nat.add_sub_of_le hlt.le]
      rw [← hcalc]
      exact mem_entrance_iterate T hdle hq
    have heq : (p + 1) * n = (q + 1) * n - d := by
      by_contra hne
      exact disjoint_left.mp (disjoint_entrance T hne) hp hshift
    have hdvd : n ∣ d := by
      have hk : n ∣ (q + 1) * n := dvd_mul_left _ _
      have hm : n ∣ (p + 1) * n := dvd_mul_left _ _
      have hsub : d = (q + 1) * n - (p + 1) * n := by
        have hcancel : (q + 1) * n - ((q + 1) * n - d) = d := Nat.sub_sub_self hdle
        rw [← heq] at hcancel
        exact hcancel.symm
      rw [hsub]
      exact Nat.dvd_sub hk hm
    have hmod : d % n = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have hmod' : d % n = d := Nat.mod_eq_of_lt hdlt
    omega
  rcases lt_or_gt_of_ne hrs with hlt | hlt
  · exact hone hlt hs
  · exact (hone hlt hr).symm

/-- A positive-measure measurable piece of `J` with pairwise disjoint preimages of length `M`.
Aperiodicity kills short periods, and a compatible complete metric separates the rest. -/
private lemma exists_isDisjointPreimage_of_pos (ha : IsAperiodicModMeasure T μ) {M : ℕ}
    {J : Set Ω} (hJ : MeasurableSet J) (hJ0 : 0 < μ J) :
    ∃ F : Set Ω, MeasurableSet F ∧ F ⊆ J ∧ 0 < μ F ∧ IsDisjointPreimage T M F := by
  by_cases hM : M ≤ 1
  · refine ⟨J, hJ, subset_rfl, hJ0, hJ, ?_⟩
    intro i j hi hj hij
    omega
  · have hM' : 1 < M := by omega
    let Per : Set Ω := ⋃ k ∈ Finset.Ioo 0 M, {x | (T^[k]) x = x}
    have hPer0 : μ Per = 0 :=
      (measure_biUnion_null_iff (Finset.countable_toSet (Finset.Ioo 0 M))).mpr fun k hk =>
        ha k (Finset.mem_Ioo.mp hk).1
    obtain ⟨τ, hBorel, hPolish⟩ := (inferInstance : StandardBorelSpace Ω).polish
    let _ : TopologicalSpace Ω := τ
    have _ : BorelSpace Ω := hBorel
    have _ : PolishSpace Ω := hPolish
    let _ := TopologicalSpace.upgradeIsCompletelyMetrizable Ω
    have hsep_meas : ∀ δ : ℝ, MeasurableSet
        (⋂ k ∈ Finset.Ioo 0 M, {x | δ ≤ dist x ((T^[k]) x)}) := by
      intro δ
      refine MeasurableSet.biInter (Finset.countable_toSet _) fun k _ => ?_
      exact measurableSet_le measurable_const (measurable_id.dist (T.measurable.iterate k))
    have hscale : ∃ m : ℕ, 0 < μ (J ∩ ⋂ k ∈ Finset.Ioo 0 M,
        {x | (1 : ℝ) / (m + 1) ≤ dist x ((T^[k]) x)}) := by
      by_contra hnone
      have hzero : ∀ m : ℕ, μ (J ∩ ⋂ k ∈ Finset.Ioo 0 M,
          {x | (1 : ℝ) / (m + 1) ≤ dist x ((T^[k]) x)}) = 0 := by
        intro m
        have hnot : ¬ 0 < μ (J ∩ ⋂ k ∈ Finset.Ioo 0 M,
            {x | (1 : ℝ) / (m + 1) ≤ dist x ((T^[k]) x)}) := by
          intro hlt
          exact hnone ⟨m, hlt⟩
        have hμ : μ (J ∩ ⋂ k ∈ Finset.Ioo 0 M,
            {x | (1 : ℝ) / (m + 1) ≤ dist x ((T^[k]) x)}) ≤ 0 :=
          le_of_not_gt hnot
        exact le_antisymm hμ (zero_le (a := _))
      have hU : μ (⋃ m : ℕ, J ∩ ⋂ k ∈ Finset.Ioo 0 M,
          {x | (1 : ℝ) / (m + 1) ≤ dist x ((T^[k]) x)}) = 0 :=
        (measure_iUnion_null_iff).2 hzero
      have hcover : J \ Per ⊆ ⋃ m : ℕ, J ∩ ⋂ k ∈ Finset.Ioo 0 M,
          {x | (1 : ℝ) / (m + 1) ≤ dist x ((T^[k]) x)} := by
        intro x hx
        have hposd : ∀ k ∈ Finset.Ioo 0 M, 0 < dist x ((T^[k]) x) := by
          intro k hk
          exact dist_pos.mpr fun heq => hx.2 (mem_iUnion₂.2 ⟨k, hk, heq.symm⟩)
        have hne : (Finset.Ioo 0 M).Nonempty := ⟨1, Finset.mem_Ioo.mpr ⟨Nat.one_pos, hM'⟩⟩
        set δ0 : ℝ := (Finset.Ioo 0 M).inf' hne fun k => dist x ((T^[k]) x)
        have hδ0 : 0 < δ0 :=
          (Finset.lt_inf'_iff (f := fun k => dist x ((T^[k]) x)) hne).2 hposd
        have hmin : ∀ k ∈ Finset.Ioo 0 M, δ0 ≤ dist x ((T^[k]) x) :=
          (Finset.le_inf'_iff hne (fun k => dist x ((T^[k]) x))).mp le_rfl
        obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ0)
        have hmpos : 0 < (m : ℝ) := (one_div_pos.mpr hδ0).trans hm
        have hm0 : 0 < m := Nat.cast_pos.mp hmpos
        have h1m : (1 : ℝ) / m < δ0 := by
          rw [div_lt_iff₀ hmpos, mul_comm]
          exact (div_lt_iff₀ hδ0).mp hm
        refine mem_iUnion.2 ⟨m - 1, hx.1, ?_⟩
        rw [mem_iInter₂]
        intro k hk
        have hcoe : (((m - 1 : ℕ) + 1 : ℕ) : ℝ) = (m : ℝ) := by
          rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hm0)]
        have hle : (1 : ℝ) / (((m - 1 : ℕ) + 1 : ℕ) : ℝ) ≤ dist x ((T^[k]) x) := by
          rw [hcoe]
          exact h1m.le.trans (hmin k hk)
        simpa using hle
      have hdiff : μ (J \ Per) = μ J := measure_sdiff_null hPer0
      exact hJ0.ne' ((hdiff.symm.trans (measure_mono_null hcover hU)))
    obtain ⟨m, hmμ⟩ := hscale
    set δ : ℝ := 1 / (m + 1 : ℝ)
    have hδpos : 0 < δ := by positivity
    set E := J ∩ ⋂ k ∈ Finset.Ioo 0 M, {x | δ ≤ dist x ((T^[k]) x)}
    have hEmeas : MeasurableSet E := hJ.inter (hsep_meas δ)
    obtain ⟨s, hsCount, hsDense⟩ := TopologicalSpace.exists_countable_dense Ω
    have huniv : ⋃ c ∈ s, Metric.ball c (δ / 2) = univ :=
      (Metric.dense_iff_iUnion_ball s).1 hsDense _ (half_pos hδpos)
    have hball : ∃ c ∈ s, 0 < μ (E ∩ Metric.ball c (δ / 2)) := by
      by_contra hnone
      have hzero : ∀ c ∈ s, μ (E ∩ Metric.ball c (δ / 2)) = 0 := by
        intro c hc
        have hnot : ¬ 0 < μ (E ∩ Metric.ball c (δ / 2)) := by
          intro hlt
          exact hnone ⟨c, hc, hlt⟩
        have hμ : μ (E ∩ Metric.ball c (δ / 2)) ≤ 0 := le_of_not_gt hnot
        exact le_antisymm hμ (zero_le (a := _))
      have hU0 : μ (⋃ c ∈ s, E ∩ Metric.ball c (δ / 2)) = 0 :=
        (measure_biUnion_null_iff hsCount).2 hzero
      have hsub : E ⊆ ⋃ c ∈ s, E ∩ Metric.ball c (δ / 2) := by
        intro x hx
        have hxU : x ∈ ⋃ c ∈ s, Metric.ball c (δ / 2) := by simp [huniv]
        obtain ⟨c, hc, hxb⟩ := mem_iUnion₂.1 hxU
        exact mem_iUnion₂.2 ⟨c, hc, hx, hxb⟩
      exact hmμ.ne' (measure_mono_null hsub hU0)
    obtain ⟨c, hc, hc0⟩ := hball
    set F := E ∩ Metric.ball c (δ / 2)
    have hFmeas : MeasurableSet F := hEmeas.inter measurableSet_ball
    have hFsep : ∀ k, 0 < k → k < M → Disjoint F ((T^[k]) ⁻¹' F) := by
      intro k hk0 hkM
      rw [disjoint_left]
      intro x hx hxk
      have hge : δ ≤ dist x ((T^[k]) x) := by
        have hxE : x ∈ ⋂ j ∈ Finset.Ioo 0 M, {y | δ ≤ dist y ((T^[j]) y)} := hx.1.2
        simpa using mem_iInter₂.mp hxE k (Finset.mem_Ioo.mpr ⟨hk0, hkM⟩)
      have hlt : dist x ((T^[k]) x) < δ := by
        have h1 : dist x c < δ / 2 := Metric.mem_ball.mp hx.2
        have h2 : dist ((T^[k]) x) c < δ / 2 := Metric.mem_ball.mp hxk.2
        calc
          dist x ((T^[k]) x) ≤ dist x c + dist c ((T^[k]) x) := dist_triangle _ _ _
          _ = dist x c + dist ((T^[k]) x) c := by rw [dist_comm c]
          _ < δ / 2 + δ / 2 := add_lt_add h1 h2
          _ = δ := add_halves δ
      exact not_lt_of_ge hge hlt
    exact ⟨F, hFmeas, fun x hx => hx.1.1, hc0, IsDisjointPreimage.of_shifts T hFmeas hFsep⟩

/-- A small disjoint-preimage base whose forward saturation is conull. -/
private lemma exists_sweep (hT : MeasurePreserving T μ μ) (ha : IsAperiodicModMeasure T μ)
    {M : ℕ} (hM : 0 < M) :
    ∃ A : Set Ω, MeasurableSet A ∧ μ A ≤ 1 / (M : ℝ≥0∞) ∧ μ (forwardSat T A)ᶜ = 0 := by
  set A := sweep (μ := μ) T M
  have hAdisj : IsDisjointPreimage T M A := sweep_isDisjointPreimage T M hM
  have hAμ : μ A ≤ 1 / (M : ℝ≥0∞) := measure_le_inv T hT hM hAdisj
  have hHmeas : ∀ n, MeasurableSet (halfPiece (μ := μ) T M (cum (μ := μ) T M n)) :=
    fun n => (halfPiece_spec T M (cum (μ := μ) T M n)).1.1.1
  have hsumle : ∑' n, μ (halfPiece (μ := μ) T M (cum (μ := μ) T M n)) ≤ 1 := by
    calc
      ∑' n, μ (halfPiece (μ := μ) T M (cum (μ := μ) T M n))
          ≤ μ (⋃ n, halfPiece (μ := μ) T M (cum (μ := μ) T M n)) :=
            tsum_meas_le_meas_iUnion_of_disjoint μ hHmeas (halfPiece_pairwise T M hM)
      _ ≤ μ (Set.univ : Set Ω) :=
        measure_mono (subset_univ (⋃ n, halfPiece (μ := μ) T M (cum (μ := μ) T M n)))
      _ = 1 := measure_univ
  have hsumne : ∑' n, μ (halfPiece (μ := μ) T M (cum (μ := μ) T M n)) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hsumle
  have htail : Tendsto
      (fun n => 2 * ∑' k, μ (halfPiece (μ := μ) T M (cum (μ := μ) T M (k + n))))
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := 2)
      (ENNReal.tendsto_sum_nat_add
        (fun k => μ (halfPiece (μ := μ) T M (cum (μ := μ) T M k))) hsumne)
      (Or.inr (by simp))
  have hBilmeas : MeasurableSet (bilateral T A) := by
    have hfor : MeasurableSet (forwardSat T A) :=
      MeasurableSet.iUnion fun k => hAdisj.1.preimage (T.measurable.iterate k)
    have hback : MeasurableSet (forwardSat (⇑T.symm) A) :=
      MeasurableSet.iUnion fun k => hAdisj.1.preimage (T.symm.measurable.iterate k)
    exact hfor.union hback
  have hnbhd : ∀ n, orbitNbhd T M (cum (μ := μ) T M n) ⊆ bilateral T A := by
    intro n x hx
    have hcum : cum (μ := μ) T M n ⊆ A := cum_subset_sweep (μ := μ) T M n
    rcases hx with hx | hx
    · obtain ⟨d, _, hxd⟩ := mem_iUnion₂.1 hx
      exact Or.inl (mem_iUnion.2 ⟨d, hcum hxd⟩)
    · obtain ⟨d, _, hxd⟩ := mem_iUnion₂.1 hx
      exact Or.inr (mem_iUnion.2 ⟨d, hcum hxd⟩)
  have hBil0 : μ (bilateral T A)ᶜ = 0 := by
    by_contra hne
    have hpos : 0 < μ (bilateral T A)ᶜ := lt_of_le_of_ne (zero_le (a := _)) (Ne.symm hne)
    obtain ⟨F, hFmeas, hFsub, hF0, hFdisj⟩ :=
      exists_isDisjointPreimage_of_pos T ha hBilmeas.compl hpos
    have hFadm : ∀ n, IsAdmissible T M (cum (μ := μ) T M n) F := by
      intro n
      exact ⟨hFdisj, hFsub.trans (compl_subset_compl.mpr (hnbhd n))⟩
    have hFle : ∀ n, μ F ≤ 2 * μ (halfPiece (μ := μ) T M (cum (μ := μ) T M n)) := by
      intro n
      exact (le_csSup (adm_bddAbove T M (cum (μ := μ) T M n))
        (mem_image_of_mem μ (hFadm n))).trans (halfPiece_spec T M (cum (μ := μ) T M n)).2
    have htail_le : ∀ n, μ F ≤ 2 * ∑' k, μ (halfPiece (μ := μ) T M (cum (μ := μ) T M (k + n))) := by
      intro n
      exact (hFle n).trans (by
        simpa [Nat.zero_add] using mul_le_mul_right
          (ENNReal.le_tsum
            (f := fun k => μ (halfPiece (μ := μ) T M (cum (μ := μ) T M (k + n)))) 0) 2)
    obtain ⟨N, hN⟩ := eventually_atTop.mp (htail (isOpen_Iio.mem_nhds hF0))
    exact (hN N le_rfl).not_ge (htail_le N)
  set bad := {x | x ∈ A ∧ ¬ ∃ᶠ n in atTop, (T^[n]) x ∈ A}
  have hbad : μ bad = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    refine (hT.conservative.ae_mem_imp_frequently_image_mem hAdisj.1.nullMeasurableSet).mono ?_
    intro x hx hxb
    exact hxb.2 (hx hxb.1)
  set badOrbit := (⋃ k, (T^[k]) '' bad) ∪ (⋃ k, (T.symm^[k]) '' bad)
  have hbadOrbit : μ badOrbit = 0 := by
    have h1 : μ (⋃ k, (T^[k]) '' bad) = 0 :=
      (measure_iUnion_null_iff).2 fun k => measure_image_iterate_null T hT hbad k
    have h2 : μ (⋃ k, (T.symm^[k]) '' bad) = 0 :=
      (measure_iUnion_null_iff).2 fun k =>
        measure_image_iterate_null T.symm (MeasurePreserving.symm T hT) hbad k
    exact le_antisymm ((measure_union_le _ _).trans (by simp [h1, h2])) (zero_le (a := _))
  have hμF : μ (forwardSat T A)ᶜ = 0 := by
    have hsub : bilateral T A \ badOrbit ⊆ forwardSat T A := by
      intro x hx
      rcases hx.1 with hxF | hxB
      · exact hxF
      · obtain ⟨k, hk⟩ := mem_iUnion.1 hxB
        have hy : (T.symm^[k]) x ∈ A := hk
        have hxeq : (T^[k]) ((T.symm^[k]) x) = x := iterate_symm_apply T k x
        have hybad : (T.symm^[k]) x ∉ bad := by
          intro hbad'
          have hxbad : x ∈ (T^[k]) '' bad := ⟨(T.symm^[k]) x, hbad', hxeq⟩
          exact hx.2 (Or.inl (mem_iUnion.2 ⟨k, hxbad⟩))
        have hfreq : ∃ᶠ n in atTop, (T^[n]) ((T.symm^[k]) x) ∈ A := by
          by_contra hnot
          exact hybad ⟨hy, hnot⟩
        obtain ⟨n, hnk, hnA⟩ := frequently_atTop.mp hfreq k
        refine mem_iUnion.2 ⟨n - k, ?_⟩
        show (T^[n - k]) x ∈ A
        have hshift : (T^[n - k]) x = (T^[n]) ((T.symm^[k]) x) := by
          conv_lhs => rw [← hxeq]
          rw [iterate_apply_add T (n - k) k ((T.symm^[k]) x), Nat.add_sub_of_le hnk]
        rw [hshift]
        exact hnA
    have hcompl : (forwardSat T A)ᶜ ⊆ (bilateral T A)ᶜ ∪ badOrbit := by
      intro x hx
      by_cases hb : x ∈ bilateral T A
      · exact Or.inr (by
          by_contra hnot
          exact hx (hsub ⟨hb, hnot⟩))
      · exact Or.inl hb
    have hunion : μ ((bilateral T A)ᶜ ∪ badOrbit) = 0 :=
      le_antisymm ((measure_union_le _ _).trans (by simp [hBil0, hbadOrbit])) (zero_le (a := _))
    exact measure_mono_null hcompl hunion
  exact ⟨A, hAdisj.1, hAμ, hμF⟩

/-- A Rokhlin base cut from a measurable set whose forward saturation is conull. -/
private lemma exists_tower_of_forward (hT : MeasurePreserving T μ μ) {A : Set Ω}
    (hA : MeasurableSet A) (hF : μ (forwardSat T A)ᶜ = 0) {n : ℕ} (hn : 0 < n) :
    ∃ B : Set Ω, MeasurableSet B ∧
      (∀ i j, i < n → j < n → i ≠ j → Disjoint (towerLevel T B i) (towerLevel T B j)) ∧
      μ (⋃ i ∈ Finset.range n, towerLevel T B i)ᶜ ≤ (n : ℝ≥0∞) * μ A := by
  set S := skyscraper T A n
  have hent : ∀ k, MeasurableSet (entrance T A k) := by
    intro k
    exact (hA.preimage (T.measurable.iterate k)).diff
      (MeasurableSet.biUnion (Finset.countable_toSet _) fun j _ =>
        hA.preimage (T.measurable.iterate j))
  have hS : MeasurableSet S := MeasurableSet.iUnion fun q => hent _
  set B := (T^[n - 1]) ⁻¹' S
  have hB : MeasurableSet B := hS.preimage (T.measurable.iterate (n - 1))
  have hlevel : ∀ i, i < n → towerLevel T B i = (T^[n - 1 - i]) ⁻¹' S := by
    intro i hi
    ext x
    rw [towerLevel, image_iterate_eq_preimage_symm, mem_preimage, mem_preimage]
    change (T^[n - 1]) ((T.symm^[i]) x) ∈ S ↔ (T^[n - 1 - i]) x ∈ S
    have hi' : i ≤ n - 1 := by omega
    have hinv : (T^[i]) ((T.symm^[i]) x) = x := iterate_symm_apply T i x
    have hsum : i + (n - 1 - i) = n - 1 := Nat.add_sub_of_le hi'
    have hcomp : (T^[n - 1]) ((T.symm^[i]) x) =
        (T^[n - 1 - i]) ((T^[i]) ((T.symm^[i]) x)) := by
      conv_lhs => rw [← hsum]
      exact (iterate_apply_add T (n - 1 - i) i ((T.symm^[i]) x)).symm
    rw [hcomp, hinv]
  have hdisj : ∀ i j, i < n → j < n → i ≠ j →
      Disjoint (towerLevel T B i) (towerLevel T B j) := by
    intro i j hi hj hij
    rw [hlevel i hi, hlevel j hj]
    exact disjoint_skyscraper_shifts T hn (by omega) (by omega) (by omega)
  set C := ⋃ i ∈ Finset.range n, towerLevel T B i
  set small := ⋃ j ∈ Finset.range n, entrance T A j
  have hsmall : μ small ≤ (n : ℝ≥0∞) * μ A := by
    calc
      μ small ≤ ∑ j ∈ Finset.range n, μ (entrance T A j) := measure_biUnion_finset_le _ _
      _ ≤ ∑ j ∈ Finset.range n, μ A := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact (measure_mono (sdiff_subset (s := (T^[j]) ⁻¹' A))).trans_eq
          (measure_preimage_iterate T hT hA j)
      _ = (n : ℝ≥0∞) * μ A := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hforward : forwardSat T A \ small ⊆ C := by
    intro x hx
    have hex : ∃ k, (T^[k]) x ∈ A := by simpa [forwardSat, mem_iUnion] using hx.1
    have : DecidablePred (fun k : ℕ => (T^[k]) x ∈ A) := fun _ => Classical.propDecidable _
    set m := Nat.find hex
    have hmA : (T^[m]) x ∈ A := Nat.find_spec hex
    have hmmin : ∀ j < m, (T^[j]) x ∉ A := fun j hj => Nat.find_min hex hj
    have hment : x ∈ entrance T A m := by
      refine ⟨hmA, ?_⟩
      intro hmem
      obtain ⟨j, hj, hjA⟩ := mem_iUnion₂.1 hmem
      exact hmmin j (Finset.mem_range.mp hj) hjA
    have hmn : n ≤ m := by
      by_contra hlt
      exact hx.2 (mem_iUnion₂.2 ⟨m, Finset.mem_range.mpr (Nat.lt_of_not_ge hlt), hment⟩)
    set r := m % n
    have hr : r < n := Nat.mod_lt _ hn
    have hent_r : (T^[r]) x ∈ entrance T A (m - r) :=
      mem_entrance_iterate T (Nat.mod_le _ _) hment
    have hsubeq : m - r = m / n * n :=
      (Nat.sub_eq_iff_eq_add (by simpa [r] using Nat.mod_le m n)).mpr
        (by simpa [r] using (Nat.div_add_mod' m n).symm)
    have hmult : m - r = (m / n - 1 + 1) * n := by
      have hq : 1 ≤ m / n := Nat.succ_le_of_lt (Nat.div_pos hmn hn)
      rw [hsubeq, Nat.sub_add_cancel hq]
    have hSk : (T^[r]) x ∈ S := by
      rw [hmult] at hent_r
      exact mem_iUnion.2 ⟨m / n - 1, hent_r⟩
    have hrn : n - 1 - r < n := by omega
    have hshift : n - 1 - (n - 1 - r) = r := by omega
    have hxC : x ∈ (T^[r]) ⁻¹' S := hSk
    rw [← hshift] at hxC
    exact mem_iUnion₂.2 ⟨n - 1 - r, Finset.mem_range.mpr hrn, (hlevel (n - 1 - r) hrn).symm ▸ hxC⟩
  have hcompl : Cᶜ ⊆ small ∪ (forwardSat T A)ᶜ := by
    intro x hx
    by_cases hxF : x ∈ forwardSat T A
    · by_cases hxs : x ∈ small
      · exact Or.inl hxs
      · exact (hx (hforward ⟨hxF, hxs⟩)).elim
    · exact Or.inr hxF
  have hμ : μ Cᶜ ≤ (n : ℝ≥0∞) * μ A :=
    calc
      μ Cᶜ ≤ μ (small ∪ (forwardSat T A)ᶜ) := measure_mono hcompl
      _ ≤ μ small + μ (forwardSat T A)ᶜ := measure_union_le _ _
      _ = μ small := by simp [hF]
      _ ≤ (n : ℝ≥0∞) * μ A := hsmall
  exact ⟨B, hB, hdisj, hμ⟩

end Rokhlin

/-- **10.9**, Rokhlin's tower lemma for a standard Borel probability system with a bimeasurable
invertible transformation. The height is positive; no tower exists at height zero with near-full
  mass. -/
theorem rokhlin_tower [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ) (ha : IsAperiodicModMeasure T μ)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : Set Ω, MeasurableSet B ∧
      (∀ i j : ℕ, i < n → j < n → i ≠ j → Disjoint (towerLevel T B i) (towerLevel T B j)) ∧
      1 - ENNReal.ofReal ε < μ (⋃ i ∈ Finset.range n, towerLevel T B i) := by
  obtain ⟨M, hM⟩ := exists_nat_gt ((n : ℝ) / min ε 1)
  have hδ : 0 < min ε (1 : ℝ) := lt_min hε zero_lt_one
  have hM0 : 0 < M := Nat.cast_pos.mp ((div_nonneg (Nat.cast_nonneg n) hδ.le).trans_lt hM)
  have hdiv : (n : ℝ) / M < min ε 1 := by
    rw [div_lt_iff₀ (Nat.cast_pos.mpr hM0), mul_comm]
    exact (div_lt_iff₀ hδ).mp hM
  have hcoe : ENNReal.ofReal ((n : ℝ) / M) = (n : ℝ≥0∞) / M := by
    rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hM0)]
    simp
  have hη : ENNReal.ofReal ((n : ℝ) / M) < min (ENNReal.ofReal ε) 1 := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_min]
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).2 hdiv
  obtain ⟨A, hA, hAμ, hF⟩ := exists_sweep (μ := μ) T hT ha hM0
  have hprod : (n : ℝ≥0∞) * μ A ≤ ENNReal.ofReal ((n : ℝ) / M) :=
    calc
      (n : ℝ≥0∞) * μ A ≤ (n : ℝ≥0∞) * (1 / (M : ℝ≥0∞)) := mul_le_mul_right hAμ _
      _ = (n : ℝ≥0∞) / M := by simp [div_eq_mul_inv]
      _ = ENNReal.ofReal ((n : ℝ) / M) := hcoe.symm
  obtain ⟨B, hB, hdisj, hcompl⟩ := exists_tower_of_forward T hT hA hF hn
  refine ⟨B, hB, hdisj, ?_⟩
  set C := ⋃ i ∈ Finset.range n, towerLevel T B i
  have hCmeas : MeasurableSet C := by
    refine MeasurableSet.biUnion (Finset.countable_toSet _) fun i _ => ?_
    rw [towerLevel, image_iterate_eq_preimage_symm T]
    exact hB.preimage (T.symm.measurable.iterate i)
  have hC1 : μ C ≤ 1 := by
    calc
      μ C ≤ μ (Set.univ : Set Ω) := measure_mono (Set.subset_univ C)
      _ = 1 := measure_univ
  have hCc : μ Cᶜ < min (ENNReal.ofReal ε) 1 := (hcompl.trans hprod).trans_lt hη
  have hCeq : μ C = 1 - μ Cᶜ := by
    have hcompl_eq : μ Cᶜ = 1 - μ C := prob_compl_eq_one_sub hCmeas
    rw [hcompl_eq, ENNReal.sub_sub_cancel ENNReal.one_ne_top hC1]
  by_cases hε1 : ENNReal.ofReal ε ≤ 1
  · rw [hCeq]
    exact one_sub_lt_one_sub hε1 (lt_min_iff.mp hCc).1
  · rw [tsub_eq_zero_of_le (lt_of_not_ge hε1).le, hCeq]
    exact tsub_pos_iff_lt.mpr (lt_min_iff.mp hCc).2

/-- The intersection measuring an arithmetic progression of `k+1` return times. -/
def multipleRecurrenceSet (T : Ω → Ω) (A : Set Ω) (k n : ℕ) : Set Ω :=
  ⋂ j ∈ Finset.range (k + 1), (T^[j * n]) ⁻¹' A

/-- Finite averages of real masses of arithmetic-progression intersections. -/
def multipleRecurrenceAverage (T : Ω → Ω) (A : Set Ω) (μ : Measure Ω)
    (k N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, (μ (multipleRecurrenceSet T A k (n + 1))).toReal

/-- **10.48**, Furstenberg multiple recurrence in positive-liminf form.
Lengths `k≥2` select the nontrivial gap beyond the mean-ergodic `k=1` case. -/
theorem furstenberg_multiple_recurrence [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) (hpos : 0 < μ A)
    {k : ℕ} (hk : 2 ≤ k) :
    0 < liminf (multipleRecurrenceAverage T A μ k) atTop := by
  unfold multipleRecurrenceAverage multipleRecurrenceSet
  exact multiple_recurrence_liminf hT hA hpos hk

end CKMA
