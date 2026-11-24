/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.Probability.Independence.Integration

/-!
# Kolmogorov's maximal inequality for finite independent families

First-hitting decomposition and Kolmogorov's maximal inequality for partial sums of a finite
independent mean-zero square-integrable family.

## Main definitions

* `CKMA.Kolmogorov.pastFinset`: indices strictly before a partial-sum time `k`.
* `CKMA.Kolmogorov.partialSum`: sum of a finite family over indices strictly before `k`.

## Main results

* `CKMA.Kolmogorov.measure_exists_le_abs_partialSum_le`: Kolmogorov's maximal inequality for
  partial sums of a finite independent mean-zero `L²` family.
-/

public section

noncomputable section

namespace CKMA.Kolmogorov

open scoped NNReal ENNReal ProbabilityTheory BigOperators
open MeasureTheory ProbabilityTheory

/-- Indices strictly before a partial-sum time. -/
@[expose]
def pastFinset (n : ℕ) (k : Fin (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ i.val < k.val

/-- Indices at or after a partial-sum time. -/
private def futureFinset (n : ℕ) (k : Fin (n + 1)) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ k.val ≤ i.val

/-- Sum of the family over indices strictly before `k`. -/
@[expose]
def partialSum {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (k : Fin (n + 1)) : Ω → ℝ :=
  fun ω ↦ ∑ i ∈ pastFinset n k, X i ω

/-- The last partial sum is the sum of the whole family. -/
lemma partialSum_last {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (ω : Ω) :
    partialSum X (Fin.last n) ω = ∑ i : Fin n, X i ω := by
  have hpast : pastFinset n (Fin.last n) = Finset.univ := by
    ext i
    simp [pastFinset, Fin.val_last, i.isLt]
  simp [partialSum, hpast]

/-- Past and future index sets partition the family. -/
private lemma past_future_partition (n : ℕ) (k : Fin (n + 1)) :
    Disjoint (pastFinset n k) (futureFinset n k) ∧
      pastFinset n k ∪ futureFinset n k = Finset.univ := by
  constructor
  · rw [Finset.disjoint_left]
    intro i hi hf
    exact not_le_of_gt (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hf).2
  · ext i
    constructor
    · intro _
      exact Finset.mem_univ i
    · intro _
      rcases lt_or_ge i.val k.val with hlt | hge
      · exact Finset.mem_union_left _ (by simp [pastFinset, hlt])
      · exact Finset.mem_union_right _ (by simp [futureFinset, hge])

/-- The full sum splits as the partial sum plus the future sum. -/
private lemma partialSum_add_future {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ)
    (k : Fin (n + 1)) (ω : Ω) :
    partialSum X (Fin.last n) ω =
      partialSum X k ω + ∑ i ∈ futureFinset n k, X i ω := by
  have hlast : pastFinset n (Fin.last n) = Finset.univ := by
    ext i
    simp [pastFinset, Fin.val_last, i.isLt]
  rw [partialSum, partialSum, hlast, ← (past_future_partition n k).2,
    Finset.sum_union (past_future_partition n k).1]

/-- First time the partial sums reach height `ε`. -/
private def firstHitSet {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (ε : ℝ)
    (k : Fin (n + 1)) : Set Ω :=
  {ω | ε ≤ |partialSum X k ω|} ∩
    {ω | ∀ j : Fin (n + 1), j < k → |partialSum X j ω| < ε}

/-- Partial sums of a measurable family are measurable. -/
private lemma measurable_partialSum {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {X : Fin n → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (k : Fin (n + 1)) :
    Measurable (partialSum X k) :=
  Finset.measurable_sum (pastFinset n k) fun i _ ↦ hX i

/-- The first-hit set of a measurable family is measurable. -/
private lemma measurableSet_firstHit {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {X : Fin n → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (ε : ℝ) (k : Fin (n + 1)) :
    MeasurableSet (firstHitSet X ε k) := by
  refine MeasurableSet.inter ?_ ?_
  · exact measurableSet_le measurable_const
      (continuous_abs.measurable.comp (measurable_partialSum hX k))
  · have hset : {ω | ∀ j : Fin (n + 1), j < k → |partialSum X j ω| < ε} =
        ⋂ j : {j : Fin (n + 1) // j < k}, {ω | |partialSum X j.1 ω| < ε} := by
      ext ω
      simp
    rw [hset]
    refine MeasurableSet.iInter fun j ↦ ?_
    exact measurableSet_lt
      (continuous_abs.measurable.comp (measurable_partialSum hX j.1)) measurable_const

/-- Distinct first-hit sets are disjoint. -/
private lemma pairwise_firstHit {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (ε : ℝ) :
    Pairwise fun k m ↦ Disjoint (firstHitSet X ε k) (firstHitSet X ε m) := by
  intro k m hkm
  rcases lt_or_gt_of_ne hkm with hlt | hgt
  · refine Set.disjoint_left.2 fun ω hωk hωm ↦ ?_
    have hltAbs : |partialSum X k ω| < ε := hωm.2 k hlt
    have hge : ε ≤ |partialSum X k ω| := hωk.1
    exact not_lt_of_ge hge hltAbs
  · refine Set.disjoint_left.2 fun ω hωk hωm ↦ ?_
    have hltAbs : |partialSum X m ω| < ε := hωk.2 m hgt
    have hge : ε ≤ |partialSum X m ω| := hωm.1
    exact not_lt_of_ge hge hltAbs

/-- The first-hit sets cover every path whose partial sums reach height `ε`. -/
private lemma iUnion_firstHit {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) (ε : ℝ) :
    ⋃ k, firstHitSet X ε k = {ω | ∃ k : Fin (n + 1), ε ≤ |partialSum X k ω|} := by
  ext ω
  constructor
  · intro hω
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hω
    exact ⟨k, hk.1⟩
  · intro hω
    obtain ⟨k0, hk0⟩ := hω
    let s : Finset (Fin (n + 1)) :=
      Finset.univ.filter fun k ↦ ε ≤ |partialSum X k ω|
    have hs : s.Nonempty := ⟨k0, by simp [s, hk0]⟩
    let k := s.min' hs
    have hkmem : k ∈ s := Finset.min'_mem s hs
    have hkle : ε ≤ |partialSum X k ω| := by
      simpa [s] using hkmem
    have hearly : ∀ j : Fin (n + 1), j < k → |partialSum X j ω| < ε := by
      intro j hj
      have hnot : j ∉ s := by
        intro hjs
        have hmin := Finset.min'_le s j hjs
        exact not_le_of_gt hj hmin
      have hlt : ¬ ε ≤ |partialSum X j ω| := by simpa [s] using hnot
      exact lt_of_not_ge hlt
    exact Set.mem_iUnion.2 ⟨k, ⟨hkle, hearly⟩⟩

/-- Partial sum of a past tuple, using only coordinates before `j`. -/
private def subtypeSum {n : ℕ} (k j : Fin (n + 1))
    (f : {i : Fin n // i ∈ pastFinset n k} → ℝ) : ℝ :=
  ∑ i : pastFinset n k, if i.1.val < j.val then f i else 0

/-- Value of the past tuple on the first-hit event, and zero otherwise. -/
private def hitOfPast {n : ℕ} (k : Fin (n + 1)) (ε : ℝ)
    (f : {i : Fin n // i ∈ pastFinset n k} → ℝ) : ℝ :=
  if (∀ j : Fin (n + 1), j < k → |subtypeSum k j f| < ε) ∧ ε ≤ |subtypeSum k k f| then
    subtypeSum k k f else 0

/-- Sum of a future tuple. -/
private def tailOfFuture {n : ℕ} (k : Fin (n + 1))
    (g : {i : Fin n // i ∈ futureFinset n k} → ℝ) : ℝ :=
  ∑ i, g i

/-- A coordinatewise truncated sum of a tuple is measurable. -/
private lemma measurable_subtypeSum {n : ℕ} (k j : Fin (n + 1)) :
    Measurable (subtypeSum k j) := by
  unfold subtypeSum
  refine Finset.measurable_sum Finset.univ fun i _ ↦ ?_
  by_cases h : i.1.val < j.val
  · simpa [h] using measurable_pi_apply i
  · simpa [h] using measurable_const

/-- The first-hit functional of the past tuple is measurable. -/
private lemma measurable_hitOfPast {n : ℕ} (k : Fin (n + 1)) (ε : ℝ) :
    Measurable (hitOfPast k ε) := by
  have hset : MeasurableSet {f |
      (∀ j : Fin (n + 1), j < k → |subtypeSum k j f| < ε) ∧
        ε ≤ |subtypeSum k k f|} := by
    have hrewrite : {f |
        (∀ j : Fin (n + 1), j < k → |subtypeSum k j f| < ε) ∧
          ε ≤ |subtypeSum k k f|} =
        (⋂ j : {j : Fin (n + 1) // j < k}, {f | |subtypeSum k j.1 f| < ε}) ∩
          {f | ε ≤ |subtypeSum k k f|} := by
      ext f
      simp
    rw [hrewrite]
    refine MeasurableSet.inter ?_ ?_
    · refine MeasurableSet.iInter fun j ↦ ?_
      exact measurableSet_lt (continuous_abs.measurable.comp (measurable_subtypeSum k j.1))
        measurable_const
    · exact measurableSet_le measurable_const
        (continuous_abs.measurable.comp (measurable_subtypeSum k k))
  unfold hitOfPast
  exact (measurable_subtypeSum k k).ite hset measurable_const

/-- The future-sum functional is measurable. -/
private lemma measurable_tailOfFuture {n : ℕ} (k : Fin (n + 1)) :
    Measurable (tailOfFuture k) := by
  unfold tailOfFuture
  exact Finset.measurable_sum Finset.univ fun i _ ↦ measurable_pi_apply i

/-- Reading the past from the family reproduces partial sums up to time `k`. -/
private lemma subtypeSum_eq_partialSum {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ)
    (k j : Fin (n + 1)) (hj : j ≤ k) (ω : Ω) :
    subtypeSum k j (fun i ↦ X i.1 ω) = partialSum X j ω := by
  rw [subtypeSum, partialSum]
  have hcoe := Finset.sum_coe_sort (s := pastFinset n k)
    (fun i ↦ if i.val < j.val then X i ω else 0)
  rw [hcoe, ← Finset.sum_filter]
  have hjv : j.val ≤ k.val := (Fin.le_def).mp hj
  have hfilt : (pastFinset n k).filter (fun i ↦ i.val < j.val) = pastFinset n j := by
    ext i
    simp only [pastFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨lt_of_lt_of_le h hjv, h⟩
  rw [hfilt]

/-- The past functional reproduces the partial sum on the first-hit set. -/
private lemma hitOfPast_eq_indicator {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ)
    (k : Fin (n + 1)) (ε : ℝ) (ω : Ω) :
    hitOfPast k ε (fun i ↦ X i.1 ω) =
      (firstHitSet X ε k).indicator (partialSum X k) ω := by
  have hps : ∀ j : Fin (n + 1), j ≤ k →
      subtypeSum k j (fun i ↦ X i.1 ω) = partialSum X j ω :=
    fun j hj ↦ subtypeSum_eq_partialSum X k j hj ω
  by_cases hmem : ω ∈ firstHitSet X ε k
  · rw [Set.indicator_of_mem hmem]
    have hcond : (∀ j : Fin (n + 1), j < k →
        |subtypeSum k j (fun i ↦ X i.1 ω)| < ε) ∧
        ε ≤ |subtypeSum k k (fun i ↦ X i.1 ω)| := by
      constructor
      · intro j hj
        rw [hps j hj.le]
        exact hmem.2 j hj
      · rw [hps k le_rfl]
        exact hmem.1
    rw [hitOfPast, ite_eq_left hcond]
    exact hps k le_rfl
  · rw [Set.indicator_of_notMem hmem]
    have hcond : ¬ ((∀ j : Fin (n + 1), j < k →
        |subtypeSum k j (fun i ↦ X i.1 ω)| < ε) ∧
        ε ≤ |subtypeSum k k (fun i ↦ X i.1 ω)|) := by
      intro h
      apply hmem
      refine ⟨?_, ?_⟩
      · have h2 := h.2
        rw [hps k le_rfl] at h2
        exact h2
      · intro j hj
        have h1 := h.1 j hj
        rw [hps j hj.le] at h1
        exact h1
    rw [hitOfPast, ite_eq_right hcond]

/-- The future functional reproduces the future sum. -/
private lemma tailOfFuture_eq {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ)
    (k : Fin (n + 1)) (ω : Ω) :
    tailOfFuture k (fun i ↦ X i.1 ω) = ∑ i ∈ futureFinset n k, X i ω := by
  unfold tailOfFuture
  exact Finset.sum_coe_sort (s := futureFinset n k) (f := fun i ↦ X i ω)

/-- On a first-hit set, the squared full sum dominates `ε ^ 2` times the measure. -/
private lemma firstHit_integral_lower {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hLp : ∀ i, MemLp (X i) 2 μ) (hind : iIndepFun X μ) {ε : ℝ} (hε : 0 < ε)
    (k : Fin (n + 1)) :
    ε ^ 2 * μ.real (firstHitSet X ε k) ≤
      ∫ ω, (firstHitSet X ε k).indicator
        (fun ω ↦ (partialSum X (Fin.last n) ω) ^ 2) ω ∂μ := by
  let A := firstHitSet X ε k
  have hA : MeasurableSet A := measurableSet_firstHit hX ε k
  let Sk := partialSum X k
  let tail : Ω → ℝ := fun ω ↦ ∑ i ∈ futureFinset n k, X i ω
  have hsplit : ∀ ω, partialSum X (Fin.last n) ω = Sk ω + tail ω :=
    fun ω ↦ partialSum_add_future X k ω
  have hSkLp : MemLp Sk 2 μ := by
    unfold Sk partialSum
    exact memLp_finsetSum (pastFinset n k) fun i _ ↦ hLp i
  have htailLp : MemLp tail 2 μ :=
    memLp_finsetSum (futureFinset n k) fun i _ ↦ hLp i
  have hSkSq : Integrable (fun ω ↦ Sk ω ^ 2) μ := hSkLp.integrable_sq
  have htailSq : Integrable (fun ω ↦ tail ω ^ 2) μ := htailLp.integrable_sq
  have hprod : Integrable (fun ω ↦ Sk ω * tail ω) μ := by
    convert hSkLp.integrable_mul htailLp using 1
  have hInd1 : Integrable (A.indicator fun ω ↦ Sk ω ^ 2) μ := hSkSq.indicator hA
  have hInd2 : Integrable (A.indicator fun ω ↦ Sk ω * tail ω) μ := hprod.indicator hA
  have hInd3 : Integrable (A.indicator fun ω ↦ tail ω ^ 2) μ := htailSq.indicator hA
  have hcross : ∫ ω, A.indicator (fun ω ↦ Sk ω * tail ω) ω ∂μ = 0 := by
    let pastRead : Ω → {i : Fin n // i ∈ pastFinset n k} → ℝ := fun ω i ↦ X i.1 ω
    let futureRead : Ω → {i : Fin n // i ∈ futureFinset n k} → ℝ := fun ω i ↦ X i.1 ω
    have hpastMeas : Measurable pastRead :=
      Measurable.of_eval fun i ↦ hX i.1
    have hfutureMeas : Measurable futureRead :=
      Measurable.of_eval fun i ↦ hX i.1
    have hdisj : Disjoint (pastFinset n k) (futureFinset n k) :=
      (past_future_partition n k).1
    have hindep := (hind.indepFun_finset (pastFinset n k) (futureFinset n k) hdisj hX).comp
      (measurable_hitOfPast k ε) (measurable_tailOfFuture k)
    let Xp : Ω → ℝ := fun ω ↦ hitOfPast k ε (pastRead ω)
    let Yf : Ω → ℝ := fun ω ↦ tailOfFuture k (futureRead ω)
    have hindep' : Xp ⟂ᵢ[μ] Yf := by
      simpa [Xp, Yf, Function.comp_def] using hindep
    have hfac := hindep'.integral_fun_mul_eq_mul_integral
      ((measurable_hitOfPast k ε).comp hpastMeas).aestronglyMeasurable
      ((measurable_tailOfFuture k).comp hfutureMeas).aestronglyMeasurable
    have hpoint : (fun ω ↦ Xp ω * Yf ω) = A.indicator (fun ω ↦ Sk ω * tail ω) := by
      ext ω
      unfold Xp Yf pastRead futureRead Sk tail
      rw [hitOfPast_eq_indicator X k ε ω, tailOfFuture_eq X k ω]
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
        ring
    have htail0 : ∫ ω, Yf ω ∂μ = 0 := by
      have hint : ∀ i ∈ futureFinset n k, Integrable (X i) μ := by
        intro i _
        exact memLp_one_iff_integrable.1
          ((hLp i).mono_exponent (by simp : (1 : ℝ≥0∞) ≤ 2))
      rw [show (fun ω ↦ Yf ω) = fun ω ↦ ∑ i ∈ futureFinset n k, X i ω by
        ext ω; exact tailOfFuture_eq X k ω, integral_finsetSum _ hint]
      exact Finset.sum_eq_zero fun i _ ↦ hmean i
    rw [← hpoint, hfac, htail0, mul_zero]
  have hexpand : ∫ ω, A.indicator (fun ω ↦ (partialSum X (Fin.last n) ω) ^ 2) ω ∂μ =
      ∫ ω, A.indicator (fun ω ↦ Sk ω ^ 2) ω ∂μ +
      2 * ∫ ω, A.indicator (fun ω ↦ Sk ω * tail ω) ω ∂μ +
      ∫ ω, A.indicator (fun ω ↦ tail ω ^ 2) ω ∂μ := by
    have hpt : ∀ ω, A.indicator (fun η ↦ (partialSum X (Fin.last n) η) ^ 2) ω =
        A.indicator (fun η ↦ Sk η ^ 2) ω +
        2 * A.indicator (fun η ↦ Sk η * tail η) ω +
        A.indicator (fun η ↦ tail η ^ 2) ω := by
      intro ω
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, Set.indicator_of_mem hω,
          Set.indicator_of_mem hω, hsplit ω]
        ring
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω,
          Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
        ring
    rw [integral_congr_ae (ae_of_all _ hpt), integral_add, integral_add, integral_const_mul]
    · exact hInd1
    · exact hInd2.const_mul 2
    · exact hInd1.add (hInd2.const_mul 2)
    · exact hInd3
  have hsqLower : ε ^ 2 * μ.real A ≤ ∫ ω, A.indicator (fun ω ↦ Sk ω ^ 2) ω ∂μ := by
    have hpt : ∀ ω, ε ^ 2 * A.indicator (1 : Ω → ℝ) ω ≤
        A.indicator (fun η ↦ Sk η ^ 2) ω := by
      intro ω
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
        simp only [Pi.one_apply, mul_one]
        have hsqAbs : |ε| ≤ |partialSum X k ω| := by
          rw [abs_of_pos hε]
          exact hω.1
        simpa [Sk] using sq_le_sq.mpr hsqAbs
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
        simp
    have hint : Integrable (fun ω ↦ ε ^ 2 * A.indicator (1 : Ω → ℝ) ω) μ :=
      (integrable_const _).indicator hA |>.const_mul _
    rw [← integral_indicator_one hA, ← integral_const_mul]
    exact integral_mono hint hInd1 hpt
  have htailNonneg : 0 ≤ ∫ ω, A.indicator (fun ω ↦ tail ω ^ 2) ω ∂μ :=
    integral_nonneg fun ω ↦ by
      by_cases hω : ω ∈ A
      · simp [Set.indicator_of_mem hω, sq_nonneg]
      · simp [Set.indicator_of_notMem hω]
  linarith [hcross, hexpand, hsqLower, htailNonneg]

/-- **Kolmogorov's maximal inequality** for a finite independent mean-zero square-integrable
family: `μ {∃ k, ε ≤ |S_k|} ≤ E[S_n²] / ε²`. -/
lemma measure_exists_le_abs_partialSum_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hLp : ∀ i, MemLp (X i) 2 μ) (hind : iIndepFun X μ) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ∃ k : Fin (n + 1), ε ≤ |partialSum X k ω|} ≤
      ENNReal.ofReal ((∫ ω, (partialSum X (Fin.last n) ω) ^ 2 ∂μ) / ε ^ 2) := by
  have hmeas : ∀ k, MeasurableSet (firstHitSet X ε k) := fun k ↦ measurableSet_firstHit hX ε k
  have hSLp : MemLp (partialSum X (Fin.last n)) 2 μ := by
    unfold partialSum
    rw [show pastFinset n (Fin.last n) = Finset.univ by
      ext i; simp [pastFinset, Fin.val_last, i.isLt]]
    exact memLp_finsetSum (Finset.univ : Finset (Fin n)) fun i _ ↦ hLp i
  have hSSq : Integrable (fun ω ↦ (partialSum X (Fin.last n) ω) ^ 2) μ := hSLp.integrable_sq
  have hsumLe : ε ^ 2 * μ.real (⋃ k, firstHitSet X ε k) ≤
      ∫ ω, (partialSum X (Fin.last n) ω) ^ 2 ∂μ := by
    rw [measureReal_iUnion_fintype (pairwise_firstHit X ε) hmeas
      (fun _ ↦ measure_ne_top μ _)]
    rw [Finset.mul_sum]
    have hint : ∑ k, ∫ ω, (firstHitSet X ε k).indicator
        (fun ω ↦ (partialSum X (Fin.last n) ω) ^ 2) ω ∂μ ≤
        ∫ ω, (partialSum X (Fin.last n) ω) ^ 2 ∂μ := by
      rw [← integral_finsetSum]
      · have hpt : ∀ ω, ∑ k, (firstHitSet X ε k).indicator
            (fun η ↦ (partialSum X (Fin.last n) η) ^ 2) ω ≤
            (partialSum X (Fin.last n) ω) ^ 2 := by
          intro ω
          have hdisj := pairwise_firstHit X ε
          by_cases hmem : ω ∈ ⋃ k, firstHitSet X ε k
          · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hmem
            rw [Finset.sum_eq_single k]
            · rw [Set.indicator_of_mem hk]
            · intro m _ hmk
              have hnot : ω ∉ firstHitSet X ε m :=
                Set.disjoint_left.1 (hdisj hmk.symm) hk
              rw [Set.indicator_of_notMem hnot]
            · intro hknot
              exact (hknot (Finset.mem_univ k)).elim
          · rw [Finset.sum_eq_zero]
            · exact sq_nonneg _
            · intro k _
              have hnot : ω ∉ firstHitSet X ε k := by
                intro hk
                exact hmem (Set.mem_iUnion.2 ⟨k, hk⟩)
              rw [Set.indicator_of_notMem hnot]
        exact integral_mono
          (integrable_finsetSum _ fun k _ ↦ hSSq.indicator (hmeas k)) hSSq hpt
      · intro k _
        exact hSSq.indicator (hmeas k)
    refine le_trans (Finset.sum_le_sum fun k _ ↦ firstHit_integral_lower hX hmean hLp hind hε k)
      hint
  have hreal : μ.real {ω | ∃ k : Fin (n + 1), ε ≤ |partialSum X k ω|} ≤
      (∫ ω, (partialSum X (Fin.last n) ω) ^ 2 ∂μ) / ε ^ 2 := by
    rw [← iUnion_firstHit X ε, le_div_iff₀ (sq_pos_of_pos hε), mul_comm]
    exact hsumLe
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_le_ofReal hreal

end CKMA.Kolmogorov
