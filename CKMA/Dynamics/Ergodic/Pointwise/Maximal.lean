/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

import Mathlib.Tactic

/-!
# The maximal ergodic inequality

Garsia's proof that the integral of an integrable observable over the set where a positive-length
Birkhoff sum is strictly positive is nonnegative. The finite sets increase to the strict supremum
set, and the inequality passes to strictly invariant subsets.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Finset MeasureTheory Filter Set Function
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Partial maxima of the Birkhoff sums, including the empty sum `0`. -/
def birkhoffSumMax (T : Ω → Ω) (f : Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n + 1, ω => max (birkhoffSumMax T f n ω) (birkhoffSum T f (n + 1) ω)

section Pointwise

omit [MeasurableSpace Ω]

/-- The maximum through length zero is the empty sum. -/
@[simp] lemma birkhoffSumMax_zero (T : Ω → Ω) (f : Ω → ℝ) :
    birkhoffSumMax T f 0 = 0 := rfl

/-- Each partial maximum extends the previous one by the next Birkhoff sum. -/
lemma birkhoffSumMax_succ (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) :
    birkhoffSumMax T f (n + 1) =
      fun ω => max (birkhoffSumMax T f n ω) (birkhoffSum T f (n + 1) ω) := rfl

/-- Partial maxima are nonnegative. -/
lemma birkhoffSumMax_nonneg (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ birkhoffSumMax T f n ω := by
  induction n with
  | zero => simp [birkhoffSumMax]
  | succ n ih =>
    rw [birkhoffSumMax]
    exact le_trans ih (le_max_left _ _)

/-- Birkhoff sums up to the current length lie under the partial maximum. -/
lemma birkhoffSum_le_birkhoffSumMax (T : Ω → Ω) (f : Ω → ℝ) (k n : ℕ) (hk : k ≤ n)
    (ω : Ω) : birkhoffSum T f k ω ≤ birkhoffSumMax T f n ω := by
  induction n with
  | zero =>
    obtain rfl := Nat.eq_zero_of_le_zero hk
    simp [birkhoffSumMax, birkhoffSum_zero_apply]
  | succ n ih =>
    rw [birkhoffSumMax]
    rcases hk.eq_or_lt with rfl | hklt
    · exact le_max_right _ _
    · exact (ih (Nat.le_of_lt_succ hklt)).trans (le_max_left _ _)

/-- A positive partial maximum is witnessed by a positive Birkhoff sum. -/
lemma exists_birkhoffSum_pos_of_birkhoffSumMax_pos (T : Ω → Ω) (f : Ω → ℝ) (N : ℕ)
    {ω : Ω} (h : 0 < birkhoffSumMax T f N ω) :
    ∃ n, 0 < n ∧ n ≤ N ∧ 0 < birkhoffSum T f n ω := by
  induction N with
  | zero => simp [birkhoffSumMax] at h
  | succ N ih =>
    rw [birkhoffSumMax] at h
    rcases lt_max_iff.mp h with hN | hS
    · obtain ⟨n, hn, hnN, hpos⟩ := ih hN
      exact ⟨n, hn, hnN.trans N.le_succ, hpos⟩
    · exact ⟨N + 1, Nat.succ_pos N, le_rfl, hS⟩

/-- The finite maximal-positive set is the positivity set of the partial maximum. -/
lemma maximalPositiveSet_eq_birkhoffSumMax_pos (T : Ω → Ω) (f : Ω → ℝ) (N : ℕ) :
    {ω | ∃ n, 0 < n ∧ n ≤ N ∧ 0 < birkhoffSum T f n ω} =
      {ω | 0 < birkhoffSumMax T f N ω} := by
  ext ω
  constructor
  · rintro ⟨n, hn, hnN, hpos⟩
    exact lt_of_lt_of_le hpos (birkhoffSum_le_birkhoffSumMax T f n N hnN ω)
  · exact exists_birkhoffSum_pos_of_birkhoffSumMax_pos T f N

/-- The one-step recurrence `Mₙ₊₁(ω) = max(0, f(ω) + Mₙ(Tω))`. -/
lemma birkhoffSumMax_succ_eq_max_add (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    birkhoffSumMax T f (n + 1) ω =
      max 0 (f ω + birkhoffSumMax T f n (T ω)) := by
  induction n generalizing ω with
  | zero => simp [birkhoffSumMax, birkhoffSum_one_apply]
  | succ n ih =>
    have hS : birkhoffSum T f (n + 2) ω =
        f ω + birkhoffSum T f (n + 1) (T ω) :=
      birkhoffSum_succ_apply' T f (n + 1) ω
    have hmax : max (max (0 : ℝ) (f ω + birkhoffSumMax T f n (T ω)))
          (f ω + birkhoffSum T f (n + 1) (T ω)) =
        max 0 (f ω + max (birkhoffSumMax T f n (T ω))
          (birkhoffSum T f (n + 1) (T ω))) := by
      rw [max_assoc, ← add_max]
    calc
      birkhoffSumMax T f (n + 2) ω
          = max (birkhoffSumMax T f (n + 1) ω) (birkhoffSum T f (n + 2) ω) := rfl
      _ = max (max 0 (f ω + birkhoffSumMax T f n (T ω)))
            (f ω + birkhoffSum T f (n + 1) (T ω)) := by rw [ih ω, hS]
      _ = max 0 (f ω + birkhoffSumMax T f (n + 1) (T ω)) := by
        rw [hmax, birkhoffSumMax]

/-- Iterates preserve a strictly invariant set. -/
lemma preimage_iterate_eq_of_invariant {T : Ω → Ω} {E : Set Ω} (hinv : T ⁻¹' E = E)
    (k : ℕ) : (T^[k]) ⁻¹' E = E :=
  IsFixedPt.preimage_iterate hinv k

/-- On a strictly invariant set the Birkhoff sums of an indicator agree with the
indicator of the sums. -/
lemma birkhoffSum_indicator_invariant {T : Ω → Ω} {E : Set Ω} (hinv : T ⁻¹' E = E)
    (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    birkhoffSum T (E.indicator f) n ω = E.indicator (birkhoffSum T f n) ω := by
  by_cases hω : ω ∈ E
  · rw [indicator_of_mem hω]
    unfold birkhoffSum
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : T^[k] ω ∈ E := by
      rw [← Set.mem_preimage, preimage_iterate_eq_of_invariant hinv k]
      exact hω
    simp [indicator_of_mem hk]
  · rw [indicator_of_notMem hω]
    unfold birkhoffSum
    refine Finset.sum_eq_zero fun k _ => ?_
    have hk : T^[k] ω ∉ E := by
      rw [← Set.mem_preimage, preimage_iterate_eq_of_invariant hinv k]
      exact hω
    simp [indicator_of_notMem hk]

/-- Finite maximal-positive sets increase to the set where some positive-length sum is positive. -/
lemma iUnion_maximalPositiveSet (T : Ω → Ω) (f : Ω → ℝ) :
    ⋃ N, {ω | ∃ n, 0 < n ∧ n ≤ N ∧ 0 < birkhoffSum T f n ω} =
      {ω | ∃ n, 0 < n ∧ 0 < birkhoffSum T f n ω} := by
  ext ω
  simp only [mem_iUnion]
  constructor
  · rintro ⟨N, n, hn, _, hpos⟩
    exact ⟨n, hn, hpos⟩
  · rintro ⟨n, hn, hpos⟩
    exact ⟨n, n, hn, le_rfl, hpos⟩

end Pointwise

/-- A measurable self-map preserves measurability of Birkhoff sums. -/
lemma measurable_birkhoffSum {T : Ω → Ω} (hT : Measurable T) {f : Ω → ℝ}
    (hf : Measurable f) : ∀ n, Measurable (birkhoffSum T f n)
  | 0 => by
    change Measurable fun _ : Ω => (0 : ℝ)
    exact measurable_const
  | n + 1 => by
    rw [birkhoffSum_succ']
    exact hf.add ((measurable_birkhoffSum hT hf n).comp hT)

/-- Partial maxima of a measurable observable are measurable. -/
lemma measurable_birkhoffSumMax {T : Ω → Ω} (hT : Measurable T) {f : Ω → ℝ}
    (hf : Measurable f) : ∀ n, Measurable (birkhoffSumMax T f n)
  | 0 => by
    simp [birkhoffSumMax]
  | n + 1 =>
    (measurable_birkhoffSumMax hT hf n).max (measurable_birkhoffSum hT hf (n + 1))

/-- Birkhoff sums of an integrable observable along a measure-preserving map are integrable. -/
lemma integrable_birkhoffSum {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Integrable f μ) (n : ℕ) : Integrable (birkhoffSum T f n) μ := by
  induction n with
  | zero => simp [birkhoffSum_zero]
  | succ n ih =>
    rw [birkhoffSum_succ']
    exact hf.add (hT.integrable_comp_of_integrable ih)

/-- Partial maxima of an integrable observable are integrable. -/
lemma integrable_birkhoffSumMax {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Integrable f μ) (n : ℕ) : Integrable (birkhoffSumMax T f n) μ := by
  induction n with
  | zero => simp [birkhoffSumMax]
  | succ n ih =>
    rw [birkhoffSumMax_succ]
    exact ih.sup (integrable_birkhoffSum hT hf (n + 1))

/-- A measure-preserving self-map preserves integrals of integrable observables. -/
lemma integral_comp_measurePreserving {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {g : Ω → ℝ} (hg : Integrable g μ) : ∫ ω, g (T ω) ∂μ = ∫ ω, g ω ∂μ := by
  have hsm : AEStronglyMeasurable g (μ.map T) := by
    rw [hT.map_eq]
    exact hg.aestronglyMeasurable
  have hmap := integral_map (μ := μ) (φ := T) hT.measurable.aemeasurable hsm
  simpa [hT.map_eq] using hmap.symm

/-- Positivity set of a measurable partial maximum. -/
lemma measurableSet_birkhoffSumMax_pos {T : Ω → Ω} (hT : Measurable T) {f : Ω → ℝ}
    (hf : Measurable f) (n : ℕ) : MeasurableSet {ω | 0 < birkhoffSumMax T f n ω} :=
  measurableSet_lt (measurable_const : Measurable fun (_ : Ω) => (0 : ℝ))
    (measurable_birkhoffSumMax hT hf n)

/-- On a probability space the finite maximal integral is nonnegative for a measurable
integrable observable. The argument is Garsia's comparison of consecutive partial maxima. -/
lemma integral_nonneg_maximal_of_measurable {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Integrable f μ) (hf_meas : Measurable f) (N : ℕ) :
    0 ≤ ∫ ω in {ω | ∃ n, 0 < n ∧ n ≤ N ∧ 0 < birkhoffSum T f n ω}, f ω ∂μ := by
  rw [maximalPositiveSet_eq_birkhoffSumMax_pos]
  cases N with
  | zero => simp [birkhoffSumMax]
  | succ N =>
    let M : ℕ → Ω → ℝ := birkhoffSumMax T f
    let A : Set Ω := {ω | 0 < M (N + 1) ω}
    have hA : MeasurableSet A :=
      measurableSet_birkhoffSumMax_pos hT.measurable hf_meas (N + 1)
    have hM_int : Integrable (M (N + 1)) μ := integrable_birkhoffSumMax hT hf (N + 1)
    have hPrev_int : Integrable (M N) μ := integrable_birkhoffSumMax hT hf N
    have hComp_int : Integrable (fun ω => M N (T ω)) μ :=
      hT.integrable_comp_of_integrable hPrev_int
    have h_on : ∀ ω ∈ A, M (N + 1) ω = f ω + M N (T ω) := by
      intro ω hω
      have hmem : 0 < birkhoffSumMax T f (N + 1) ω := by
        simpa [M, A] using hω
      rw [birkhoffSumMax_succ_eq_max_add] at hmem
      have hpos : 0 < f ω + M N (T ω) :=
        (lt_max_iff.mp hmem).resolve_left (lt_irrefl 0)
      rw [show M (N + 1) ω = birkhoffSumMax T f (N + 1) ω from rfl,
        birkhoffSumMax_succ_eq_max_add]
      exact max_eq_right hpos.le
    have h_eq_ind : (fun ω => M (N + 1) ω) =
        A.indicator (fun ω => f ω + M N (T ω)) := by
      ext ω
      by_cases hω : ω ∈ A
      · simp [indicator_of_mem hω, h_on ω hω]
      · have hle : M (N + 1) ω ≤ 0 := not_lt.mp hω
        have hz : M (N + 1) ω = 0 :=
          le_antisymm hle (birkhoffSumMax_nonneg T f (N + 1) ω)
        simp [indicator_of_notMem hω, hz]
    have h_split : A.indicator (fun ω => f ω + M N (T ω)) =
        A.indicator f + A.indicator (fun ω => M N (T ω)) := by
      ext ω
      by_cases hω : ω ∈ A
      · simp [indicator_of_mem hω]
      · simp [indicator_of_notMem hω]
    have hfA : Integrable (A.indicator f) μ := hf.indicator hA
    have hMA : Integrable (A.indicator (fun ω => M N (T ω))) μ :=
      hComp_int.indicator hA
    have h_int_sum : ∫ ω, M (N + 1) ω ∂μ =
        ∫ ω, A.indicator f ω ∂μ + ∫ ω, A.indicator (fun ω => M N (T ω)) ω ∂μ := by
      rw [h_eq_ind, h_split]
      exact integral_add hfA hMA
    have h_ind_le : ∫ ω, A.indicator (fun ω => M N (T ω)) ω ∂μ ≤
        ∫ ω, M N (T ω) ∂μ := by
      refine integral_mono_ae hMA hComp_int ?_
      refine Eventually.of_forall fun ω => ?_
      by_cases hω : ω ∈ A
      · simp [indicator_of_mem hω]
      · simpa [indicator_of_notMem hω] using birkhoffSumMax_nonneg T f N (T ω)
    have h_comp : ∫ ω, M N (T ω) ∂μ = ∫ ω, M N ω ∂μ :=
      integral_comp_measurePreserving hT hPrev_int
    have h_mono : ∫ ω, M N ω ∂μ ≤ ∫ ω, M (N + 1) ω ∂μ := by
      refine integral_mono hPrev_int hM_int fun ω => ?_
      rw [show M (N + 1) ω = max (M N ω) (birkhoffSum T f (N + 1) ω) from rfl]
      exact le_max_left _ _
    have h_set : ∫ ω in A, f ω ∂μ = ∫ ω, A.indicator f ω ∂μ :=
      (integral_indicator hA).symm
    have h_ind_le' : ∫ ω, A.indicator (fun ω => M N (T ω)) ω ∂μ ≤
        ∫ ω, M N ω ∂μ := by
      simpa [h_comp] using h_ind_le
    have h_f : ∫ ω in A, f ω ∂μ =
        ∫ ω, M (N + 1) ω ∂μ -
          ∫ ω, A.indicator (fun ω => M N (T ω)) ω ∂μ := by
      rw [h_set, eq_sub_iff_add_eq, h_int_sum.symm]
    have h_nonneg_diff : 0 ≤ ∫ ω, M (N + 1) ω ∂μ - ∫ ω, M N ω ∂μ :=
      sub_nonneg.mpr h_mono
    have h_ge : ∫ ω, M (N + 1) ω ∂μ - ∫ ω, M N ω ∂μ ≤
        ∫ ω, M (N + 1) ω ∂μ -
          ∫ ω, A.indicator (fun ω => M N (T ω)) ω ∂μ :=
      sub_le_sub_left h_ind_le' _
    linarith

/-- The finite maximal integral is nonnegative for a general integrable observable.
The sums of an almost-everywhere equal measurable representative agree almost everywhere,
so the restricted integrals agree. -/
lemma integral_nonneg_maximalErgodicSet {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Integrable f μ) (N : ℕ) :
    0 ≤ ∫ ω in {ω | ∃ n : ℕ, 0 < n ∧ n ≤ N ∧ 0 < birkhoffSum T f n ω}, f ω ∂μ := by
  set g : Ω → ℝ := hf.aestronglyMeasurable.mk f with hg_def
  have hfg : f =ᵐ[μ] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg_meas : Measurable g := hf.aestronglyMeasurable.measurable_mk
  have hg_int : Integrable g μ := (integrable_congr hfg).1 hf
  set Af := {ω | ∃ n : ℕ, 0 < n ∧ n ≤ N ∧ 0 < birkhoffSum T f n ω}
  set Ag := {ω | ∃ n : ℕ, 0 < n ∧ n ≤ N ∧ 0 < birkhoffSum T g n ω}
  have hsums : ∀ᵐ ω ∂μ, ∀ n, birkhoffSum T f n ω = birkhoffSum T g n ω :=
    (ae_all_iff).2 fun n =>
      hT.quasiMeasurePreserving.birkhoffSum_ae_eq_of_ae_eq hfg n
  have hsets : Af =ᵐ[μ] Ag := by
    filter_upwards [hsums] with ω hω
    refine propext ?_
    constructor
    · rintro ⟨n, hn, hnN, hpos⟩
      exact ⟨n, hn, hnN, by rwa [← hω n]⟩
    · rintro ⟨n, hn, hnN, hpos⟩
      exact ⟨n, hn, hnN, by rwa [hω n]⟩
  have hrest : μ.restrict Af = μ.restrict Ag := Measure.restrict_congr_set hsets
  have hint : ∫ ω in Af, f ω ∂μ = ∫ ω in Ag, g ω ∂μ := by
    rw [hrest]
    exact integral_congr_ae (ae_restrict_of_ae hfg)
  rw [hint]
  exact integral_nonneg_maximal_of_measurable hT hg_int hg_meas N

/-- Integral over the strict supremum set of a measurable integrable observable. -/
lemma integral_nonneg_strictPositive_of_measurable {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Integrable f μ)
    (hf_meas : Measurable f) :
    0 ≤ ∫ ω in {ω | ∃ n, 0 < n ∧ 0 < birkhoffSum T f n ω}, f ω ∂μ := by
  let A : ℕ → Set Ω := fun N =>
    {ω | ∃ n, 0 < n ∧ n ≤ N ∧ 0 < birkhoffSum T f n ω}
  have hmono : Monotone A := by
    intro m n hmn ω
    rintro ⟨k, hk, hkN, hpos⟩
    exact ⟨k, hk, hkN.trans hmn, hpos⟩
  have hmeas : ∀ N, MeasurableSet (A N) := by
    intro N
    dsimp [A]
    rw [maximalPositiveSet_eq_birkhoffSumMax_pos]
    exact measurableSet_birkhoffSumMax_pos hT.measurable hf_meas N
  have hfi : IntegrableOn f (⋃ N, A N) μ := hf.integrableOn
  have htend :=
    tendsto_setIntegral_of_monotone (s := A) (f := f) (μ := μ) hmeas hmono hfi
  have hge : ∀ N, 0 ≤ ∫ ω in A N, f ω ∂μ :=
    fun N => integral_nonneg_maximal_of_measurable hT hf hf_meas N
  have hlim : 0 ≤ ∫ ω in ⋃ N, A N, f ω ∂μ :=
    ge_of_tendsto htend (Eventually.of_forall hge)
  simpa [iUnion_maximalPositiveSet, A] using hlim

/-- If a measurable strictly invariant set sits inside the strict supremum set, its integral
is nonnegative. -/
lemma setIntegral_nonneg_of_invariant_subset_positive {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Integrable f μ)
    (hf_meas : Measurable f) {E : Set Ω} (hE : MeasurableSet E) (hinv : T ⁻¹' E = E)
    (hsub : E ⊆ {ω | ∃ n, 0 < n ∧ 0 < birkhoffSum T f n ω}) :
    0 ≤ ∫ ω in E, f ω ∂μ := by
  set g : Ω → ℝ := E.indicator f with hg
  have hg_meas : Measurable g := hf_meas.indicator hE
  have hg_int : Integrable g μ := hf.indicator hE
  have hpos : {ω | ∃ n, 0 < n ∧ 0 < birkhoffSum T g n ω} = E := by
    ext ω
    constructor
    · rintro ⟨n, hn, hnpos⟩
      by_contra hnot
      have hz : birkhoffSum T g n ω = 0 := by
        rw [birkhoffSum_indicator_invariant hinv f n ω, indicator_of_notMem hnot]
      exact lt_irrefl (0 : ℝ) (hz ▸ hnpos)
    · intro hω
      obtain ⟨n, hn, hnpos⟩ := hsub hω
      refine ⟨n, hn, ?_⟩
      have heq : birkhoffSum T g n ω = birkhoffSum T f n ω := by
        rw [birkhoffSum_indicator_invariant hinv f n ω, indicator_of_mem hω]
      rwa [heq]
  have hnonneg := integral_nonneg_strictPositive_of_measurable hT hg_int hg_meas
  rw [hpos] at hnonneg
  have heq : ∫ ω in E, g ω ∂μ = ∫ ω in E, f ω ∂μ := by
    refine setIntegral_congr_ae hE (ae_of_all μ fun ω hω => ?_)
    simp [g, indicator_of_mem hω]
  rwa [heq] at hnonneg

/-- Shift of a constant does not change the shape of the maximal inequality on an invariant set. -/
lemma setIntegral_ge_const_of_invariant_subset_positive [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Integrable f μ)
    (hf_meas : Measurable f) {E : Set Ω} (hE : MeasurableSet E) (hinv : T ⁻¹' E = E)
    {α : ℝ}
    (hsub : E ⊆ {ω | ∃ n, 0 < n ∧ 0 < birkhoffSum T (fun ω => f ω - α) n ω}) :
    α * μ.real E ≤ ∫ ω in E, f ω ∂μ := by
  have hconst : Integrable (fun _ : Ω => α) μ := integrable_const α
  have hsubf : Integrable (fun ω => f ω - α) μ := hf.sub hconst
  have hmeas : Measurable (fun ω => f ω - α) := hf_meas.sub measurable_const
  have hnonneg := setIntegral_nonneg_of_invariant_subset_positive hT hsubf hmeas hE hinv hsub
  have hsplit : ∫ ω in E, (f ω - α) ∂μ =
      ∫ ω in E, f ω ∂μ - ∫ ω in E, (α : ℝ) ∂μ :=
    integral_sub hf.integrableOn hconst.integrableOn
  have hα : ∫ ω in E, (α : ℝ) ∂μ = α * μ.real E := by
    rw [setIntegral_const]
    simp [smul_eq_mul, mul_comm]
  have hle : 0 ≤ ∫ ω in E, f ω ∂μ - α * μ.real E := by
    rw [hsplit, hα] at hnonneg
    exact hnonneg
  linarith

end CKMA
