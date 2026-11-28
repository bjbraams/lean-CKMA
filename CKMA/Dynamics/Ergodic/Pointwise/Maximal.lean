/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Maximal
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The maximal ergodic inequality

The finite-horizon and strict-supremum inequalities are Mathlib's
`setIntegral_support_birkhoffMax_nonneg` and `setIntegral_birkhoffSumSup_nonneg`. The argument
below only passes the supremum inequality to a strictly invariant subset.

## Main results

* `CKMA.birkhoffSum_indicator_invariant`: Birkhoff sums of an indicator of a strictly invariant
  set.
* `CKMA.integral_comp_measurePreserving`: integrals are preserved by measure-preserving maps.
* `CKMA.integral_nonneg_maximalErgodicSet`: the maximal ergodic inequality on finite horizons.
* `CKMA.setIntegral_ge_const_of_invariant_subset_positive`: lower bound for the integral over a
  strictly invariant subset of the positivity set of `f - α`.
-/

public section

noncomputable section

namespace CKMA

open Finset MeasureTheory Filter Set Function
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

section Pointwise

omit [MeasurableSpace Ω]

/-- A positive partial maximum is a positive Birkhoff sum of positive length at most `N`. -/
private lemma pos_birkhoffMax_iff (T : Ω → Ω) (f : Ω → ℝ) (N : ℕ) (ω : Ω) :
    0 < birkhoffMax T f N ω ↔ ∃ n, 0 < n ∧ n ≤ N ∧ 0 < birkhoffSum T f n ω := by
  rw [birkhoffMax, Pi.partialSups_apply, partialSups_apply, lt_sup'_iff]
  constructor
  · rintro ⟨n, hn, hpos⟩
    have hnN : n ≤ N := by simpa [Finset.mem_Iic] using hn
    have hn0 : 0 < n := by
      cases n with
      | zero => simp [birkhoffSum_zero_apply] at hpos
      | succ _ => exact Nat.succ_pos _
    exact ⟨n, hn0, hnN, hpos⟩
  · rintro ⟨n, _, hnN, hpos⟩
    exact ⟨n, by simpa [Finset.mem_Iic] using hnN, hpos⟩

/-- The support of `birkhoffMax` is the finite maximal-positive Birkhoff set. -/
private lemma support_birkhoffMax_eq (T : Ω → Ω) (f : Ω → ℝ) (N : ℕ) :
    (birkhoffMax T f N).support =
      {ω | ∃ n, 0 < n ∧ n ≤ N ∧ 0 < birkhoffSum T f n ω} := by
  ext ω
  simp only [Function.mem_support, mem_ofPred_eq]
  rw [ne_comm, ← (birkhoffMax_nonneg (f := T) (g := f) (n := N) (x := ω)).lt_iff_ne]
  exact pos_birkhoffMax_iff T f N ω

/-- The strict supremum set is the set where some positive-length sum is positive. -/
private lemma setOf_birkhoffSum_pos_eq (T : Ω → Ω) (f : Ω → ℝ) :
    {ω | ∃ n, 0 < n ∧ 0 < birkhoffSum T f n ω} = {ω | 0 < birkhoffSumSup T f ω} := by
  ext ω
  rw [setOf_birkhoffSumSup_pos_eq_iUnion_birkhoffMax_support]
  simp only [mem_ofPred_eq, mem_iUnion, Function.mem_support]
  constructor
  · rintro ⟨n, hn, hpos⟩
    refine ⟨n, ?_⟩
    rw [ne_comm, ← (birkhoffMax_nonneg (f := T) (g := f) (n := n) (x := ω)).lt_iff_ne]
    exact (pos_birkhoffMax_iff T f n ω).2 ⟨n, hn, le_rfl, hpos⟩
  · rintro ⟨N, hN⟩
    have hpos : 0 < birkhoffMax T f N ω := by
      rw [(birkhoffMax_nonneg (f := T) (g := f) (n := N) (x := ω)).lt_iff_ne, ne_comm]
      exact hN
    obtain ⟨n, hn, -, hsum⟩ := (pos_birkhoffMax_iff T f N ω).1 hpos
    exact ⟨n, hn, hsum⟩

/-- Iterates preserve a strictly invariant set. -/
private lemma preimage_iterate_eq_of_invariant {T : Ω → Ω} {E : Set Ω} (hinv : T ⁻¹' E = E)
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

end Pointwise

/-- A measure-preserving map preserves integrals of almost everywhere strongly measurable
observables: `∫ g ∘ T ∂μ = ∫ g ∂ν`. Unlike Mathlib's `MeasurePreserving.integral_comp`, no
measurable embedding is needed, since `g` is a.e. strongly measurable for the image measure. -/
lemma integral_comp_measurePreserving {α β G : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {μ : Measure α} {ν : Measure β} {T : α → β}
    (hT : MeasurePreserving T μ ν) {g : β → G} (hg : AEStronglyMeasurable g ν) :
    ∫ x, g (T x) ∂μ = ∫ y, g y ∂ν := by
  rw [← hT.map_eq] at hg ⊢
  exact (integral_map hT.measurable.aemeasurable hg).symm

/-- The finite maximal integral is nonnegative. This is `setIntegral_support_birkhoffMax_nonneg`
on the finite maximal-positive set. -/
lemma integral_nonneg_maximalErgodicSet {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Integrable f μ) (N : ℕ) :
    0 ≤ ∫ ω in {ω | ∃ n : ℕ, 0 < n ∧ n ≤ N ∧ 0 < birkhoffSum T f n ω}, f ω ∂μ := by
  rw [← support_birkhoffMax_eq T f N]
  exact setIntegral_support_birkhoffMax_nonneg (n := N) μ hT hf

/-- Integral over the set where some positive-length Birkhoff sum is positive. -/
private lemma integral_nonneg_strictPositive {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    0 ≤ ∫ ω in {ω | ∃ n, 0 < n ∧ 0 < birkhoffSum T f n ω}, f ω ∂μ := by
  rw [setOf_birkhoffSum_pos_eq]
  exact setIntegral_birkhoffSumSup_nonneg μ hT hf

/-- If a measurable strictly invariant set sits inside the strict supremum set, its integral
is nonnegative. -/
private lemma setIntegral_nonneg_of_invariant_subset_positive {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Integrable f μ)
    {E : Set Ω} (hE : MeasurableSet E) (hinv : T ⁻¹' E = E)
    (hsub : E ⊆ {ω | ∃ n, 0 < n ∧ 0 < birkhoffSum T f n ω}) :
    0 ≤ ∫ ω in E, f ω ∂μ := by
  set g : Ω → ℝ := E.indicator f
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
  have hnonneg := integral_nonneg_strictPositive hT hg_int
  rw [hpos] at hnonneg
  have heq : ∫ ω in E, g ω ∂μ = ∫ ω in E, f ω ∂μ := by
    refine setIntegral_congr_ae hE (ae_of_all μ fun ω hω => ?_)
    simp [g, indicator_of_mem hω]
  rwa [heq] at hnonneg

/-- If a strictly invariant measurable set `E` lies in the set where some positive-length
Birkhoff sum of `f - α` is positive, then `α * μ(E) ≤ ∫_E f`. -/
lemma setIntegral_ge_const_of_invariant_subset_positive [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Integrable f μ)
    {E : Set Ω} (hE : MeasurableSet E) (hinv : T ⁻¹' E = E) {α : ℝ}
    (hsub : E ⊆ {ω | ∃ n, 0 < n ∧ 0 < birkhoffSum T (fun ω => f ω - α) n ω}) :
    α * μ.real E ≤ ∫ ω in E, f ω ∂μ := by
  have hconst : Integrable (fun _ : Ω => α) μ := integrable_const α
  have hsubf : Integrable (fun ω => f ω - α) μ := hf.sub hconst
  have hnonneg := setIntegral_nonneg_of_invariant_subset_positive hT hsubf hE hinv hsub
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
