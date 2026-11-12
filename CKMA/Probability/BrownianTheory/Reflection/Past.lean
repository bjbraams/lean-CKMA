/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.BrownianTheory.Reflection.Grid
public import Mathlib.Probability.Independence.Basic

/-!
# Reflection of one Brownian increment

The increment after a fixed time is independent of the stopped path and is a symmetric Gaussian.
A measurable condition on that path is therefore equally likely to be followed by an up-crossing
of a level or by its reflected down-crossing.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The path stopped at time `s`. -/
def past (C : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : Iic s → ℝ :=
  fun u => C u ω

/-- The stopped path is measurable when every marginal is measurable. -/
lemma measurable_past {C : ℝ≥0 → Ω → ℝ} (hm : ∀ u, Measurable (C u)) (s : ℝ≥0) :
    Measurable (past C s) :=
  Measurable.of_eval fun u => hm u

/-- Grid time `j` viewed as a time at most grid time `k`. -/
def gridCast {t : ℝ≥0} {n : ℕ} {j k : ℕ} (hjk : j ≤ k) : Iic (grid t n k) :=
  ⟨grid t n j, grid_mono hjk⟩

/-- Casting a grid time does not change its value. -/
lemma coe_gridCast {t : ℝ≥0} {n j k : ℕ} (hjk : j ≤ k) :
    (gridCast (t := t) (n := n) hjk : ℝ≥0) = grid t n j := rfl

/-- Paths whose first grid visit to level `b` is at index `k`. -/
def firstPassage (t : ℝ≥0) (b : ℝ) (n k : ℕ) : Set (Iic (grid t n k) → ℝ) :=
  {y | b ≤ y ⟨grid t n k, le_rfl⟩ ∧ ∀ j (hj : j < k), y (gridCast (le_of_lt hj)) < b}

/-- The first grid visit is a measurable condition on the stopped path. -/
lemma measurableSet_firstPassage (t : ℝ≥0) (b : ℝ) (n k : ℕ) :
    MeasurableSet (firstPassage t b n k) := by
  let hit : Set (Iic (grid t n k) → ℝ) := {y | b ≤ y ⟨grid t n k, le_rfl⟩}
  have hhit : MeasurableSet hit := measurableSet_Ici.preimage (measurable_pi_apply _)
  let prev : Set (Iic (grid t n k) → ℝ) :=
    {y | ∀ j (hj : j < k), y (gridCast (le_of_lt hj)) < b}
  have hprev : MeasurableSet prev := by
    let S (j : ℕ) : Set (Iic (grid t n k) → ℝ) :=
      if hj : j < k then {y | y (gridCast (le_of_lt hj)) < b} else univ
    have hS : ∀ j, MeasurableSet (S j) := by
      intro j
      by_cases hj : j < k
      · have hS' : S j = {y | y (gridCast (le_of_lt hj)) < b} := by simp [S, hj]
        rw [hS']
        exact measurableSet_Iio.preimage (measurable_pi_apply _)
      · have hS' : S j = univ := by simp [S, hj]
        rw [hS']
        exact MeasurableSet.univ
    have hSeq : prev = ⋂ j, S j := by
      ext y
      simp only [prev, S, mem_ofPred_eq, mem_iInter]
      constructor
      · intro h j
        by_cases hj : j < k
        · simpa [hj] using h j hj
        · simp [hj]
      · intro h j hj
        simpa [hj] using h j
    rw [hSeq]
    exact MeasurableSet.iInter hS
  have heq : firstPassage t b n k = hit ∩ prev := by
    ext y
    simp [firstPassage, hit, prev]
  rw [heq]
  exact hhit.inter hprev

/-- On indices inside the grid, the first-visit event is the stopped-path condition. -/
lemma isTauSet_eq_preimage (C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (b : ℝ) {n k : ℕ} (hk : k ≤ 2 ^ n) :
    isTauSet C t b n k = past C (grid t n k) ⁻¹' firstPassage t b n k := by
  ext ω
  constructor
  · intro h
    refine ⟨?_, fun j hj => ?_⟩
    · simpa [past] using h.2.1
    · simpa [past, coe_gridCast] using h.2.2 j hj
  · intro h
    refine ⟨hk, ?_, fun j hj => ?_⟩
    · simpa [past] using h.1
    · simpa [past, coe_gridCast] using h.2 j hj

/-- Pairs that meet `A` and whose sum reaches level `b`. -/
def reflectSet (s : ℝ≥0) (b : ℝ) (A : Set (Iic s → ℝ)) : Set (ℝ × (Iic s → ℝ)) :=
  {p | p.2 ∈ A ∧ b ≤ p.2 ⟨s, le_rfl⟩ + p.1}

/-- The reflected crossing set is measurable. -/
lemma measurableSet_reflectSet {s : ℝ≥0} {b : ℝ} {A : Set (Iic s → ℝ)} (hA : MeasurableSet A) :
    MeasurableSet (reflectSet s b A) := by
  have hsnd : MeasurableSet {p : ℝ × (Iic s → ℝ) | p.2 ∈ A} := hA.preimage measurable_snd
  have hsum : Measurable (fun p : ℝ × (Iic s → ℝ) => p.2 ⟨s, le_rfl⟩ + p.1) :=
    ((measurable_pi_apply (⟨s, le_rfl⟩ : Iic s)).comp measurable_snd).add measurable_fst
  have hcross : MeasurableSet {p : ℝ × (Iic s → ℝ) | b ≤ p.2 ⟨s, le_rfl⟩ + p.1} :=
    measurableSet_Ici.preimage hsum
  have heq : reflectSet s b A =
      {p | p.2 ∈ A} ∩ {p | b ≤ p.2 ⟨s, le_rfl⟩ + p.1} := by
    ext p
    simp [reflectSet]
  rw [heq]
  exact hsnd.inter hcross

/-- A measurable past event is equally likely before an up-crossing and its reflection. -/
lemma measure_reflect_past {C : ℝ≥0 → Ω → ℝ} (hC : IsBrownianReal C μ)
    (hm : ∀ u, Measurable (C u)) {s t₀ : ℝ≥0} (hs : s ≤ t₀) {b : ℝ}
    {A : Set (Iic s → ℝ)} (hA : MeasurableSet A) :
    μ {ω | past C s ω ∈ A ∧ b ≤ C t₀ ω} =
      μ {ω | past C s ω ∈ A ∧ C t₀ ω ≤ 2 * C s ω - b} := by
  let Y : Ω → Iic s → ℝ := past C s
  let incr : Ω → ℝ≥0 → ℝ := fun ω u => C (s + u) ω - C s ω
  let F : Ω → ℝ := fun ω => C t₀ ω - C s ω
  let G : Ω → ℝ := fun ω => C s ω - C t₀ ω
  have hY : Measurable Y := measurable_past hm s
  have hincr : IndepFun incr Y μ := hC.toIsPreBrownianReal.indepFun_shift s
  have hFeval : (fun ω => incr ω (t₀ - s)) =ᵐ[μ] F :=
    Eventually.of_forall fun ω => by
      show C (s + (t₀ - s)) ω - C s ω = C t₀ ω - C s ω
      rw [add_tsub_cancel_of_le hs]
  have hGeval : (fun ω => -incr ω (t₀ - s)) =ᵐ[μ] G :=
    Eventually.of_forall fun ω => by
      show -(C (s + (t₀ - s)) ω - C s ω) = C s ω - C t₀ ω
      rw [add_tsub_cancel_of_le hs]
      ring
  have hFindep : IndepFun F Y μ := by
    have hcomp := hincr.comp (measurable_pi_apply (t₀ - s)) measurable_id
    exact hcomp.congr hFeval (Eventually.of_forall fun ω => rfl)
  have hGindep : IndepFun G Y μ := by
    have hφ : Measurable (fun f : ℝ≥0 → ℝ => -f (t₀ - s)) :=
      measurable_neg.comp (measurable_pi_apply (t₀ - s))
    exact (hincr.comp hφ measurable_id).congr hGeval (Eventually.of_forall fun ω => rfl)
  have hGlaw : HasLaw G (gaussianReal 0 (nndist s.1 t₀.1)) μ :=
    hC.toIsPreBrownianReal.hasLaw_sub s t₀
  have hnegG : (fun ω => -G ω) = F := by
    funext ω
    simp only [G, F]
    ring
  have hFlaw : HasLaw F (gaussianReal 0 (nndist s.1 t₀.1)) μ := by
    have hneg := gaussianReal_neg hGlaw
    simp only [Pi.neg_def, neg_zero, hnegG] at hneg
    exact hneg
  have hpairF := hFindep.map_prod_eq_prod_map_map hFlaw.aemeasurable hY.aemeasurable
  have hpairG := hGindep.map_prod_eq_prod_map_map hGlaw.aemeasurable hY.aemeasurable
  have hmap : μ.map (fun ω => (F ω, Y ω)) = μ.map (fun ω => (G ω, Y ω)) := by
    rw [hpairF, hpairG, hFlaw.map_eq, hGlaw.map_eq]
  let E := reflectSet s b A
  have hE : MeasurableSet E := measurableSet_reflectSet hA
  have hpre : μ ((fun ω => (F ω, Y ω)) ⁻¹' E) = μ ((fun ω => (G ω, Y ω)) ⁻¹' E) := by
    rw [← Measure.map_apply_of_aemeasurable (hFlaw.aemeasurable.prodMk hY.aemeasurable) hE,
      ← Measure.map_apply_of_aemeasurable (hGlaw.aemeasurable.prodMk hY.aemeasurable) hE, hmap]
  have hEF : (fun ω => (F ω, Y ω)) ⁻¹' E = {ω | Y ω ∈ A ∧ b ≤ C t₀ ω} := by
    ext ω
    simp only [E, reflectSet, mem_preimage, mem_ofPred_eq, F]
    constructor
    · rintro ⟨hAω, hle⟩
      have hval : Y ω ⟨s, le_rfl⟩ = C s ω := rfl
      rw [hval, add_sub_cancel] at hle
      exact ⟨hAω, hle⟩
    · rintro ⟨hAω, hle⟩
      have hval : Y ω ⟨s, le_rfl⟩ = C s ω := rfl
      exact ⟨hAω, by rw [hval, add_sub_cancel]; exact hle⟩
  have hEG : (fun ω => (G ω, Y ω)) ⁻¹' E =
      {ω | Y ω ∈ A ∧ C t₀ ω ≤ 2 * C s ω - b} := by
    ext ω
    simp only [E, reflectSet, mem_preimage, mem_ofPred_eq, G]
    constructor
    · rintro ⟨hAω, hle⟩
      have hval : Y ω ⟨s, le_rfl⟩ = C s ω := rfl
      rw [hval] at hle
      exact ⟨hAω, by linarith⟩
    · rintro ⟨hAω, hle⟩
      have hval : Y ω ⟨s, le_rfl⟩ = C s ω := rfl
      exact ⟨hAω, by rw [hval]; linarith⟩
  simpa [Y, hEF, hEG] using hpre

/-- First grid passage reflects across the level. -/
lemma measure_isTau_reflect {C : ℝ≥0 → Ω → ℝ} (hC : IsBrownianReal C μ)
    (hm : ∀ u, Measurable (C u)) (t : ℝ≥0) (b : ℝ) {n k : ℕ} (hk : k ≤ 2 ^ n) :
    μ (isTauSet C t b n k ∩ {ω | b ≤ C t ω}) =
      μ (isTauSet C t b n k ∩ {ω | C t ω ≤ 2 * C (grid t n k) ω - b}) := by
  have hs : grid t n k ≤ t := grid_le hk
  have h := measure_reflect_past hC hm hs (b := b) (measurableSet_firstPassage t b n k)
  have hpre := isTauSet_eq_preimage C t b hk
  have hL : isTauSet C t b n k ∩ {ω | b ≤ C t ω} =
      {ω | past C (grid t n k) ω ∈ firstPassage t b n k ∧ b ≤ C t ω} := by
    ext ω
    simp [hpre, mem_inter_iff, mem_preimage, mem_ofPred_eq]
  have hR : isTauSet C t b n k ∩ {ω | C t ω ≤ 2 * C (grid t n k) ω - b} =
      {ω | past C (grid t n k) ω ∈ firstPassage t b n k ∧
        C t ω ≤ 2 * C (grid t n k) ω - b} := by
    ext ω
    simp [hpre, mem_inter_iff, mem_preimage, mem_ofPred_eq]
  rw [hL, hR]
  exact h

end CKMA
