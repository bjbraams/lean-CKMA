/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.Topology.Instances.ENNReal.Lemmas

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

/-- **10.9**, Rokhlin's tower lemma for a standard Borel probability system with a bimeasurable
invertible transformation. The height is positive; no tower exists at height zero with near-full
  mass. -/
theorem rokhlin_tower [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ) (ha : IsAperiodicModMeasure T μ)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : Set Ω, MeasurableSet B ∧
      (∀ i j : ℕ, i < n → j < n → i ≠ j → Disjoint (towerLevel T B i) (towerLevel T B j)) ∧
      1 - ENNReal.ofReal ε < μ (⋃ i ∈ Finset.range n, towerLevel T B i) := by
  sorry

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
  sorry

end CKMA
