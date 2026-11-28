/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.BrownianQuadraticVariation.TimePartition
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Quadratic covariation along deterministic partitions

`IsQuadraticCovariation X Y μ A` says that, for every horizon `T` and every sequence of
deterministic partitions of `[0, T]` with mesh tending to zero, the completed-interval covariation
sums of `X` and `Y` converge to `A` in probability, uniformly on `[0, T]`. Such a process is
unique up to modification, and `quadraticCovariation X Y μ` is a chosen one (or `0` when none
exists).

## Main definitions

* `CKMA.IsQuadraticCovariation`: `A` is a quadratic covariation process of `X` and `Y`.
* `CKMA.quadraticCovariation`: the bracket `[X, Y]`.

## Main results

* `CKMA.TimePartition.tendsto_mesh_uniform`: uniform partitions have mesh tending to zero.
* `CKMA.IsQuadraticCovariation.ae_eq`: quadratic covariation processes agree almost surely at
  each time.
* `CKMA.IsQuadraticCovariation.quadraticCovariation_ae_eq`: the bracket agrees almost surely with
  any quadratic covariation process.
-/

public section

noncomputable section

namespace CKMA

open scoped NNReal ENNReal
open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `A` is a quadratic covariation process of `X` and `Y` under `μ`: for every horizon `T` and
every sequence of deterministic partitions of `[0, T]` with mesh tending to zero, the
completed-interval covariation sums converge to `A` in probability, uniformly on `[0, T]`. -/
@[expose]
def IsQuadraticCovariation (X Y : ℝ≥0 → Ω → ℝ) (μ : Measure Ω) (A : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ (T : ℝ≥0) (π : ℕ → TimePartition T), Tendsto (fun n ↦ (π n).mesh) atTop (𝓝 0) →
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ μ {ω | ∃ t ≤ T,
      ε < |(π n).covariation X Y t ω - A t ω|}) atTop (𝓝 0)

/-- Defining property of `IsQuadraticCovariation`. -/
theorem isQuadraticCovariation_iff {X Y : ℝ≥0 → Ω → ℝ} {μ : Measure Ω}
    {A : ℝ≥0 → Ω → ℝ} : IsQuadraticCovariation X Y μ A ↔
      ∀ (T : ℝ≥0) (π : ℕ → TimePartition T), Tendsto (fun n ↦ (π n).mesh) atTop (𝓝 0) →
        ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ μ {ω | ∃ t ≤ T,
          ε < |(π n).covariation X Y t ω - A t ω|}) atTop (𝓝 0) :=
  Iff.rfl

/-- The uniform partitions of `[0, T]` have mesh tending to zero. -/
theorem TimePartition.tendsto_mesh_uniform (T : ℝ≥0) :
    Tendsto (fun n ↦ (TimePartition.uniform T n).mesh) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ ↦ T * (1 / ((n : ℝ≥0) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul T
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ zero_le) fun n ↦ ?_
  rw [mul_one_div]
  exact TimePartition.mesh_uniform_le T n

/-- Quadratic covariation processes are unique up to modification: two of them agree almost
surely at each fixed time. -/
theorem IsQuadraticCovariation.ae_eq {X Y : ℝ≥0 → Ω → ℝ} {μ : Measure Ω}
    {A A' : ℝ≥0 → Ω → ℝ} (hA : IsQuadraticCovariation X Y μ A)
    (hA' : IsQuadraticCovariation X Y μ A') (t : ℝ≥0) : A t =ᵐ[μ] A' t := by
  have hsmall : ∀ ε : ℝ, 0 < ε → μ {ω | ε < |A t ω - A' t ω|} = 0 := by
    intro ε hε
    let π := TimePartition.uniform t
    have h1 := hA t π (TimePartition.tendsto_mesh_uniform t) (ε / 2) (half_pos hε)
    have h2 := hA' t π (TimePartition.tendsto_mesh_uniform t) (ε / 2) (half_pos hε)
    refine le_antisymm (ge_of_tendsto' (by simpa using h1.add h2) fun n ↦ ?_) zero_le
    refine (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
    have hω : ε < |A t ω - A' t ω| := hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and, not_lt] at hnot
    have ha := hnot.1 t le_rfl
    have hb := hnot.2 t le_rfl
    have htri : |A t ω - A' t ω| ≤ |(π n).covariation X Y t ω - A t ω| +
        |(π n).covariation X Y t ω - A' t ω| := by
      calc
        |A t ω - A' t ω| = |((π n).covariation X Y t ω - A' t ω) -
            ((π n).covariation X Y t ω - A t ω)| := by ring_nf
        _ ≤ _ := (abs_sub _ _).trans_eq (add_comm _ _)
    linarith
  have hunion : {ω | A t ω ≠ A' t ω} ⊆ ⋃ m : ℕ, {ω | 1 / ((m : ℝ) + 1) < |A t ω - A' t ω|} := by
    intro ω hω
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (abs_pos.2 (sub_ne_zero.2 hω))
    exact Set.mem_iUnion.2 ⟨m, hm⟩
  exact ae_iff.2 (measure_mono_null hunion
    (measure_iUnion_null fun m ↦ hsmall _ (by positivity)))

open Classical in
/-- The quadratic covariation bracket `[X, Y]`: a chosen quadratic covariation process when one
exists, and `0` otherwise. By `IsQuadraticCovariation.ae_eq` it is determined almost surely at
each time. -/
@[expose]
def quadraticCovariation (X Y : ℝ≥0 → Ω → ℝ) (μ : Measure Ω) : ℝ≥0 → Ω → ℝ :=
  if h : ∃ A, IsQuadraticCovariation X Y μ A then h.choose else 0

open Classical in
/-- Defining equation of `quadraticCovariation`. -/
theorem quadraticCovariation_def (X Y : ℝ≥0 → Ω → ℝ) (μ : Measure Ω) :
    quadraticCovariation X Y μ =
      if h : ∃ A, IsQuadraticCovariation X Y μ A then h.choose else 0 := rfl

/-- If a quadratic covariation process exists, the bracket is one. -/
theorem IsQuadraticCovariation.isQuadraticCovariation_quadraticCovariation
    {X Y : ℝ≥0 → Ω → ℝ} {μ : Measure Ω} {A : ℝ≥0 → Ω → ℝ}
    (hA : IsQuadraticCovariation X Y μ A) :
    IsQuadraticCovariation X Y μ (quadraticCovariation X Y μ) := by
  have h : ∃ A, IsQuadraticCovariation X Y μ A := ⟨A, hA⟩
  rw [quadraticCovariation, dite_eq_left h]
  exact h.choose_spec

/-- The bracket agrees almost surely, at each time, with any quadratic covariation process. -/
theorem IsQuadraticCovariation.quadraticCovariation_ae_eq
    {X Y : ℝ≥0 → Ω → ℝ} {μ : Measure Ω} {A : ℝ≥0 → Ω → ℝ}
    (hA : IsQuadraticCovariation X Y μ A) (t : ℝ≥0) :
    quadraticCovariation X Y μ t =ᵐ[μ] A t :=
  hA.isQuadraticCovariation_quadraticCovariation.ae_eq hA t

end CKMA
