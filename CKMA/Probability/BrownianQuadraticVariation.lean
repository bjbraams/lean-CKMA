/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Brownian quadratic variation and covariation (08.7)

`TimePartition` records ordered deterministic nodes, allowing repeated nodes and the
zero time interval. Its mesh controls quadratic and bilinear covariation sums formed
from completed partition intervals. The main statements give uniform convergence in
probability, almost-sure convergence under a summable mesh condition, and cross-coordinate
covariation for independent Brownian coordinates.

The process interface is pre-Brownian: for a sequence of deterministic partitions only
countably many evaluation times are involved. Time and partition nodes are nonnegative
reals; covariance normalization is the standard Brownian one.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped NNReal ENNReal


open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

/-- A finite deterministic partition of `[0,T]`. Repeated nodes are allowed. -/
structure TimePartition (T : ℝ≥0) where
  /-- Number of increments. -/
  size : ℕ
  /-- Partition nodes, including both endpoints. -/
  node : Fin (size + 1) → ℝ≥0
  /-- Time ordering. -/
  monotone_node : Monotone node
  /-- Initial endpoint. -/
  node_zero : node 0 = 0
  /-- Terminal endpoint. -/
  node_last : node (Fin.last size) = T

/-- Largest time increment of a finite partition. -/
def TimePartition.mesh {T : ℝ≥0} (π : TimePartition T) : ℝ≥0 :=
  Finset.univ.sup fun i : Fin π.size ↦ π.node i.succ - π.node i.castSucc

/-- Quadratic covariation using completed partition intervals up to time `t`.
It is constant between adjacent nodes, as in the argument of `GAPS_EASY.md`. -/
def TimePartition.covariation {Ω : Type*} {T : ℝ≥0} (π : TimePartition T)
    (B C : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i : Fin π.size, if π.node i.succ ≤ t then
    (B (π.node i.succ) ω - B (π.node i.castSucc) ω) *
    (C (π.node i.succ) ω - C (π.node i.castSucc) ω) else 0

/-- **08.7**: uniform-on-compact convergence in probability along deterministic vanishing mesh.
No path continuity assumption is needed for completed-interval quadratic sums. -/
theorem brownian_quadraticVariation_ucp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B μ) {T : ℝ≥0} (π : ℕ → TimePartition T)
    (hmesh : Tendsto (fun n ↦ (π n).mesh) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ μ {ω | ∃ t ≤ T,
      ε < |(π n).covariation B B t ω - (t : ℝ)|}) atTop (𝓝 0) := by
  sorry

/-- Summable meshes give almost sure uniform convergence, hence in particular dyadic convergence. -/
theorem brownian_quadraticVariation_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B μ) {T : ℝ≥0} (π : ℕ → TimePartition T)
    (hmesh : Summable (fun n ↦ ((π n).mesh : ℝ))) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ t ≤ T, |(π n).covariation B B t ω - (t : ℝ)| < ε := by
  sorry


/-- Independent Brownian coordinates have diagonal quadratic covariation.
Independence is imposed on the coordinate processes as random elements, rather than only
on pairs of one-time marginals. -/
theorem brownian_covariation_ucp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (B : Fin d → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) μ)
    (hind : iIndepFun (fun i ω ↦ fun t ↦ B i t ω) μ)
    {T : ℝ≥0} (π : ℕ → TimePartition T)
    (hmesh : Tendsto (fun n ↦ (π n).mesh) atTop (𝓝 0)) (i j : Fin d) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ μ {ω | ∃ t ≤ T,
      ε < |(π n).covariation (B i) (B j) t ω - if i = j then (t : ℝ) else 0|})
      atTop (𝓝 0) := by
  sorry

end CKMA
