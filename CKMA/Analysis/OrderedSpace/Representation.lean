/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.OrderedSpace.Bands
public import CKMA.Analysis.OrderedSpace.Representation.AL.Gluing.Sum
public import CKMA.Analysis.OrderedSpace.Representation.AM
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Category.CompHaus.Basic
public import Mathlib.Topology.ContinuousMap.Ordered
public import Mathlib.MeasureTheory.Function.LpOrder

/-!
# AM and AL Banach lattices and their representations

AM spaces have the maximum norm identity on the positive cone; an AM unit identifies the norm
unit ball with its order interval. AL spaces have additive norm on the positive cone, and the
KB property concerns convergence of increasing norm-bounded positive sequences.

Kakutani representation identifies AM spaces with continuous real functions on a compact
Hausdorff carrier and AL spaces with real L1 spaces. Empty compact carriers represent the zero
space; no sigma-finiteness restriction is imposed on the general AL representation. The AL-to-KB
implication uses Mathlib's bounded monotone convergence of real sequences and its metric
Cauchy criterion, with the AL identity converting norm differences into distances.
Sources: GAPS 19.27 and 19.29.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology MeasureTheory

universe u

/-- Mathlib's compact Hausdorff carrier, including the empty space for the zero AM space. -/
abbrev CompactHausdorffModel := CompHaus.{u}

/-- The underlying carrier of a compact Hausdorff representation space. -/
abbrev CompactHausdorffModel.Carrier (K : CompactHausdorffModel.{u}) : Type u := K

/-- A measure-space carrier for an AL representation, without an unnecessary sigma-finiteness
restriction on a general AL space. -/
structure MeasureSpaceModel where
  /-- Underlying type. -/
  Carrier : Type u
  /-- Sigma algebra. -/
  [measurableSpace : MeasurableSpace Carrier]
  /-- Representing measure. -/
  measure : Measure Carrier

attribute [instance] MeasureSpaceModel.measurableSpace

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]

/-- The maximum norm identity on the positive cone defining an AM space. -/
def IsAMSpace (E : Type*) [NormedAddCommGroup E] [Lattice E] : Prop :=
  ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x ⊔ y‖ = max ‖x‖ ‖y‖

/-- An AM unit identifies its order interval with the closed norm unit ball. -/
def IsAMSpaceUnit (e : E) : Prop :=
  IsAMSpace E ∧ 0 ≤ e ∧ Metric.closedBall (0 : E) 1 = Set.Icc (-e) e

/-- Norm additivity on the positive cone defining an AL space. -/
def IsALSpace (E : Type*) [NormedAddCommGroup E] [Lattice E] : Prop :=
  ∀ x y : E, 0 ≤ x → 0 ≤ y → ‖x + y‖ = ‖x‖ + ‖y‖

/-- The KB property, formulated with norm convergence of increasing bounded positive sequences. -/
def IsKBSpace (E : Type*) [NormedAddCommGroup E] [Lattice E] : Prop :=
  ∀ x : ℕ → E, Monotone x → (∀ n, 0 ≤ x n) →
    (∃ M : ℝ, ∀ n, ‖x n‖ ≤ M) → ∃ y : E, Tendsto x atTop (𝓝 y)

/-- **19.27**, Kakutani: an AM Banach lattice with unit is lattice isometric to a compact
Hausdorff continuous-function space, with that unit represented by the constant one. -/
theorem exists_amSpace_representation [CompleteSpace E] {e : E} (he : IsAMSpaceUnit e) :
    ∃ K : CompactHausdorffModel.{u}, ∃ U : E ≃ₗᵢ[ℝ] C(K.Carrier, ℝ),
      U e = 1 ∧ ∀ x y, U (x ⊔ y) = U x ⊔ U y := by
  rcases he with ⟨-, he0, hball⟩
  obtain ⟨K, U, hU, hsup⟩ := exists_am_representation (E := E) he0 hball
  exact ⟨K, U, hU, hsup⟩

/-- **19.29**, Kakutani: an AL Banach lattice is lattice isometric to some real L1 space. -/
theorem exists_alSpace_representation [CompleteSpace E] (hE : IsALSpace E) :
    ∃ M : MeasureSpaceModel.{u}, ∃ U : E ≃ₗᵢ[ℝ] Lp ℝ 1 M.measure,
      ∀ x y, U (x ⊔ y) = U x ⊔ U y := by
  obtain ⟨X, mX, μ, U, hsup⟩ := exists_al_representation (E := E) hE
  exact ⟨{ Carrier := X, measurableSpace := mX, measure := μ }, U, hsup⟩

omit [NormedSpace ℝ E] [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- The monotone-completeness consequence of the AL identity.
The full net-based order-continuity statement is not part of this interface yet. -/
theorem IsALSpace.isKBSpace [CompleteSpace E] (hE : IsALSpace E) : IsKBSpace E := by
  intro x hx hpos hbound
  have hsub : ∀ n m, n ≤ m → ‖x m - x n‖ = ‖x m‖ - ‖x n‖ := by
    intro n m hnm
    have h := hE (x n) (x m - x n) (hpos n) (sub_nonneg.mpr (hx hnm))
    rw [add_sub_cancel] at h
    linarith
  have hn : Monotone (fun n => ‖x n‖) := by
    intro n m hnm
    have h := hsub n m hnm
    linarith [norm_nonneg (x m - x n)]
  have hb : BddAbove (Set.range fun n => ‖x n‖) := by
    rcases hbound with ⟨M, hM⟩
    exact ⟨M, by rintro _ ⟨n, rfl⟩; exact hM n⟩
  have hcnorm := (tendsto_atTop_ciSup hn hb).cauchySeq
  apply cauchySeq_tendsto_of_complete
  refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
  rcases Metric.cauchySeq_iff'.1 hcnorm ε hε with ⟨N, hN⟩
  refine ⟨N, fun n hNn => ?_⟩
  have heq : dist (x n) (x N) = dist ‖x n‖ ‖x N‖ := by
    rw [dist_eq_norm, hsub N n hNn, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr (hn hNn))]
  rw [heq]
  exact hN n hNn

end CKMA
