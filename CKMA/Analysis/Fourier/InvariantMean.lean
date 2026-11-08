/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Invariant means on Haar L∞ spaces

A positive normalized continuous linear functional is left invariant when translated
representatives agree almost everywhere. Such invariant means exist for compact
groups and locally compact abelian groups; closed subgroups inherit amenability with
their own Haar measure. Translation invariance is stated intrinsically at the level of
L∞ equivalence classes.

Source: GAPS 28.58.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped ENNReal

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]

/-- A positive normalized left-invariant bounded functional on Haar L-infinity.
Translation is specified by a.e. representative equality, so no chosen representative is shifted
as if pointwise equality were intrinsic to the L-infinity class. -/
def IsHaarInvariantMean (μ : Measure G) (m : Lp ℝ ∞ μ →L[ℝ] ℝ) : Prop :=
  (∀ f : Lp ℝ ∞ μ, (∀ᵐ x ∂μ, 0 ≤ f x) → 0 ≤ m f) ∧
    (∀ f : Lp ℝ ∞ μ, (∀ᵐ x ∂μ, f x = 1) → m f = 1) ∧
    ∀ (g : G) (f h : Lp ℝ ∞ μ), (∀ᵐ x ∂μ, h x = f (g⁻¹ * x)) → m h = m f

/-- Amenability in the invariant-mean model on the chosen Haar space. -/
def IsHaarAmenable (μ : Measure G) : Prop := ∃ m, IsHaarInvariantMean μ m

/-- **28.58**, compact groups admit invariant means on their Haar L-infinity spaces. -/
theorem isHaarAmenable_of_compact [CompactSpace G] [T2Space G]
    (μ : Measure G) [Measure.IsHaarMeasure μ] : IsHaarAmenable μ := by
  sorry

/-- Locally compact abelian groups admit invariant means, including noncompact groups. -/
theorem isHaarAmenable_of_commutative [LocallyCompactSpace G] [T2Space G]
    (hcomm : ∀ x y : G, x * y = y * x)
    (μ : Measure G) [Measure.IsHaarMeasure μ] : IsHaarAmenable μ := by
  sorry

/-- Closed subgroups inherit amenability, with their own Haar measure. -/
theorem isHaarAmenable_closed_subgroup [LocallyCompactSpace G] [T2Space G]
    (μ : Measure G) [Measure.IsHaarMeasure μ] (hG : IsHaarAmenable μ)
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (ν : Measure H) [Measure.IsHaarMeasure ν] : IsHaarAmenable ν := by
  sorry

end CKMA
