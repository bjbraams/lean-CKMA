/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Convex.Uniform
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Fixed points beyond contraction mappings

Brouwer and Schauder concern continuous maps of nonempty convex sets; Schauder assumes a
closed domain and relatively compact total image rather than boundedness of the domain.
Kakutani–Fan–Glicksberg allows upper hemicontinuous multifunctions with nonempty closed convex
values inside a compact convex set in a locally convex Hausdorff space.

The Browder–Göhde–Kirk statement uses uniform convexity and a nonexpansive map on a closed
bounded convex set; compactness of the map is not required. Sources: GAPS 35.12, 35.13, 35.15, and
  35.21.
-/

@[expose] public section

noncomputable section

namespace CKMA

/-- **35.12**: Brouwer's theorem on a compact convex subset of a finite-dimensional real space. -/
theorem exists_fixedPoint_brouwer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {C : Set E} (hne : C.Nonempty) (hC : IsCompact C)
    (hc : Convex ℝ C) (T : C → C) (hT : Continuous T) : ∃ x : C, T x = x := by
  sorry

/-- **35.13**: Schauder's theorem with relatively compact total image on a closed convex set.
Boundedness of the domain is not required when the total image is relatively compact. -/
theorem exists_fixedPoint_schauder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C)
    (hc : Convex ℝ C) (T : C → C) (hT : Continuous T)
    (himage : IsCompact (closure (Set.range (fun x : C ↦ (T x : E))))) :
    ∃ x : C, T x = x := by
  sorry

/-- **35.15**: Kakutani–Fan–Glicksberg for compact convex subsets of locally convex spaces.
The multifunction is defined on the ambient space but only its restriction to `C` is constrained. -/
theorem exists_fixedPoint_kakutani {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E]
    {C : Set E} (hne : C.Nonempty) (hC : IsCompact C) (hc : Convex ℝ C)
    (T : E → Set E) (hT : UpperHemicontinuousOn T C)
    (hvalues : ∀ x ∈ C, (T x).Nonempty ∧ IsClosed (T x) ∧ Convex ℝ (T x) ∧ T x ⊆ C) :
    ∃ x ∈ C, x ∈ T x := by
  sorry

/-- **35.21**: Browder–Göhde–Kirk requires uniform convexity of the Banach space,
not compactness of the nonexpansive map. -/
theorem exists_fixedPoint_nonexpansive {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [UniformConvexSpace E]
    {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C) (hbounded : Bornology.IsBounded C)
    (hc : Convex ℝ C) (T : C → C) (hT : LipschitzWith 1 T) : ∃ x : C, T x = x := by
  sorry

end CKMA
