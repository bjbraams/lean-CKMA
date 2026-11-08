/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Exact Lipschitz extension between Hilbert spaces

Kirszbraun extension preserves the Lipschitz bound of a map from an arbitrary subset
of a real inner-product space into a complete real Hilbert space. The subset may be
empty and the source need not be complete. Norms, distances and Lipschitz predicates
are Mathlib's. Source: GAPS 05.33.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped NNReal

/-- **05.33**: a Lipschitz map on any subset of a real inner-product space extends with
exactly the same bound into a complete real Hilbert target. The subset may be empty;
the domain need not be complete. -/
theorem exists_lipschitz_extension_hilbert {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (s : Set H) (f : s → K) {L : ℝ≥0} (hf : LipschitzWith L f) :
    ∃ g : H → K, LipschitzWith L g ∧ ∀ x : s, g x = f x := by
  sorry

end CKMA
