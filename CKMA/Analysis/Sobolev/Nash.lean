/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Nash inequality

Nash's inequality on L¹∩H¹ with an actual weak derivative. Weak derivatives reuse TauCeti,
and Lebesgue norms and real powers use Mathlib.
Source: GAPS 14.40. The critical unboundedness statement is in `CKMA.Analysis.Sobolev.Critical`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped ENNReal

/-- **14.40**: Nash's inequality on `L¹ ∩ H¹`, including weak derivatives. -/
theorem nash {d : ℕ} (hd : 0 < d) : ∃ C : ℝ, 0 < C ∧
    ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ)
      (U : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
      MemLp u 1 volume → MemLp u 2 volume → MemLp U 2 volume →
      TauCeti.HasWeakFDerivOn volume ⊤ u U →
      (eLpNorm u 2 volume).toReal ^ (2 + 4 / (d : ℝ)) ≤
        C * (eLpNorm U 2 volume).toReal ^ 2 * (eLpNorm u 1 volume).toReal ^ (4 / (d : ℝ)) := by
  sorry

end CKMA
