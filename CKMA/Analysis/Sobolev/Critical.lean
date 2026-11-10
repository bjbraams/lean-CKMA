/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Critical Sobolev functions that are essentially unbounded

In dimension at least two, every nonempty open set contains an essentially unbounded
`W^{1,d}` function. A logarithmic radial profile describes the local singularity before
a smooth cutoff. Weak derivatives reuse TauCeti, and Lebesgue norms use Mathlib.
Source: GAPS 26.16.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped ENNReal

/-- The radial logarithmic singularity used at the critical exponent, totalized at the origin.
A smooth cutoff is still needed to obtain a compactly supported Sobolev function. -/
def criticalSobolevProfile {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.log (Real.log (Real.exp 1 / ‖x‖))

/-- **26.16**: every nonempty open Euclidean domain in dimension at least two contains an
unbounded `W^{1,d}` function. The `L∞` failure is essential, rather than merely pointwise. -/
theorem exists_memSobolev_not_memLp_top {d : ℕ} (hd : 2 ≤ d)
    (Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))) (hne : (Ω : Set (EuclideanSpace ℝ (Fin
      d))).Nonempty) :
    ∃ (u : EuclideanSpace ℝ (Fin d) → ℝ)
      (U : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
      MemLp u (d : ℝ≥0∞) (volume.restrict Ω) ∧
      MemLp U (d : ℝ≥0∞) (volume.restrict Ω) ∧
      TauCeti.HasWeakFDerivOn volume Ω u U ∧ ¬ MemLp u ∞ (volume.restrict Ω) := by
  sorry

end CKMA
