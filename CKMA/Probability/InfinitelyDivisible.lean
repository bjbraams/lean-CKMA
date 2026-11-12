/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.InfinitelyDivisible.Existence
public import CKMA.Probability.InfinitelyDivisible.Uniqueness

/-!
# Infinite divisibility and Lévy–Khintchine triplets (06.51)

`convolutionPower` and `IsInfinitelyDivisible` use positive convolution roots of a real
probability law. `IsLevyMeasure` records the zero atom and integrability of the truncated
quadratic jump size. `LevyTriplet` packages Gaussian variance, drift and jump measure,
with its characteristic exponent using the stated truncation near zero.

The main equivalence characterizes infinite divisibility by a unique triplet. Its drift
and uniqueness are relative to this fixed truncation, rather than independent of that
convention.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory

/-- **06.51**: a real probability law is infinitely divisible exactly when it has a unique
Levy triplet for this fixed truncation convention. -/
theorem isInfinitelyDivisible_iff_existsUnique_levyTriplet (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    IsInfinitelyDivisible μ ↔
      ∃! L : LevyTriplet, ∀ t : ℝ, charFun μ t = Complex.exp (L.exponent t) := by
  constructor
  · intro h
    obtain ⟨L, hL⟩ := exists_levyTriplet_of_isInfinitelyDivisible h
    refine ⟨L, hL, ?_⟩
    intro L' hL'
    exact levyTriplet_eq_of_forall_charFun_eq fun t => by
      rw [← hL' t, hL t]
  · intro h
    obtain ⟨L, hL, -⟩ := h
    exact isInfinitelyDivisible_of_forall_charFun_eq_exp L hL

end CKMA
