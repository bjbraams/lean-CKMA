/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic

/-!
# Hausdorff moment sequences (48.34)

Complete monotonicity uses forward differences with the alternating sign convention.
`hausdorffWeight` and `hausdorffApproximant` give the Bernstein discrete measures used
in the moment construction. Supporting lemmas prove nonnegativity of the weights and
nonnegativity and antitonicity of the original sequence.

The main theorem characterizes these sequences by a unique finite positive measure
concentrated on `[0,1]`. No probability normalization is imposed, so zero mass is included.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped BigOperators ENNReal

/-- The forward difference of a real sequence. -/
def forwardDifference (s : ℕ → ℝ) (n : ℕ) : ℝ := s (n + 1) - s n

/-- Discrete complete monotonicity with the forward-difference sign convention. -/
def IsCompletelyMonotoneSequence (s : ℕ → ℝ) : Prop :=
  ∀ n k : ℕ, 0 ≤ (-1 : ℝ) ^ k * ((forwardDifference^[k]) s) n

/-- Bernstein weights in the constructive Hausdorff approximation. -/
def hausdorffWeight (s : ℕ → ℝ) (N k : ℕ) : ℝ :=
  (N.choose k : ℝ) * ((-1 : ℝ) ^ (N - k) * ((forwardDifference^[N - k]) s) k)

/-- The finite discrete measure approximating a Hausdorff moment law. -/
def hausdorffApproximant (s : ℕ → ℝ) (N : ℕ) : Measure ℝ :=
  ∑ k ∈ Finset.range (N + 1), ENNReal.ofReal (hausdorffWeight s N k) •
    Measure.dirac ((k : ℝ) / N)

/-- Complete monotonicity makes every Bernstein weight nonnegative. -/
theorem IsCompletelyMonotoneSequence.hausdorffWeight_nonneg {s : ℕ → ℝ}
    (hs : IsCompletelyMonotoneSequence s) (N k : ℕ) : 0 ≤ hausdorffWeight s N k :=
  mul_nonneg (Nat.cast_nonneg _) (hs k (N - k))

/-- Complete monotonicity includes nonnegativity of the sequence. -/
theorem IsCompletelyMonotoneSequence.nonneg {s : ℕ → ℝ}
    (hs : IsCompletelyMonotoneSequence s) (n : ℕ) : 0 ≤ s n := by
  simpa using hs n 0

/-- Complete monotonicity includes antitonicity. -/
theorem IsCompletelyMonotoneSequence.antitone {s : ℕ → ℝ}
    (hs : IsCompletelyMonotoneSequence s) : Antitone s := by
  apply antitone_nat_of_succ_le
  intro n
  have h := hs n 1
  simp only [pow_one, Function.iterate_one, forwardDifference] at h
  linarith

/-- A finite measure concentrated on `[0,1]` represents all the moments of `s`. -/
def RepresentsHausdorffMoments (μ : Measure ℝ) (s : ℕ → ℝ) : Prop :=
  IsFiniteMeasure μ ∧ μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧ ∀ n : ℕ, ∫ x, x ^ n ∂μ = s n

/-- **48.34**: the Hausdorff existence and uniqueness theorem, including the zero measure. -/
theorem completelyMonotoneSequence_iff_existsUnique_measure (s : ℕ → ℝ) :
    IsCompletelyMonotoneSequence s ↔ ∃! μ : Measure ℝ, RepresentsHausdorffMoments μ s := by
  sorry

end CKMA
