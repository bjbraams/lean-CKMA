/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Absolutely convergent bilateral Fourier series

Functions on the unit circle are represented by Fourier series indexed by the integers, with
summable coefficient norms. Circle elements are nonzero, so negative integer powers are
well-defined. Coefficient convolution records multiplication of these series; Wiener's lemma
asserts closure under pointwise inversion for functions with no zero on the circle.
Source: GAPS 20.40.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped BigOperators

/-- A bilateral Fourier series evaluated on the unit circle. -/
def wienerSeries (a : ℤ → ℂ) (z : Circle) : ℂ := ∑' n, a n * (z : ℂ) ^ n

/-- Absolute Fourier convergence, with a specified circle-valued function. -/
def HasAbsolutelyConvergentFourierSeries (f : Circle → ℂ) : Prop :=
  ∃ a : ℤ → ℂ, Summable (fun n ↦ ‖a n‖) ∧ f = wienerSeries a

/-- Convolution of bilateral coefficient sequences. -/
def wienerConvolution (a b : ℤ → ℂ) (n : ℤ) : ℂ := ∑' k, a k * b (n - k)

/-- **20.40**, Wiener's lemma: inversion preserves absolutely convergent Fourier series. -/
theorem HasAbsolutelyConvergentFourierSeries.inv {f : Circle → ℂ}
    (hf : HasAbsolutelyConvergentFourierSeries f) (hzero : ∀ z, f z ≠ 0) :
    HasAbsolutelyConvergentFourierSeries (fun z ↦ (f z)⁻¹) := by
  sorry

end CKMA
