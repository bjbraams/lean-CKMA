/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Euler–Maclaurin summation with periodic remainder

The inclusive sum over integer endpoints is expressed as an interval integral,
half-endpoint values, Bernoulli derivative corrections and an exact signed periodic
Bernoulli remainder. The order is positive, and the remainder involves the derivative
of order twice that order.

Source: GAPS 50.23. Bernoulli functions and numbers reuse Mathlib's zeta-value API.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped BigOperators

/-- The signed Euler–Maclaurin remainder for the convention used in `GAPS_EASY.md`. -/
def eulerMaclaurinRemainder (p : ℕ) (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  -((2 * p).factorial : ℝ)⁻¹ * ∫ x in a..b,
    periodizedBernoulli (2 * p) (x : AddCircle (1 : ℝ)) * iteratedDeriv (2 * p) f x

/-- **50.23**: inclusive integer-endpoint Euler–Maclaurin with its exact periodic remainder.
Equal endpoints are included: both sides reduce to `f m`. The displayed remainder convention
requires `p ≥ 1`; the `p=0` formula is different. -/
theorem euler_maclaurin {m n : ℤ} (hmn : m ≤ n) {p : ℕ} (hp : 0 < p)
    (f : ℝ → ℝ) (hf : ContDiff ℝ (2 * p) f) :
    (∑ k ∈ Finset.Icc m n, f k) = (∫ x in (m : ℝ)..n, f x) + (f m + f n) / 2 +
      (∑ r ∈ Finset.range p, ((bernoulli (2 * (r + 1)) : ℚ) : ℝ) /
        (2 * (r + 1)).factorial *
        (iteratedDeriv (2 * r + 1) f n - iteratedDeriv (2 * r + 1) f m)) +
      eulerMaclaurinRemainder p f m n := by
  sorry

end CKMA
