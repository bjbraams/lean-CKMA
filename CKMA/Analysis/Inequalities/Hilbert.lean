/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Hilbert integral and sequence inequalities

Hilbert's bilinear inequality on the positive half-line and its sequence analogue,
with conjugate exponents and constant `pi / sin (pi / p)`. The discrete denominator
`m+n+2` corresponds to positive integers `m+1,n+1`. Nonnegative integrals and sums
preserve infinite values; the input norms use Mathlib's `MemLp` and `eLpNorm`.
Source: GAPS 11.37.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped ENNReal

/-- Hilbert's sharp constant at exponent `p`. -/
def hilbertConstant (p : ℝ) : ℝ := Real.pi / Real.sin (Real.pi / p)

/-- **11.37**: Hilbert's integral inequality for nonnegative functions on the positive half-line.
The nonnegative integral avoids the totalized Bochner integral for infinite bilinear forms. -/
theorem hilbert_integral {p : ℝ} (hp : 1 < p) {f g : ℝ → ℝ}
    (hf0 : ∀ᵐ x ∂volume.restrict (Set.Ioi 0), 0 ≤ f x)
    (hg0 : ∀ᵐ x ∂volume.restrict (Set.Ioi 0), 0 ≤ g x)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Ioi 0)))
    (hg : MemLp g (ENNReal.ofReal (p / (p - 1))) (volume.restrict (Set.Ioi 0))) :
    (∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ y in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (f x * g y / (x + y))) ≤
      ENNReal.ofReal (hilbertConstant p) *
        eLpNorm f (ENNReal.ofReal p) (volume.restrict (Set.Ioi 0)) *
        eLpNorm g (ENNReal.ofReal (p / (p - 1))) (volume.restrict (Set.Ioi 0)) := by
  sorry

/-- The discrete Hilbert inequality; indices `m,n : ℕ` represent the positive integers `m+1,n+1`. -/
theorem hilbert_tsum {p : ℝ} (hp : 1 < p) {a b : ℕ → ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n)
    (ha : MemLp a (ENNReal.ofReal p) Measure.count)
    (hb : MemLp b (ENNReal.ofReal (p / (p - 1))) Measure.count) :
    (∑' m, ∑' n, ENNReal.ofReal (a m * b n / (m + n + 2 : ℝ))) ≤
      ENNReal.ofReal (hilbertConstant p) * eLpNorm a (ENNReal.ofReal p) Measure.count *
        eLpNorm b (ENNReal.ofReal (p / (p - 1))) Measure.count := by
  sorry

end CKMA
