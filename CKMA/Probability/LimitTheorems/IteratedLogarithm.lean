/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# The Hartman–Wintner law of the iterated logarithm (06.27)

For i.i.d. centred real random variables of positive finite variance `σ²`, the partial sums
divided by `√(2 σ² n log log n)` have limsup `1` and liminf `-1` almost surely. Limits are taken
in `EReal`, and the index is shifted by three so that `log log n > 0`.

## Main definitions

* `CKMA.iteratedLogScale`: the iterated-logarithm normalization `√(2 σ² n log log n)`.

## Main results

* `CKMA.hartman_wintner`: Hartman–Wintner law of the iterated logarithm (**06.27**).
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory Filter Topology

/-- The iterated-logarithm normalization `√(2 σ² n log log n)`. For `n ≤ 2` the logarithm
`log log n` is not positive and the square root is the junk value `0`. -/
@[expose]
def iteratedLogScale (varianceParam : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (2 * varianceParam * n * Real.log (Real.log n))

/-- Defining formula of `iteratedLogScale`. -/
lemma iteratedLogScale_def (varianceParam : ℝ) (n : ℕ) :
    iteratedLogScale varianceParam n = Real.sqrt (2 * varianceParam * n * Real.log (Real.log n)) :=
  rfl

/-- **06.27**: the Hartman–Wintner law of the iterated logarithm.
The shift by three keeps `log log` positive (`log log 3 ≈ 0.094`) without changing the limit.
Measurability of the `X n` is not assumed: `hid` gives a.e. measurability. -/
theorem hartman_wintner {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hi : iIndepFun X μ) (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    (hX : MemLp (X 0) 2 μ) (hc : ∫ ω, X 0 ω ∂μ = 0) (hv : 0 < variance (X 0) μ) :
    ∀ᵐ ω ∂μ,
      limsup (fun n : ℕ ↦ (((∑ j ∈ Finset.range (n + 3), X j ω) /
        iteratedLogScale (variance (X 0) μ) (n + 3) : ℝ) : EReal)) atTop = 1 ∧
      liminf (fun n : ℕ ↦ (((∑ j ∈ Finset.range (n + 3), X j ω) /
        iteratedLogScale (variance (X 0) μ) (n + 3) : ℝ) : EReal)) atTop = -1 := by
  sorry

end CKMA
