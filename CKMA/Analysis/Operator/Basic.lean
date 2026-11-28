/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family.Schatten
public import TauCeti.Analysis.OperatorIdeal.Nuclear.Basic
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Schatten gauges, trace class and the Hilbert-space trace

The basic operator-ideal interfaces used across sections. The Schatten gauge is TauCeti's
`TauCeti.OperatorIdealFamily.schatten`, at finite Banach exponents `1 ≤ p`. Trace class is
finiteness of TauCeti's nuclear gauge `ContinuousLinearMap.nuclearENorm`, which is the
Schatten-one gauge. The Hilbert trace is the diagonal sum `∑' i, ⟪b i, T (b i)⟫` in a supplied
Hilbert basis `b`; inner products are linear in the second slot. Its theorems (absolute
convergence, basis independence and cyclicity for trace-class operators) are in
`CKMA.Analysis.Operator.TraceIdeals`.

## Main definitions

* `CKMA.schattenGauge`: the Schatten `p`-gauge from TauCeti.
* `CKMA.IsTraceClassOperator`: membership in the trace class `S₁`.
* `CKMA.hilbertTrace`: scalar trace of an operator with respect to a Hilbert basis.

## Main results

* `CKMA.schattenGauge_def`, `CKMA.isTraceClassOperator_iff`, `CKMA.hilbertTrace_def`: the
  defining equations.
* `CKMA.hilbertTrace_zero`: the trace of the zero operator vanishes.
-/

public section

noncomputable section

namespace CKMA

open scoped ENNReal InnerProductSpace

variable {𝕜 H K ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]

/-- The Schatten `p`-gauge of an operator between Hilbert spaces, at a finite exponent
`1 ≤ p`: the gauge of TauCeti's Schatten operator-ideal family. -/
abbrev schattenGauge [CompleteSpace H] [CompleteSpace K] (p : ℝ) (hp : 1 ≤ p)
    (T : H →L[𝕜] K) : ℝ≥0∞ :=
  (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge T

/-- The Schatten gauge is the gauge of TauCeti's Schatten family. -/
theorem schattenGauge_def [CompleteSpace H] [CompleteSpace K] (p : ℝ) (hp : 1 ≤ p)
    (T : H →L[𝕜] K) :
    schattenGauge p hp T = (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge T :=
  rfl

/-- Trace-class membership: finiteness of TauCeti's nuclear gauge
`ContinuousLinearMap.nuclearENorm`, the Schatten-one gauge. -/
@[expose]
def IsTraceClassOperator (T : H →L[𝕜] K) : Prop := T.nuclearENorm ≠ ∞

/-- An operator is trace class iff its nuclear gauge is finite. -/
theorem isTraceClassOperator_iff (T : H →L[𝕜] K) :
    IsTraceClassOperator T ↔ T.nuclearENorm ≠ ∞ :=
  Iff.rfl

/-- Introduction rule for `IsTraceClassOperator`. -/
theorem IsTraceClassOperator.of_nuclearENorm_ne_top {T : H →L[𝕜] K} (h : T.nuclearENorm ≠ ∞) :
    IsTraceClassOperator T :=
  h

/-- Elimination rule for `IsTraceClassOperator`. -/
theorem IsTraceClassOperator.nuclearENorm_ne_top {T : H →L[𝕜] K} (h : IsTraceClassOperator T) :
    T.nuclearENorm ≠ ∞ :=
  h

/-- Trace computed in a supplied Hilbert basis, using Mathlib's second-variable-linear inner
product convention. For an operator that is not trace class the series may fail to converge,
and then `tsum` gives the junk value `0`. -/
@[expose]
def hilbertTrace (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] H) : 𝕜 :=
  ∑' i, ⟪b i, T (b i)⟫_𝕜

/-- The Hilbert trace is the diagonal sum in the basis. -/
theorem hilbertTrace_def (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] H) :
    hilbertTrace b T = ∑' i, ⟪b i, T (b i)⟫_𝕜 :=
  rfl

/-- The trace of the zero operator is zero. -/
@[simp]
theorem hilbertTrace_zero (b : HilbertBasis ι 𝕜 H) : hilbertTrace b (0 : H →L[𝕜] H) = 0 := by
  simp [hilbertTrace_def]

end CKMA
