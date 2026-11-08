/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family.Schatten
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Schatten products and the Hilbert-space trace

Schatten gauges reuse TauCeti's operator-ideal family, with finite Banach exponents at least one.
The product estimate has constant one at conjugate exponents. Trace class is finiteness of the
Schatten-one gauge.

A supplied Hilbert basis defines the scalar trace sum. Trace-class membership gives absolute
convergence, independence of the possibly differently indexed basis, and cyclicity under bounded
multiplication. Inner products are linear in the second slot. Sources: GAPS 21.22 and 21.23.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped ENNReal InnerProductSpace

variable {𝕜 H K L ι κ : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace 𝕜 L] [CompleteSpace L]

/-- The upstream Schatten gauge. No second approximation-number definition is introduced. -/
abbrev schattenGauge (p : ℝ) (hp : 1 ≤ p) (T : H →L[𝕜] K) : ℝ≥0∞ :=
  (TauCeti.OperatorIdealFamily.schatten 𝕜 p hp).gauge T

/-- **21.22**: the constant-one Schatten Hölder estimate at finite exponents. -/
theorem schatten_holder {p q r : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hpqr : r⁻¹ = p⁻¹ + q⁻¹) (S : K →L[𝕜] L) (T : H →L[𝕜] K) :
    schattenGauge r hr (S.comp T) ≤ schattenGauge p hp S * schattenGauge q hq T := by
  sorry

/-- Trace-class membership through the actual upstream extended Schatten-one gauge. -/
def IsTraceClassOperator (T : H →L[𝕜] K) : Prop := schattenGauge 1 le_rfl T ≠ ∞

/-- Trace computed in a supplied Hilbert basis, using Mathlib's second-variable-linear inner
product convention. The trace-class theorems establish that this sum is legitimate. -/
def hilbertTrace (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] H) : 𝕜 :=
  ∑' i, ⟪b i, T (b i)⟫_𝕜

omit [CompleteSpace H] in
/-- The trace of the zero operator is zero. -/
theorem hilbertTrace_zero (b : HilbertBasis ι 𝕜 H) : hilbertTrace b (0 : H →L[𝕜] H) = 0 := by
  simp [hilbertTrace]

/-- **21.23**: absolute convergence and the trace-norm bound for every Hilbert basis. -/
theorem IsTraceClassOperator.summable_trace {T : H →L[𝕜] H} (hT : IsTraceClassOperator T)
    (b : HilbertBasis ι 𝕜 H) :
    Summable (fun i ↦ ‖⟪b i, T (b i)⟫_𝕜‖) ∧
      ‖hilbertTrace b T‖ₑ ≤ schattenGauge 1 le_rfl T := by
  sorry

/-- The trace is independent of the possibly differently indexed Hilbert basis. -/
theorem hilbertTrace_basis_independent {T : H →L[𝕜] H} (hT : IsTraceClassOperator T)
    (b : HilbertBasis ι 𝕜 H) (c : HilbertBasis κ 𝕜 H) : hilbertTrace b T = hilbertTrace c T := by
  sorry

/-- Bounded multiplication preserves trace class, and the trace is cyclic. -/
theorem IsTraceClassOperator.trace_cyclic {T : H →L[𝕜] H} (hT : IsTraceClassOperator T)
    (A : H →L[𝕜] H) (b : HilbertBasis ι 𝕜 H) :
    IsTraceClassOperator (A.comp T) ∧ IsTraceClassOperator (T.comp A) ∧
      hilbertTrace b (A.comp T) = hilbertTrace b (T.comp A) := by
  sorry

end CKMA
