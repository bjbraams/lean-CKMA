/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.RCLike.Basic

/-!
# Surjective scalar Lp duality

The scalar pairing integrates `f * star g`, so it is linear in the first argument and
conjugate-linear in the representing function. On sigma-finite measure spaces, every continuous
linear functional on Lp for finite `p ≥ 1` is represented by a unique conjugate-exponent Lq
function with the same norm. The endpoint `p=1, q=∞` is included. Source: GAPS 04.39.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped ENNReal

variable {𝕜 X : Type*} [RCLike 𝕜] [MeasurableSpace X]

/-- The scalar `Lᵖ` dual pairing, linear in its first argument and conjugate-linear in its second.
  -/
def lpDualPairing {p q : ℝ≥0∞} {μ : Measure X} (f : Lp 𝕜 p μ) (g : Lp 𝕜 q μ) : 𝕜 :=
  ∫ x, f x * star (g x) ∂μ

/-- **04.39**: every scalar functional is represented by a unique conjugate-exponent function,
with the norm identity. Sigma-finiteness includes the `p=1, q=∞` endpoint. -/
theorem existsUnique_lpDualRepresentation (μ : Measure X) [SigmaFinite μ]
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : p < ∞)
    (hpq : p⁻¹ + q⁻¹ = 1) (ℓ : Lp 𝕜 p μ →L[𝕜] 𝕜) :
    ∃! g : Lp 𝕜 q μ, (∀ f, ℓ f = lpDualPairing f g) ∧ ‖ℓ‖ = ‖g‖ := by
  sorry

end CKMA
