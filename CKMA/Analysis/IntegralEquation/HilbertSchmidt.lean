/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Square-integrable kernels and Hilbert–Schmidt operators

A complex L2 kernel on a sigma-finite measure space defines an operator on L2 through an a.e.
integral identity. A supplied, possibly non-countably indexed Hilbert basis records its exact
Hilbert–Schmidt energy without a separability assumption. The adjoint kernel is obtained by
transposing the variables and conjugating. Source: GAPS 25.3; the Hilbert–Schmidt energy is
TauCeti's existing construction.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory ContinuousLinearMap
open scoped ENNReal ComplexConjugate

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

/-- An operator has kernel `k` when its `L²` action is given by the integral formula a.e. -/
def HasIntegralKernel (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (k : X × X → ℂ) : Prop :=
  ∀ f : Lp ℂ 2 μ, (fun x ↦ T f x) =ᵐ[μ] fun x ↦ ∫ y, k (x, y) * f y ∂μ

/-- **25.3**: an `L²` kernel defines a unique bounded integral operator with its exact
Hilbert–Schmidt energy and transposed conjugate adjoint kernel. -/
theorem existsUnique_integralOperator {k : X × X → ℂ} (hk : MemLp k 2 (μ.prod μ))
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) :
    ∃! T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ,
      HasIntegralKernel μ T k ∧
      T.hilbertSchmidtEnergy b = (eLpNorm k 2 (μ.prod μ)) ^ 2 ∧
      HasIntegralKernel μ T.adjoint (fun p ↦ conj (k (p.2, p.1))) := by
  sorry

end CKMA
