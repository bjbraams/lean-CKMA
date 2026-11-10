/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Semigroup.Sectorial
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import TauCeti.Analysis.Normed.Module.Dual.Reflexive.Basic

/-!
# Long-time semigroup stability

Uniform boundedness, exponential operator-norm decay and strong orbit decay.
Gearhart–Prüss characterizes exponential stability of bounded complex Hilbert-space
semigroups by their imaginary-axis resolvents. The reflexive Arendt–Batty–Lyubich–Vũ
criterion uses countable imaginary spectrum and absence of generator eigenvalues.
Semigroups and complex generators reuse TauCeti; duality and limits use Mathlib.
Sources: GAPS 24.39 and 24.40.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology TauCeti.Semigroups NormedSpace
open scoped NNReal

section Real

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Uniform boundedness of a semigroup on the entire nonnegative half-line. -/
def IsBoundedSemigroup (S : StronglyContinuousSemigroup X) : Prop :=
  ∃ M : ℝ, ∀ t : ℝ≥0, ‖S t‖ ≤ M

/-- Exponential decay in operator norm. -/
def IsExponentiallyStableSemigroup (S : StronglyContinuousSemigroup X) : Prop :=
  ∃ ε M : ℝ, 0 < ε ∧ ∀ t : ℝ≥0, ‖S t‖ ≤ M * Real.exp (-ε * t)

/-- Strong stability means decay of every orbit, without an operator-norm convergence assertion. -/
def IsStronglyStableSemigroup (S : StronglyContinuousSemigroup X) : Prop :=
  ∀ x : X, Tendsto (fun t : ℝ≥0 ↦ S t x) atTop (𝓝 0)

end Real

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A concrete eigenvector condition including the partial operator's domain. -/
def HasPartialOperatorEigenvalue (A : X →ₗ.[ℂ] X) (z : ℂ) : Prop :=
  ∃ x : A.domain, (x : X) ≠ 0 ∧ A x = z • (x : X)

/-- **24.39**, Gearhart–Prüss for a uniformly bounded semigroup on a complex Hilbert space.
This interface includes the uniform bound `IsBoundedSemigroup`. -/
theorem gearhart_pruss {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : StronglyContinuousSemigroup H) (hS : S.IsComplexLinear)
    (hb : IsBoundedSemigroup S) :
    IsExponentiallyStableSemigroup S ↔
      (∀ β : ℝ, (β : ℂ) * Complex.I ∈ (S.complexGenerator hS).resolventSet) ∧
      ∃ C : ℝ, ∀ β : ℝ, ‖(S.complexGenerator hS).resolvent ((β : ℂ) * Complex.I)‖ ≤ C := by
  sorry

omit [CompleteSpace X] in
/-- **24.40**, the reflexive Arendt–Batty–Lyubich–Vũ criterion.
This avoids introducing an unbounded Banach transpose with an unspecified domain. -/
theorem arendt_batty_lyubich_vu_reflexive (S : StronglyContinuousSemigroup X)
    (hS : S.IsComplexLinear) (hb : IsBoundedSemigroup S)
    (hr : Function.Surjective (inclusionInDoubleDual ℂ X))
    (hcount : ((S.complexGenerator hS).spectrum ∩ {z | z.re = 0}).Countable)
    (hpoint : ∀ β : ℝ, ¬ HasPartialOperatorEigenvalue (S.complexGenerator hS) ((β : ℂ) * Complex.I))
      :
    IsStronglyStableSemigroup S := by
  sorry

end CKMA
