/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import TauCeti.Analysis.Semigroups.Generator.ComplexLinear
public import TauCeti.Analysis.Semigroups.GrowthBound

/-!
# Long-time semigroup stability

Uniform boundedness, exponential operator-norm decay and strong orbit decay.
Gearhart–Prüss characterizes exponential stability of bounded complex Hilbert-space
semigroups by their imaginary-axis resolvents. The reflexive Arendt–Batty–Lyubich–Vũ
criterion uses countable imaginary spectrum and absence of generator eigenvalues.
Semigroups and complex generators reuse TauCeti; duality and limits use Mathlib.
Sources: GAPS 24.39 and 24.40.

## Main definitions

* `CKMA.IsBoundedSemigroup`: uniform operator-norm boundedness of a `C₀`-semigroup.
* `CKMA.IsExponentiallyStableSemigroup`: exponential operator-norm decay of a `C₀`-semigroup.
* `CKMA.IsStronglyStableSemigroup`: strong orbit decay to zero as `t → ∞`.
* `CKMA.HasPartialOperatorEigenvalue`: point-spectrum predicate for a partial linear operator.

## Main results

* `CKMA.isBoundedSemigroup_iff_exists_hasGrowthBound`,
  `CKMA.isExponentiallyStableSemigroup_iff_exists_hasGrowthBound`: the two norm conditions as
  TauCeti growth bounds `S.HasGrowthBound ω M`, with `ω = 0` and with some `ω < 0`.
* `CKMA.gearhart_pruss`: the Gearhart–Prüss theorem characterizing exponential stability on Hilbert
  spaces via uniform resolvent bounds on the imaginary axis (**24.39**).
* `CKMA.arendt_batty_lyubich_vu_reflexive`: the Arendt–Batty–Lyubich–Vũ strong stability
  theorem on reflexive Banach spaces (**24.40**).

## Implementation notes

The general Arendt–Batty–Lyubich–Vũ theorem asks that the adjoint generator have no purely
imaginary eigenvalue. On a reflexive space bounded semigroups are mean ergodic, and the same
condition on the generator itself suffices; `CKMA.arendt_batty_lyubich_vu_reflexive` uses that
form, so no unbounded Banach-space adjoint is needed.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*.
* W. Arendt and C. J. K. Batty, *Tauberian theorems and stability of one-parameter semigroups*.
* Yu. I. Lyubich and Vũ Quôc Phóng, *Asymptotic stability of linear differential equations in
  Banach spaces*.
-/

public section

noncomputable section

namespace CKMA

open Filter Topology TauCeti.Semigroups NormedSpace
open scoped NNReal

section Real

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Uniform boundedness of a semigroup on the entire nonnegative half-line. -/
@[expose]
def IsBoundedSemigroup (S : StronglyContinuousSemigroup X) : Prop :=
  ∃ M : ℝ, ∀ t : ℝ≥0, ‖S t‖ ≤ M

/-- Exponential decay in operator norm. -/
@[expose]
def IsExponentiallyStableSemigroup (S : StronglyContinuousSemigroup X) : Prop :=
  ∃ ε M : ℝ, 0 < ε ∧ ∀ t : ℝ≥0, ‖S t‖ ≤ M * Real.exp (-ε * t)

/-- Strong stability: every orbit tends to `0` as `t → ∞`. -/
@[expose]
def IsStronglyStableSemigroup (S : StronglyContinuousSemigroup X) : Prop :=
  ∀ x : X, Tendsto (fun t : ℝ≥0 ↦ S t x) atTop (𝓝 0)

/-- Unfolding uniform boundedness. -/
theorem isBoundedSemigroup_iff {S : StronglyContinuousSemigroup X} :
    IsBoundedSemigroup S ↔ ∃ M : ℝ, ∀ t : ℝ≥0, ‖S t‖ ≤ M :=
  Iff.rfl

/-- Unfolding exponential stability. -/
theorem isExponentiallyStableSemigroup_iff {S : StronglyContinuousSemigroup X} :
    IsExponentiallyStableSemigroup S ↔
      ∃ ε M : ℝ, 0 < ε ∧ ∀ t : ℝ≥0, ‖S t‖ ≤ M * Real.exp (-ε * t) :=
  Iff.rfl

/-- Unfolding strong stability. -/
theorem isStronglyStableSemigroup_iff {S : StronglyContinuousSemigroup X} :
    IsStronglyStableSemigroup S ↔ ∀ x : X, Tendsto (fun t : ℝ≥0 ↦ S t x) atTop (𝓝 0) :=
  Iff.rfl

/-- A semigroup is uniformly bounded iff it has a TauCeti growth bound with exponent `0`. -/
theorem isBoundedSemigroup_iff_exists_hasGrowthBound {S : StronglyContinuousSemigroup X} :
    IsBoundedSemigroup S ↔ ∃ M : ℝ, S.HasGrowthBound 0 M := by
  refine ⟨fun ⟨M, hM⟩ => ⟨max M 1, S.hasGrowthBound_of_bound (le_max_right _ _) fun t _ => ?_⟩,
    fun ⟨M, hM⟩ => ⟨M, fun t => ?_⟩⟩
  · rw [zero_mul, Real.exp_zero, mul_one, S.realOperator_def]
    exact (hM _).trans (le_max_left _ _)
  · simpa [S.realOperator_coe] using hM.bound t t.2

/-- A semigroup is exponentially stable iff it has a TauCeti growth bound with a negative
exponent. -/
theorem isExponentiallyStableSemigroup_iff_exists_hasGrowthBound
    {S : StronglyContinuousSemigroup X} :
    IsExponentiallyStableSemigroup S ↔ ∃ ω < 0, ∃ M : ℝ, S.HasGrowthBound ω M := by
  refine ⟨fun ⟨ε, M, hε, hM⟩ => ⟨-ε, neg_lt_zero.2 hε, max M 1,
    S.hasGrowthBound_of_bound (le_max_right _ _) fun t ht => ?_⟩,
    fun ⟨ω, hω, M, hM⟩ => ⟨-ω, M, neg_pos.2 hω, fun t => ?_⟩⟩
  · rw [S.realOperator_def, neg_mul]
    calc ‖S t.toNNReal‖ ≤ M * Real.exp (-ε * t.toNNReal) := hM _
      _ ≤ max M 1 * Real.exp (-(ε * t)) := by
        rw [Real.coe_toNNReal t ht, neg_mul]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
  · simpa [S.realOperator_coe] using hM.bound t t.2

end Real

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- `z` is an eigenvalue of the partial operator `A`: `A x = z • x` for some nonzero `x ∈ D(A)`. -/
@[expose]
def HasPartialOperatorEigenvalue (A : X →ₗ.[ℂ] X) (z : ℂ) : Prop :=
  ∃ x : A.domain, (x : X) ≠ 0 ∧ A x = z • (x : X)

omit [CompleteSpace X] in
/-- Unfolding the eigenvalue predicate. -/
theorem hasPartialOperatorEigenvalue_iff {A : X →ₗ.[ℂ] X} {z : ℂ} :
    HasPartialOperatorEigenvalue A z ↔ ∃ x : A.domain, (x : X) ≠ 0 ∧ A x = z • (x : X) :=
  Iff.rfl

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
/-- **24.40**, the reflexive Arendt–Batty–Lyubich–Vũ criterion: a bounded semigroup on a
reflexive complex Banach space whose generator has countable spectrum on the imaginary axis and
no purely imaginary eigenvalue is strongly stable. -/
theorem arendt_batty_lyubich_vu_reflexive (S : StronglyContinuousSemigroup X)
    (hS : S.IsComplexLinear) (hb : IsBoundedSemigroup S)
    (hr : Function.Surjective (inclusionInDoubleDual ℂ X))
    (hcount : ((S.complexGenerator hS).spectrum ∩ {z | z.re = 0}).Countable)
    (hpoint : ∀ β : ℝ, ¬ HasPartialOperatorEigenvalue (S.complexGenerator hS) ((β : ℂ) * Complex.I))
      :
    IsStronglyStableSemigroup S := by
  sorry

end CKMA
