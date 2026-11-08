/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.Semigroups.Resolvent.Basic
public import TauCeti.Analysis.Semigroups.Generator.Closed
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Inhomogeneous evolution and semigroup approximation

Variation-of-constants trajectories and their integrated and classical generator
equations. Trotter–Kato relates strong resolvent convergence to uniform strong convergence
on bounded time intervals under a common growth bound. Chernoff products are stable
families tangent to the generator on an actual core. Generators, resolvents and core
domains reuse TauCeti's semigroup modules; integration uses Mathlib.
Sources: GAPS 24.13, 24.17 and 24.18.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology TauCeti.Semigroups
open scoped NNReal

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The actual variation-of-constants trajectory, using the upstream real-time semigroup shim. -/
def forcedSemigroupTrajectory (S : StronglyContinuousSemigroup X) (x : X)
    (f : ℝ → X) (t : ℝ) : X := S.realOperator t x + ∫ s in (0 : ℝ)..t, S.realOperator (t - s) (f s)

/-- An integrated solution of `u'=Au+f`, phrased independently of the variation-of-constants
formula. The time integral, rather than every value of `u`, belongs to the generator domain. -/
def IsIntegratedSemigroupSolution (S : StronglyContinuousSemigroup X) (x : X)
    (f u : ℝ → X) (T : ℝ) : Prop :=
  ContinuousOn u (Set.Icc 0 T) ∧ ∀ t ∈ Set.Icc 0 T,
    ∃ h : (∫ s in (0 : ℝ)..t, u s) ∈ S.generator.domain,
      u t = x + S.generator ⟨∫ s in (0 : ℝ)..t, u s, h⟩ + ∫ s in (0 : ℝ)..t, f s

/-- **24.13**: the variation-of-constants formula is the unique continuous integrated solution. -/
theorem variation_of_constants (S : StronglyContinuousSemigroup X) {T : ℝ} (hT : 0 ≤ T)
    (x : X) {f : ℝ → X} (hf : IntegrableOn f (Set.Icc 0 T)) :
    IsIntegratedSemigroupSolution S x f (forcedSemigroupTrajectory S x f) T ∧
      ∀ u : ℝ → X, IsIntegratedSemigroupSolution S x f u T →
        Set.EqOn u (forcedSemigroupTrajectory S x f) (Set.Icc 0 T) := by
  sorry

/-- With domain initial data and C1 forcing, the trajectory is a classical solution in the
interior time interval, and all nonnegative-time values belong to the generator domain. -/
theorem variation_of_constants_classical (S : StronglyContinuousSemigroup X) {T : ℝ}
    (hT : 0 < T) (x : S.generator.domain) {f : ℝ → X}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 T)) :
    (∀ t ∈ Set.Icc 0 T, forcedSemigroupTrajectory S x f t ∈ S.generator.domain) ∧
      ∀ t ∈ Set.Ioo 0 T, ∃ h : forcedSemigroupTrajectory S x f t ∈ S.generator.domain,
        HasDerivAt (forcedSemigroupTrajectory S x f)
          (S.generator ⟨forcedSemigroupTrajectory S x f t, h⟩ + f t) t := by
  sorry

/-- Uniform strong convergence on every bounded nonnegative time interval. -/
def SemigroupsConvergeUniformlyOnCompacts
    (S : ℕ → StronglyContinuousSemigroup X) (T : StronglyContinuousSemigroup X) : Prop :=
  ∀ x : X, ∀ R : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
    ∀ t : ℝ≥0, t ≤ R → ‖S n t x - T t x‖ < ε

/-- **24.17**, Trotter–Kato: one sufficiently large real resolvent parameter characterizes
uniform-on-bounded-time strong semigroup convergence under a common exponential bound. -/
theorem trotter_kato (S : ℕ → StronglyContinuousSemigroup X)
    (T : StronglyContinuousSemigroup X) {ω M : ℝ}
    (hS : ∀ n, (S n).HasGrowthBound ω M) (hT : T.HasGrowthBound ω M)
    {r : ℝ} (hr : ω < r) :
    (∀ x : X, Tendsto (fun n ↦ (S n).generator.resolvent r x) atTop
      (𝓝 (T.generator.resolvent r x))) ↔ SemigroupsConvergeUniformlyOnCompacts S T := by
  sorry

/-- **24.18**, Chernoff: a stable strongly continuous product family tangent to a generator
on an actual core converges uniformly over bounded nonnegative time intervals. -/
theorem chernoff_product (S : StronglyContinuousSemigroup X)
    (F : ℝ≥0 → X →L[ℝ] X) (hF0 : F 0 = 1)
    (hF : ∀ x, Continuous (fun t ↦ F t x)) {M ω : ℝ}
    (hbound : ∀ t : ℝ≥0, ∀ n : ℕ, ‖F t ^ n‖ ≤ M * Real.exp (ω * n * t))
    (D : Submodule ℝ X) (hD : S.generator.HasCore D)
    (htangent : ∀ x : D, Tendsto (fun t : ℝ ↦ t⁻¹ • (F (Real.toNNReal t) x - x))
      (𝓝[>] 0) (𝓝 (S.generator ⟨x, hD.le_domain x.property⟩))) :
    ∀ x : X, ∀ R : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in atTop,
      ∀ t : ℝ≥0, t ≤ R → ‖(F (t / (n + 1 : ℝ≥0)) ^ (n + 1)) x - S t x‖ < ε := by
  sorry

end CKMA
