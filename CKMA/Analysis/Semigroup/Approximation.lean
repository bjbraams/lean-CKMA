/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.Semigroups.Generator.Basic
public import Mathlib.Topology.Algebra.Module.LinearPMap
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Chernoff product formula

A family `F : ℝ≥0 → X →L[ℝ] X` with `F 0 = 1`, the stability bound
`‖F t ^ n‖ ≤ M e^{ω n t}` and the tangent condition `t⁻¹ (F t x - x) → A x` on a core of the
generator `A` of a strongly continuous semigroup `S` gives `F (t / n) ^ n x → S t x` uniformly on
bounded time intervals. Source: GAPS 24.18.

## Main results

* `CKMA.chernoff_product`: the Chernoff product formula (**24.18**).

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*.
-/

public section

noncomputable section

namespace CKMA

open Filter Topology TauCeti.Semigroups
open scoped NNReal

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **24.18**, **Chernoff product formula**: a family `F` with `F 0 = 1`, the stability bound
`‖F t ^ n‖ ≤ M e^{ω n t}` and the tangent condition `t⁻¹ (F t x - x) → A x` on a core `D` of the
generator `A` of `S` satisfies `F (t / (n + 1)) ^ (n + 1) x → S t x` uniformly for `t ∈ [0, R]`,
for every `x` and `R`. No continuity of `t ↦ F t` is assumed. -/
theorem chernoff_product (S : StronglyContinuousSemigroup X)
    (F : ℝ≥0 → X →L[ℝ] X) (hF0 : F 0 = 1) {M ω : ℝ}
    (hbound : ∀ t : ℝ≥0, ∀ n : ℕ, ‖F t ^ n‖ ≤ M * Real.exp (ω * n * t))
    (D : Submodule ℝ X) (hD : S.generator.HasCore D)
    (htangent : ∀ x : D, Tendsto (fun t : ℝ ↦ t⁻¹ • (F (Real.toNNReal t) x - x))
      (𝓝[>] 0) (𝓝 (S.generator ⟨x, hD.le_domain x.property⟩))) (x : X) (R : ℝ≥0) :
    TendstoUniformlyOn (fun (n : ℕ) (t : ℝ≥0) ↦ (F (t / (n + 1 : ℝ≥0)) ^ (n + 1)) x)
      (fun t ↦ S t x) atTop (Set.Iic R) := by
  sorry

end CKMA
