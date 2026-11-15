/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Asymptotics.Expansions

/-!
# Directional Borel–Laplace summation

The Borel transform starts with the coefficient of the first power and divides by
factorials. An analytic continuation of exponential growth to a sector of opening `β` determines
the directional Laplace integral along its central ray, using the complex line element. Near the
origin this integral agrees, on each closed proper subsector of the sector of opening `π`, with
a function holomorphic on the sector of opening `π + β` that has uniform Gevrey-one remainders
on proper subsectors.

Source: GAPS 50.45.

## Main definitions

* `CKMA.borelTransformSeries`: formal Borel transform of a power series.
* `CKMA.directionalBorelLaplaceSum`: directional Laplace sum along a ray.
* `CKMA.HasSectorialGevreyOneExpansion`: uniform Gevrey-one asymptotic expansion on subsectors.
* `CKMA.HasBorelContinuation`: analytic continuation of the Borel transform with exponential growth.

## Main results

* `CKMA.exists_borelLaplace_sum`: Borel–Laplace summation on a sector of opening `π + β`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology
open scoped BigOperators

/-- The formal Borel transform as a scalar series, indexed from the coefficient of `z¹`. -/
def borelTransformSeries (a : ℕ → ℂ) (ξ : ℂ) : ℂ :=
  ∑' n : ℕ, a (n + 1) * ξ ^ n / (n.factorial : ℂ)

/-- Directional Laplace summation along the ray of angle `θ`, with its complex line element. -/
def directionalBorelLaplaceSum (a₀ : ℂ) (b : ℂ → ℂ) (θ : ℝ) (z : ℂ) : ℂ :=
  a₀ + Complex.exp ((θ : ℂ) * Complex.I) *
    ∫ t in Set.Ioi (0 : ℝ),
      Complex.exp (-(Complex.exp ((θ : ℂ) * Complex.I) * t) / z) *
        b (Complex.exp ((θ : ℂ) * Complex.I) * t)

/-- Gevrey-one remainder estimates, uniform on every closed proper subsector. -/
def HasSectorialGevreyOneExpansion (f : ℂ → ℂ) (a : ℕ → ℂ) (θ ω : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → η < ω → ∃ C A r : ℝ, 0 < C ∧ 0 < A ∧ 0 < r ∧
    ∀ (N : ℕ) (z : ℂ), z ∈ closedComplexSector θ η → ‖z‖ < r →
      ‖f z - ∑ n ∈ Finset.range N, a n * z ^ n‖ ≤
        C * A ^ N * (N.factorial : ℝ) * ‖z‖ ^ N

/-- Analytic Borel continuation with exponential growth and the prescribed convergent germ. -/
def HasBorelContinuation (a : ℕ → ℂ) (b : ℂ → ℂ) (θ β : ℝ) : Prop :=
  (∃ r : ℝ, 0 < r ∧ DifferentiableOn ℂ b (complexSector θ β ∪ Metric.ball 0 r) ∧
    ∀ ξ : ℂ, ‖ξ‖ < r → HasSum (fun n : ℕ ↦ a (n + 1) * ξ ^ n / (n.factorial : ℂ)) (b ξ)) ∧
  ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ ξ ∈ complexSector θ β, ‖b ξ‖ ≤ C * Real.exp (A * ‖ξ‖)

/-- **50.45**: a Borel continuation of opening `β` sums to a function holomorphic on the sector
of opening `π + β`, with a uniform Gevrey-one expansion on its proper subsectors. On each closed
proper subsector of the sector of opening `π`, the sum agrees with the directional Laplace
integral for small `z`; the radius depends on the subsector, since the integral converges only
where `Re (exp (θ * I) / z)` exceeds the exponential growth rate of `b`. -/
theorem exists_borelLaplace_sum (a : ℕ → ℂ) (b : ℂ → ℂ) (θ : ℝ) {β : ℝ}
    (hβ : 0 < β) (hβπ : β < Real.pi) (hb : HasBorelContinuation a b θ β) :
    ∃ (f : ℂ → ℂ) (r : ℝ), 0 < r ∧
      DifferentiableOn ℂ f (complexSector θ (Real.pi + β) ∩ Metric.ball 0 r) ∧
      HasSectorialGevreyOneExpansion f a θ (Real.pi + β) ∧
      ∀ η : ℝ, 0 < η → η < Real.pi → ∃ r' : ℝ, 0 < r' ∧
        ∀ z ∈ closedComplexSector θ η, ‖z‖ < r' →
          f z = directionalBorelLaplaceSum (a 0) b θ z := by
  sorry

end CKMA
