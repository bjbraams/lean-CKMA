/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Topology.Basic

/-!
# Bessel second solutions, Airy and Mittag–Leffler functions

The Bessel second-kind connection formula is continued in its order at integers;
its principal slit-plane solution has the standard differential equation and
Wronskian. Airy solutions are defined by their entire initial-value power series and
an oscillatory real integral. Positive-order Mittag–Leffler series are entire for
arbitrary complex second parameter and include the exponential at parameters `(1,1)`.

Sources: GAPS 49.26, 49.36 and 49.76. First-kind Bessel and Gamma functions reuse Mathlib.
The exponential specialization uses Mathlib's Gamma factorial values and exponential series.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped BigOperators

/-- The nonintegral-order connection formula for the Bessel function of the second kind. -/
def besselYConnection (ν z : ℂ) : ℂ :=
  (Complex.cos (Real.pi * ν) * Complex.besselJ ν z - Complex.besselJ (-ν) z) /
    Complex.sin (Real.pi * ν)

/-- The second Bessel solution, using the order-limit at integers.
`limUnder` is a totalized limit; the convergence theorem below certifies its intended value
on the slit plane. This definition has no admitted dependency. -/
def besselY (ν z : ℂ) : ℂ := by
  classical
  exact if ∃ n : ℤ, ν = (n : ℂ) then
    Filter.limUnder (𝓝[≠] ν) (fun μ ↦ besselYConnection μ z) else besselYConnection ν z

/-- The outgoing Hankel function. -/
def hankelOne (ν z : ℂ) : ℂ := Complex.besselJ ν z + Complex.I * besselY ν z

/-- The incoming Hankel function. -/
def hankelTwo (ν z : ℂ) : ℂ := Complex.besselJ ν z - Complex.I * besselY ν z

/-- **49.26**, nonintegral-order connection formula, directly from the definition. -/
theorem besselY_of_noninteger {ν z : ℂ} (hν : ¬ ∃ n : ℤ, ν = (n : ℂ)) :
    besselY ν z = besselYConnection ν z := by
  classical
  simp [besselY, hν]

/-- The order-limit exists at each integer, for arguments in the principal slit plane. -/
theorem tendsto_besselYConnection_int (n : ℤ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    Tendsto (fun ν ↦ besselYConnection ν z) (𝓝[≠] (n : ℂ)) (𝓝 (besselY n z)) := by
  sorry

/-- The second-kind solution satisfies Bessel's equation on its principal branch. -/
theorem besselY_ode (ν : ℂ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    z ^ 2 * deriv (deriv (besselY ν)) z + z * deriv (besselY ν) z +
      (z ^ 2 - ν ^ 2) * besselY ν z = 0 := by
  sorry

/-- The Wronskian normalization certifies independence of the first- and second-kind solutions. -/
theorem besselJ_besselY_wronskian (ν : ℂ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    Complex.besselJ ν z * deriv (besselY ν) z - deriv (Complex.besselJ ν) z * besselY ν z =
      2 / (Real.pi * z) := by
  sorry

/-- Coefficients for the Airy initial-value problem `y''=zy`, with `y(0)=a₀`, `y'(0)=a₁`. -/
def airySeriesCoefficient (a₀ a₁ : ℂ) (n : ℕ) : ℂ :=
  if n % 3 = 0 then a₀ /
    ∏ k ∈ Finset.range (n / 3), ((3 * k + 3 : ℕ) : ℂ) * ((3 * k + 2 : ℕ) : ℂ)
  else if n % 3 = 1 then a₁ /
    ∏ k ∈ Finset.range (n / 3), ((3 * k + 4 : ℕ) : ℂ) * ((3 * k + 3 : ℕ) : ℂ)
  else 0

/-- The canonical Airy power-series solution with specified initial data. -/
def airySeries (a₀ a₁ z : ℂ) : ℂ := ∑' n, airySeriesCoefficient a₀ a₁ n * z ^ n

/-- The decaying Airy function with the standard Gamma normalization at zero. -/
def airyAi (z : ℂ) : ℂ :=
  airySeries ((3 : ℂ) ^ (-(2 : ℂ) / 3) / Complex.Gamma (2 / 3))
    (-((3 : ℂ) ^ (-(1 : ℂ) / 3)) / Complex.Gamma (1 / 3)) z

/-- The normalized power series solves Airy's equation everywhere. -/
theorem airySeries_ode (a₀ a₁ z : ℂ) :
    deriv (deriv (airySeries a₀ a₁)) z = z * airySeries a₀ a₁ z := by
  sorry

/-- The Airy initial conditions and convergence of the defining power series. -/
theorem airySeries_initial_and_hasSum (a₀ a₁ : ℂ) :
    airySeries a₀ a₁ 0 = a₀ ∧ deriv (airySeries a₀ a₁) 0 = a₁ ∧
      ∀ z, HasSum (fun n ↦ airySeriesCoefficient a₀ a₁ n * z ^ n) (airySeries a₀ a₁ z) := by
  sorry

/-- **49.36**: the oscillatory real-axis integral for the Airy function, interpreted by truncation.
  -/
theorem airyAi_eq_oscillatory_integral (x : ℝ) :
    Tendsto (fun T : ℝ ↦ Real.pi⁻¹ * ∫ t in (0 : ℝ)..T, Real.cos (t ^ 3 / 3 + x * t))
      atTop (𝓝 ((airyAi x).re)) := by
  sorry

/-- The two-parameter Mittag–Leffler series, with positive real first parameter in its theorems.
Reciprocals of Gamma at its poles use Mathlib's totalized value zero, as required by `1/Γ`. -/
def mittagLeffler (α : ℝ) (β z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n / Complex.Gamma ((α : ℂ) * n + β)

/-- **49.76**, convergence and entireness clause for arbitrary complex second parameter. -/
theorem mittagLeffler_hasSum_and_entire {α : ℝ} (hα : 0 < α) (β : ℂ) :
    (∀ z, HasSum (fun n : ℕ ↦ z ^ n / Complex.Gamma ((α : ℂ) * n + β))
      (mittagLeffler α β z)) ∧ Differentiable ℂ (mittagLeffler α β) := by
  sorry

/-- The exponential is the Mittag–Leffler function with parameters `(1,1)`. -/
theorem mittagLeffler_one_one (z : ℂ) : mittagLeffler 1 1 z = Complex.exp z := by
  simp only [mittagLeffler, Complex.ofReal_one, one_mul, Complex.Gamma_nat_eq_factorial]
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]

end CKMA
