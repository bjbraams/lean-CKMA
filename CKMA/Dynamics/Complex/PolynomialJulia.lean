/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.Orbit
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Polynomial Julia sets, escape rates and entire escape (46)

The filled Julia set consists of bounded forward polynomial orbits, using the general
bornological `HasBoundedOrbit` interface. Its boundary defines the polynomial Julia set.
The main targets relate repelling and attracting cycles, the logarithmic escape-rate
limit and connectedness through finite critical orbits for degree at least two.

The quadratic critical-orbit convention defines the Mandelbrot set. The entire-function
branch defines escaping orbits and states the nonemptiness and unbounded-closure-component
clauses of Eremenko's theorem. Derivatives and iteration use Mathlib's conventions.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Polynomial Filter Topology

/-- The filled Julia set of a complex polynomial, by bounded forward iteration. -/
def polynomialFilledJuliaSet (p : ℂ[X]) : Set ℂ :=
  {z | HasBoundedOrbit (fun w ↦ p.eval w) z}

/-- Filled Julia sets are completely invariant under one polynomial step. -/
theorem mem_polynomialFilledJuliaSet_iff (p : ℂ[X]) (z : ℂ) :
    p.eval z ∈ polynomialFilledJuliaSet p ↔ z ∈ polynomialFilledJuliaSet p := by
  change HasBoundedOrbit (fun w ↦ p.eval w) (p.eval z) ↔
    HasBoundedOrbit (fun w ↦ p.eval w) z
  exact ⟨HasBoundedOrbit.of_map (f := fun w ↦ p.eval w), HasBoundedOrbit.map⟩

/-- The polynomial Julia set as the boundary of its filled set.
Its equality to the nonnormality Julia set is a separate analytic interface. -/
def polynomialJuliaSet (p : ℂ[X]) : Set ℂ := frontier (polynomialFilledJuliaSet p)

/-- A periodic point is repelling when its return multiplier has norm greater than one. -/
def repellingComplexPeriodicPoints (f : ℂ → ℂ) : Set ℂ :=
  {z | ∃ n : ℕ, 0 < n ∧ (f^[n]) z = z ∧ 1 < ‖deriv (f^[n]) z‖}

/-- **46.6**, polynomial scope: repelling periodic points are dense in the polynomial Julia set. -/
theorem closure_repellingPeriodicPoints {p : ℂ[X]} (hp : 2 ≤ p.natDegree) :
    closure (repellingComplexPeriodicPoints (fun z ↦ p.eval z)) = polynomialJuliaSet p := by
  sorry

/-- Attracting polynomial periodic points lie outside the Julia set. -/
theorem attractingPeriodicPoint_not_mem_julia {p : ℂ[X]} (hp : 2 ≤ p.natDegree)
    {z : ℂ} {n : ℕ} (hn : 0 < n) (hperiod : ((fun w ↦ p.eval w)^[n]) z = z)
    (hattr : ‖deriv ((fun w ↦ p.eval w)^[n]) z‖ < 1) : z ∉ polynomialJuliaSet p := by
  sorry

/-- Polynomial escape-rate approximants with the standard `log⁺` normalization. -/
def polynomialEscapeRateApproximation (p : ℂ[X]) (z : ℂ) (n : ℕ) : ℝ :=
  (p.natDegree : ℝ)⁻¹ ^ n * Real.log (max 1 ‖((fun w ↦ p.eval w)^[n]) z‖)

/-- The escape-rate function as a totalized limit. Actual convergence is certified explicitly
below, so this definition does not hide any admitted choice or convergence theorem. -/
def polynomialEscapeRate (p : ℂ[X]) (z : ℂ) : ℝ :=
  Filter.limUnder atTop (polynomialEscapeRateApproximation p z)

/-- The Green escape-rate limit exists, is continuous and vanishes precisely on the filled set. -/
theorem polynomial_escapeRate_properties {p : ℂ[X]} (hp : 2 ≤ p.natDegree) :
    (∀ z, Tendsto (polynomialEscapeRateApproximation p z) atTop (𝓝 (polynomialEscapeRate p z))) ∧
      Continuous (polynomialEscapeRate p) ∧
      (∀ z, 0 ≤ polynomialEscapeRate p z) ∧
      (∀ z, polynomialEscapeRate p (p.eval z) = p.natDegree * polynomialEscapeRate p z) ∧
      ∀ z, polynomialEscapeRate p z = 0 ↔ z ∈ polynomialFilledJuliaSet p := by
  sorry

/-- The filled Julia set is nonempty and compact for a polynomial of degree at least two. -/
theorem polynomialFilledJuliaSet_nonempty_isCompact {p : ℂ[X]} (hp : 2 ≤ p.natDegree) :
    (polynomialFilledJuliaSet p).Nonempty ∧ IsCompact (polynomialFilledJuliaSet p) := by
  sorry

/-- **46.29**: polynomial connectedness is equivalent to boundedness of every finite critical orbit.
  -/
theorem polynomial_julia_connected_iff {p : ℂ[X]} (hp : 2 ≤ p.natDegree) :
    (IsConnected (polynomialFilledJuliaSet p) ↔
      ∀ z : ℂ, p.derivative.eval z = 0 → z ∈ polynomialFilledJuliaSet p) ∧
    (IsConnected (polynomialJuliaSet p) ↔ IsConnected (polynomialFilledJuliaSet p)) := by
  sorry

/-- The standard quadratic family. -/
def quadraticFamily (c : ℂ) : ℂ[X] := X ^ 2 + C c

/-- The Mandelbrot set is the set of bounded quadratic critical orbits. -/
def mandelbrotSet : Set ℂ := {c | HasBoundedOrbit (fun z ↦ z ^ 2 + c) 0}

/-- **46.40**: Mandelbrot compactness, connectedness, escape bound and the Julia criterion. -/
theorem mandelbrot_properties : IsCompact mandelbrotSet ∧ IsConnected mandelbrotSet ∧
    mandelbrotSet ⊆ Metric.closedBall 0 2 ∧
    ∀ c : ℂ, c ∈ mandelbrotSet ↔ IsConnected (polynomialJuliaSet (quadraticFamily c)) := by
  sorry

/-- The escaping set of a complex map, using divergence of the orbit norm. -/
def complexEscapingSet (f : ℂ → ℂ) : Set ℂ :=
  {z | Tendsto (fun n : ℕ ↦ ‖(f^[n]) z‖) atTop atTop}

/-- Transcendental entire functions are entire and are not polynomial functions. -/
def IsTranscendentalEntire (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ ∀ p : ℂ[X], f ≠ fun z ↦ p.eval z

/-- **46.58**, escaping-set clauses: nonemptiness and unbounded components of the closure.
The equality of its boundary with the nonnormality Julia set remains a separate interface. -/
theorem eremenko_escaping {f : ℂ → ℂ} (hf : IsTranscendentalEntire f) :
    (complexEscapingSet f).Nonempty ∧
      ∀ z ∈ closure (complexEscapingSet f),
        ¬ Bornology.IsBounded (connectedComponentIn (closure (complexEscapingSet f)) z) := by
  sorry

end CKMA
