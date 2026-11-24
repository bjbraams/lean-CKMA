/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Calculus.FDeriv.Defs

/-!
# Analytic Hardy classes and canonical disk factors

Radial means over normalized angular measure define the finite-exponent Hardy gauge;
the bounded holomorphic class uses the disk supremum gauge. Boundary realization
includes nontangential limits, exact norm identities and finite-p radial convergence.
Blaschke products, singular inner factors and outer factors give canonical
factorization of nonzero Hardy functions. The infinity endpoint has no asserted
radial L∞ norm convergence.

Sources: GAPS 42.1 and 42.7.

## Main definitions

* `CKMA.unitCirclePoint`, `CKMA.normalizedAngularMeasure`: angular parametrization and normalized
  measure on the unit circle.
* `CKMA.hardyRadialMean`, `CKMA.hardyGauge`, `CKMA.MemHardyClass`: finite-exponent analytic Hardy
  gauge and membership predicate.
* `CKMA.diskSupGauge`, `CKMA.MemHardyInfinity`: disk supremum gauge and bounded holomorphic
  functions on the disk.
* `CKMA.HasNontangentialLimit`: nontangential boundary limit in every Stolz region.
* `CKMA.IsDiskInner`: inner functions on the disk.
* `CKMA.blaschkeFactor`, `CKMA.IsBlaschkeZeroList`, `CKMA.blaschkeProduct`: Blaschke factors,
  zero lists and products.
* `CKMA.diskHerglotzKernel`, `CKMA.singularInnerFactor`, `CKMA.outerFactor`: Herglotz kernel,
  singular inner factor and outer factor.

## Main results

* `CKMA.hardy_boundary_realization`, `CKMA.hardyInfinity_boundary_realization`: nontangential
  boundary values and norm identities, with radial `Lᵖ` convergence for finite `p` (**42.1**).
* `CKMA.exists_hardy_factorization`: canonical Blaschke–singular–outer factorization (**42.7**).
-/

public section

noncomputable section

namespace CKMA

open Filter Topology MeasureTheory
open scoped BigOperators ENNReal ComplexConjugate

/-- The angular parametrization of the unit circle. -/
@[expose]
def unitCirclePoint (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

/-- Normalized angular measure, on a half-open period so each circle point is represented once. -/
@[expose]
def normalizedAngularMeasure : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Set.Ioc 0 (2 * Real.pi))

/-- The radial `p`th mean, retaining infinite values. -/
@[expose]
def hardyRadialMean (p : ℝ) (f : ℂ → ℂ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ t, (ENNReal.ofReal ‖f ((r : ℂ) * unitCirclePoint t)‖) ^ p ∂normalizedAngularMeasure

/-- The analytic Hardy gauge for finite positive exponents. -/
@[expose]
def hardyGauge (p : ℝ) (f : ℂ → ℂ) : ℝ≥0∞ :=
  (⨆ (r : ℝ) (_hr : 0 ≤ r ∧ r < 1), hardyRadialMean p f r) ^ (1 / p)

/-- Membership of the analytic Hardy class; theorems require `p>0`. -/
@[expose]
def MemHardyClass (p : ℝ) (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f complexUnitDisk ∧ hardyGauge p f ≠ ∞

/-- The extended supremum norm of a function on the disk. -/
@[expose]
def diskSupGauge (f : ℂ → ℂ) : ℝ≥0∞ :=
  ⨆ (z : ℂ) (_hz : z ∈ complexUnitDisk), ENNReal.ofReal ‖f z‖

/-- Bounded holomorphic functions on the disk. -/
@[expose]
def MemHardyInfinity (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f complexUnitDisk ∧ diskSupGauge f ≠ ∞

/-- A nontangential boundary limit, required in every fixed Stolz region. -/
@[expose]
def HasNontangentialLimit (f : ℂ → ℂ) (ζ L : ℂ) : Prop :=
  ∀ A : ℝ, 1 < A → Tendsto f
    (𝓝[{z ∈ complexUnitDisk | ‖z - ζ‖ ≤ A * (1 - ‖z‖)}] ζ) (𝓝 L)

/-- **42.1**, all finite positive exponents: boundary values, exact norm and radial `Lᵖ`
  convergence. -/
theorem hardy_boundary_realization {p : ℝ} (hp : 0 < p) {f : ℂ → ℂ}
    (hf : MemHardyClass p f) :
    ∃ g : ℝ → ℂ, Measurable g ∧ MemLp g (ENNReal.ofReal p) normalizedAngularMeasure ∧
      (∀ᵐ t ∂normalizedAngularMeasure, HasNontangentialLimit f (unitCirclePoint t) (g t)) ∧
      hardyGauge p f = eLpNorm g (ENNReal.ofReal p) normalizedAngularMeasure ∧
      Tendsto (fun r : ℝ ↦ eLpNorm
        (fun t ↦ f ((r : ℂ) * unitCirclePoint t) - g t)
        (ENNReal.ofReal p) normalizedAngularMeasure) (𝓝[<] 1) (𝓝 0) := by
  sorry

/-- The infinity endpoint has boundary values and the essential-supremum norm identity.
Radial convergence in `L∞` is deliberately not asserted. -/
theorem hardyInfinity_boundary_realization {f : ℂ → ℂ} (hf : MemHardyInfinity f) :
    ∃ g : ℝ → ℂ, Measurable g ∧ MemLp g ∞ normalizedAngularMeasure ∧
      (∀ᵐ t ∂normalizedAngularMeasure, HasNontangentialLimit f (unitCirclePoint t) (g t)) ∧
      diskSupGauge f = eLpNorm g ∞ normalizedAngularMeasure := by
  sorry

/-- Inner functions: bounded by one in the disk, with boundary modulus one almost everywhere. -/
@[expose]
def IsDiskInner (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f complexUnitDisk ∧ diskSupGauge f ≤ 1 ∧
    ∀ᵐ t ∂normalizedAngularMeasure,
      Tendsto (fun r : ℝ ↦ ‖f ((r : ℂ) * unitCirclePoint t)‖) (𝓝[<] 1) (𝓝 1)

/-- A normalized elementary Blaschke factor. -/
@[expose]
def blaschkeFactor (a z : ℂ) : ℂ :=
  if a = 0 then z else (‖a‖ : ℂ) / a * (a - z) / (1 - conj a * z)

/-- A finite or infinite Blaschke zero list; `none` permits finite lists without dummy zeros. -/
@[expose]
def IsBlaschkeZeroList (a : ℕ → Option ℂ) : Prop :=
  (∀ n z, a n = some z → ‖z‖ < 1) ∧
    (∑' n, match a n with | none => (0 : ℝ≥0∞) | some z => ENNReal.ofReal (1 - ‖z‖)) < ∞

/-- The pointwise Blaschke product of a zero list. -/
@[expose]
def blaschkeProduct (a : ℕ → Option ℂ) (z : ℂ) : ℂ :=
  ∏' n, match a n with | none => 1 | some w => blaschkeFactor w z

/-- The disk Herglotz kernel at a boundary angle. -/
@[expose]
def diskHerglotzKernel (z : ℂ) (t : ℝ) : ℂ :=
  (unitCirclePoint t + z) / (unitCirclePoint t - z)

/-- Singular inner factor `exp (-∫ diskHerglotzKernel z ∂μ)`.
No finiteness hypothesis is required. The Bochner integral of a non-integrable integrand is `0`,
so the value is `1` in that case. -/
@[expose]
def singularInnerFactor (μ : Measure ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-∫ t, diskHerglotzKernel z t ∂μ)

/-- Outer factor `exp (∫ diskHerglotzKernel z · Real.log ∘ h)`.
Positivity and log-integrability of `h` are not required; they belong to
`exists_hardy_factorization`. `Real.log` of a nonpositive argument is `0`. A non-integrable
integrand integrates to `0`, and then the value is `1`. -/
@[expose]
def outerFactor (h : ℝ → ℝ) (z : ℂ) : ℂ :=
  Complex.exp (∫ t, diskHerglotzKernel z t * Real.log (h t) ∂normalizedAngularMeasure)

/-- **42.7**, canonical factorization existence. The uniqueness-up-to-phase interface remains.
The singular measure is supported on one half-open angular period to avoid duplicate endpoint data.
  -/
theorem exists_hardy_factorization {p : ℝ} (hp : 0 < p) {f : ℂ → ℂ}
    (hf : MemHardyClass p f) (hne : ∃ z ∈ complexUnitDisk, f z ≠ 0) :
    ∃ (c : ℂ) (a : ℕ → Option ℂ) (μ : Measure ℝ) (h : ℝ → ℝ),
      ‖c‖ = 1 ∧ IsBlaschkeZeroList a ∧ IsFiniteMeasure μ ∧
      μ (Set.Ioc 0 (2 * Real.pi))ᶜ = 0 ∧ μ.MutuallySingular normalizedAngularMeasure ∧
      Measurable h ∧ (∀ᵐ t ∂normalizedAngularMeasure, 0 < h t) ∧
      Integrable (fun t ↦ Real.log (h t)) normalizedAngularMeasure ∧
      MemLp h (ENNReal.ofReal p) normalizedAngularMeasure ∧
      ∀ z ∈ complexUnitDisk,
        f z = c * blaschkeProduct a z * singularInnerFactor μ z * outerFactor h z := by
  sorry

end CKMA
