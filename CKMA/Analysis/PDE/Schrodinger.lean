/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.PDE.Euclidean
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Schrödinger spacetime norms and the focusing virial identity

Mixed Lebesgue gauges, admissible Strichartz exponents and free Schrödinger evolution
in Mathlib's `2*pi` Fourier convention. The homogeneous estimate is stated on Schwartz
inputs. Focusing NLS energy and spatial variance give the classical virial identity
for smooth rapidly decaying solutions with local uniform bounds on spacetime derivatives.
Essential suprema and Lebesgue norms use Mathlib's measure-theoretic infrastructure.
Sources: GAPS 34.24 and 34.32.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform ComplexConjugate

/-- Mathlib essential supremum in the measure-first convention used for the spacetime gauges. -/
abbrev nonnegativeEssentialSup {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ≥0∞) : ℝ≥0∞ :=
  essSup f μ

/-- A mixed `L_t^q L_x^r` gauge for positive exponents, including `q = ∞`.
Infinite spatial norms remain infinite; exponent zero retains the totalized power convention. -/
def mixedLebesgueGauge {d : ℕ} (q r : ℝ≥0∞) (I : Set ℝ)
    (u : ℝ → EuclideanRealSpace d → ℂ) : ℝ≥0∞ :=
  if q = ∞ then nonnegativeEssentialSup (volume.restrict I) (fun t ↦ eLpNorm (u t) r volume)
  else (∫⁻ t in I, (eLpNorm (u t) r volume) ^ q.toReal) ^ (1 / q.toReal)

/-- Schrödinger admissibility, including infinite exponents and excluding the forbidden endpoint. -/
def IsSchrodingerAdmissible (d : ℕ) (q r : ℝ≥0∞) : Prop :=
  2 ≤ q ∧ 2 ≤ r ∧ 2 * (q⁻¹).toReal + d * (r⁻¹).toReal = (d : ℝ) / 2 ∧
    ¬ (q = 2 ∧ r = ∞ ∧ d = 2)

/-- Free Schrödinger evolution on integrable inputs in Mathlib's `2π` Fourier convention. -/
def freeSchrodinger {d : ℕ} (f : EuclideanRealSpace d → ℂ) (t : ℝ)
    (x : EuclideanRealSpace d) : ℂ :=
  ∫ ξ, Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ) -
    4 * Real.pi ^ 2 * Complex.I * t * ‖ξ‖ ^ 2) * (𝓕 f) ξ

/-- **34.24**: global homogeneous Strichartz on the dense Schwartz input class.
The bounded operator extension to all `L²` inputs is a separate interface. -/
theorem homogeneous_strichartz {d : ℕ} (hd : 0 < d) {q r : ℝ≥0∞}
    (hqr : IsSchrodingerAdmissible d q r) : ∃ C : ℝ, 0 < C ∧
      ∀ f : SchwartzMap (EuclideanRealSpace d) ℂ,
        mixedLebesgueGauge q r Set.univ (freeSchrodinger f) ≤ ENNReal.ofReal C * eLpNorm f 2 volume
          := by
  sorry

/-- Focusing NLS energy with the usual `1/2` and `1/(p+1)` normalization. -/
def focusingNLSEnergy {d : ℕ} (p : ℝ) (u : EuclideanRealSpace d → ℂ) : ℝ :=
  (1 / 2 : ℝ) * (∫ x, ∑ j : Fin d, ‖fderiv ℝ u x (euclideanUnitVector j)‖ ^ 2) -
    (p + 1)⁻¹ * ∫ x, ‖u x‖ ^ (p + 1)

/-- Spatial variance of a complex wave. -/
def nlsVariance {d : ℕ} (u : EuclideanRealSpace d → ℂ) : ℝ :=
  ∫ x, ‖x‖ ^ 2 * ‖u x‖ ^ 2

/-- The classical focusing NLS equation `i u_t + Δu = -|u|^{p-1}u`. -/
def IsClassicalFocusingNLS {d : ℕ} (p : ℝ)
    (u : ℝ → EuclideanRealSpace d → ℂ) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, ∀ x, Complex.I * deriv (fun s ↦ u s x) t + Laplacian.laplacian (u t) x =
    -(‖u t x‖ ^ (p - 1) : ℝ) • u t x

/-- **34.32**, the virial identity for a twice continuously differentiable Schwartz-valued
solution, with local uniform bounds on its spacetime derivatives.
This is the smooth rapidly decaying core; finite-variance energy-class approximation
and the maximal-time blowup conclusion remain separate interfaces. -/
theorem focusing_nls_virial {d : ℕ} (hd : 0 < d) {p : ℝ} (hp : 1 < p)
    (u : ℝ → SchwartzMap (EuclideanRealSpace d) ℂ) {I : Set ℝ} (hI : IsOpen I)
    (hu : ContDiffOn ℝ 3 (fun z : ℝ × EuclideanRealSpace d ↦ u z.1 z.2) (I ×ˢ Set.univ))
    (hdecay : ∀ K : Set ℝ, IsCompact K → K ⊆ I → ∀ N k : ℕ, k ≤ 3 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ K, ∀ x : EuclideanRealSpace d,
        ‖iteratedFDeriv ℝ k (fun z : ℝ × EuclideanRealSpace d ↦ u z.1 z.2) (t, x)‖ ≤
          C * (1 + ‖x‖) ^ (-(N : ℝ)))
    (hNLS : IsClassicalFocusingNLS p (fun t x ↦ u t x) I)
    {t : ℝ} (ht : t ∈ I) :
    deriv (deriv (fun s ↦ nlsVariance (u s))) t =
      16 * focusingNLSEnergy p (u t) -
        (4 * ((d : ℝ) * (p - 1) - 4) / (p + 1)) * ∫ x, ‖u t x‖ ^ (p + 1) := by
  sorry

end CKMA
