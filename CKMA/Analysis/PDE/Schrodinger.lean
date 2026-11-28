/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.PDE.Euclidean
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Schrödinger spacetime norms and the focusing virial identity

Mixed Lebesgue gauges, admissible Strichartz exponents and free Schrödinger evolution
in Mathlib's `2*pi` Fourier convention. The homogeneous estimate is stated on Schwartz
inputs. Focusing NLS energy and spatial variance give the classical virial identity
for smooth rapidly decaying solutions with local uniform bounds on spacetime derivatives.
Essential suprema and Lebesgue norms use Mathlib's measure-theoretic infrastructure.
Sources: GAPS 34.24 and 34.32.

## Main definitions

* `CKMA.mixedLebesgueGauge`: mixed `L_t^q L_x^r` spacetime norm gauge.
* `CKMA.IsSchrodingerAdmissible`: Schrödinger-admissible exponent pairs `(q, r)`.
* `CKMA.freeSchrodinger`: free Schrödinger evolution via the Fourier transform.
* `CKMA.focusingNLSEnergy`, `CKMA.nlsVariance`: energy and spatial variance for focusing NLS.
* `CKMA.IsClassicalFocusingNLS`: classical solutions of the focusing NLS equation.

## Main results

* `CKMA.homogeneous_strichartz` (**34.24**): global homogeneous Strichartz estimate on Schwartz
  inputs.
* `CKMA.focusing_nls_virial` (**34.32**): the classical Glassey virial identity for focusing NLS.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform ComplexConjugate

/-- A mixed `L_t^q L_x^r` gauge for positive exponents, including `q = ∞`.
Infinite spatial norms remain infinite; exponent zero retains the totalized power convention. -/
@[expose]
def mixedLebesgueGauge {d : ℕ} (q r : ℝ≥0∞) (I : Set ℝ)
    (u : ℝ → EuclideanSpace ℝ (Fin d) → ℂ) : ℝ≥0∞ :=
  if q = ∞ then essSup (fun t ↦ eLpNorm (u t) r volume) (volume.restrict I)
  else (∫⁻ t in I, (eLpNorm (u t) r volume) ^ q.toReal) ^ (1 / q.toReal)

/-- Schrödinger admissibility, including infinite exponents and excluding the forbidden endpoint. -/
@[expose]
def IsSchrodingerAdmissible (d : ℕ) (q r : ℝ≥0∞) : Prop :=
  2 ≤ q ∧ 2 ≤ r ∧ 2 * (q⁻¹).toReal + d * (r⁻¹).toReal = (d : ℝ) / 2 ∧
    ¬ (q = 2 ∧ r = ∞ ∧ d = 2)

/-- Free Schrödinger evolution on integrable inputs in Mathlib's `2π` Fourier convention. -/
@[expose]
def freeSchrodinger {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℂ) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℂ :=
  ∫ ξ, Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ) -
    4 * Real.pi ^ 2 * Complex.I * t * ‖ξ‖ ^ 2) * (𝓕 f) ξ

/-- Unfolding the mixed Lebesgue gauge. -/
theorem mixedLebesgueGauge_def {d : ℕ} (q r : ℝ≥0∞) (I : Set ℝ)
    (u : ℝ → EuclideanSpace ℝ (Fin d) → ℂ) :
    mixedLebesgueGauge q r I u =
      if q = ∞ then essSup (fun t ↦ eLpNorm (u t) r volume) (volume.restrict I)
      else (∫⁻ t in I, (eLpNorm (u t) r volume) ^ q.toReal) ^ (1 / q.toReal) := rfl

/-- The mixed gauge with `q = ∞` is the essential supremum of the spatial norms. -/
@[simp]
theorem mixedLebesgueGauge_top {d : ℕ} (r : ℝ≥0∞) (I : Set ℝ)
    (u : ℝ → EuclideanSpace ℝ (Fin d) → ℂ) :
    mixedLebesgueGauge ∞ r I u = essSup (fun t ↦ eLpNorm (u t) r volume) (volume.restrict I) :=
  by simp [mixedLebesgueGauge]

/-- The mixed gauge with finite `q`. -/
theorem mixedLebesgueGauge_of_ne_top {d : ℕ} {q : ℝ≥0∞} (hq : q ≠ ∞) (r : ℝ≥0∞) (I : Set ℝ)
    (u : ℝ → EuclideanSpace ℝ (Fin d) → ℂ) :
    mixedLebesgueGauge q r I u =
      (∫⁻ t in I, (eLpNorm (u t) r volume) ^ q.toReal) ^ (1 / q.toReal) :=
  by simp [mixedLebesgueGauge, hq]

/-- Unfolding Schrödinger admissibility. -/
theorem isSchrodingerAdmissible_iff {d : ℕ} {q r : ℝ≥0∞} :
    IsSchrodingerAdmissible d q r ↔
      2 ≤ q ∧ 2 ≤ r ∧ 2 * (q⁻¹).toReal + d * (r⁻¹).toReal = (d : ℝ) / 2 ∧
        ¬ (q = 2 ∧ r = ∞ ∧ d = 2) := Iff.rfl

/-- Unfolding the free Schrödinger evolution. -/
theorem freeSchrodinger_def {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℂ) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    freeSchrodinger f t x = ∫ ξ, Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ) -
      4 * Real.pi ^ 2 * Complex.I * t * ‖ξ‖ ^ 2) * (𝓕 f) ξ := rfl

/-- **34.24**, the global homogeneous Strichartz estimate on Schwartz inputs: for an admissible
pair `(q, r)` there is `C > 0` with `‖e^{itΔ} f‖_{L_t^q L_x^r} ≤ C ‖f‖₂` for every Schwartz `f`.
In dimension `0` admissibility forces `q = ∞` and the estimate holds with `C = 1`. -/
theorem homogeneous_strichartz {d : ℕ} {q r : ℝ≥0∞}
    (hqr : IsSchrodingerAdmissible d q r) : ∃ C : ℝ, 0 < C ∧
      ∀ f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ,
        mixedLebesgueGauge q r Set.univ (freeSchrodinger f) ≤
          ENNReal.ofReal C * eLpNorm f 2 volume := by
  sorry

/-- Focusing NLS energy with the usual `1/2` and `1/(p+1)` normalization. -/
@[expose]
def focusingNLSEnergy {d : ℕ} (p : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℂ) : ℝ :=
  (1 / 2 : ℝ) * (∫ x, ∑ j : Fin d, ‖fderiv ℝ u x (euclideanUnitVector j)‖ ^ 2) -
    (p + 1)⁻¹ * ∫ x, ‖u x‖ ^ (p + 1)

/-- Spatial variance of a complex wave. -/
@[expose]
def nlsVariance {d : ℕ} (u : EuclideanSpace ℝ (Fin d) → ℂ) : ℝ :=
  ∫ x, ‖x‖ ^ 2 * ‖u x‖ ^ 2

/-- The classical focusing NLS equation `i u_t + Δu = -|u|^{p-1}u`. -/
@[expose]
def IsClassicalFocusingNLS {d : ℕ} (p : ℝ)
    (u : ℝ → EuclideanSpace ℝ (Fin d) → ℂ) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, ∀ x, Complex.I * deriv (fun s ↦ u s x) t + Laplacian.laplacian (u t) x =
    -(‖u t x‖ ^ (p - 1) : ℝ) • u t x

/-- Unfolding the focusing NLS energy. -/
theorem focusingNLSEnergy_def {d : ℕ} (p : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℂ) :
    focusingNLSEnergy p u =
      (1 / 2 : ℝ) * (∫ x, ∑ j : Fin d, ‖fderiv ℝ u x (euclideanUnitVector j)‖ ^ 2) -
        (p + 1)⁻¹ * ∫ x, ‖u x‖ ^ (p + 1) := rfl

/-- Unfolding the spatial variance. -/
theorem nlsVariance_def {d : ℕ} (u : EuclideanSpace ℝ (Fin d) → ℂ) :
    nlsVariance u = ∫ x, ‖x‖ ^ 2 * ‖u x‖ ^ 2 := rfl

/-- The spatial variance is nonnegative. -/
theorem nlsVariance_nonneg {d : ℕ} (u : EuclideanSpace ℝ (Fin d) → ℂ) : 0 ≤ nlsVariance u :=
  integral_nonneg fun _ ↦ by positivity

/-- Unfolding the classical focusing NLS equation. -/
theorem isClassicalFocusingNLS_iff {d : ℕ} {p : ℝ} {u : ℝ → EuclideanSpace ℝ (Fin d) → ℂ}
    {I : Set ℝ} :
    IsClassicalFocusingNLS p u I ↔
      ∀ t ∈ I, ∀ x, Complex.I * deriv (fun s ↦ u s x) t + Laplacian.laplacian (u t) x =
        -(‖u t x‖ ^ (p - 1) : ℝ) • u t x := Iff.rfl

/-- **34.32**, the virial identity for a three times continuously differentiable Schwartz-valued
solution of the focusing NLS, with local uniform bounds on its spacetime derivatives:
`V''(t) = 16 E(u(t)) - 4 (d (p - 1) - 4) / (p + 1) ∫ |u(t)|^{p+1}`. In dimension `0` both
sides vanish. -/
theorem focusing_nls_virial {d : ℕ} {p : ℝ} (hp : 1 < p)
    (u : ℝ → SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) {I : Set ℝ} (hI : IsOpen I)
    (hu : ContDiffOn ℝ 3 (fun z : ℝ × EuclideanSpace ℝ (Fin d) ↦ u z.1 z.2) (I ×ˢ Set.univ))
    (hdecay : ∀ K : Set ℝ, IsCompact K → K ⊆ I → ∀ N k : ℕ, k ≤ 3 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ K, ∀ x : EuclideanSpace ℝ (Fin d),
        ‖iteratedFDeriv ℝ k (fun z : ℝ × EuclideanSpace ℝ (Fin d) ↦ u z.1 z.2) (t, x)‖ ≤
          C * (1 + ‖x‖) ^ (-(N : ℝ)))
    (hNLS : IsClassicalFocusingNLS p (fun t x ↦ u t x) I)
    {t : ℝ} (ht : t ∈ I) :
    deriv (deriv (fun s ↦ nlsVariance (u s))) t =
      16 * focusingNLSEnergy p (u t) -
        (4 * ((d : ℝ) * (p - 1) - 4) / (p + 1)) * ∫ x, ‖u t x‖ ^ (p + 1) := by
  sorry

end CKMA
