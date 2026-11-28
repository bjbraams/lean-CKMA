/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Potential.Basic
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Sobolev capacity, quasicontinuity and the BBM limit

Inhomogeneous first-order Sobolev capacity and quasicontinuous representatives, unique
outside capacity-zero sets. Fractional Gagliardo p-energy converges to gradient energy
in the Bourgain–Brezis–Mironescu limit, including p=1. The exact constant is a unit-ball
moment with factor `(d+p)/p`. Weak derivatives reuse TauCeti; extended energies and
integration use Mathlib. Sources: GAPS 26.31 and 26.42.

## Main definitions

* `CKMA.sobolevTestEnergy`: inhomogeneous first-order `p`-energy of a smooth test.
* `CKMA.compactSobolevCapacity`: variational `C_{1,p}` capacity on compact sets.
* `CKMA.sobolevCapacity`: outer Sobolev capacity on arbitrary sets.
* `CKMA.IsSobolevQuasicontinuous`: quasicontinuity with respect to Sobolev capacity.
* `CKMA.fractionalPEnergy`: fractional Gagliardo `p`-energy.
* `CKMA.bbmConstant`: Bourgain–Brezis–Mironescu unit-ball moment constant.

## Main results

* `CKMA.exists_sobolevQuasicontinuous_representative`: existence of quasicontinuous
  representatives for weak first-order Sobolev functions.
* `CKMA.sobolevQuasicontinuous_unique`: uniqueness outside a capacity-zero set.
* `CKMA.tendsto_fractionalPEnergy_bbm`: Bourgain–Brezis–Mironescu limit as `s → 1⁻`.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Inhomogeneous first-order `p`-energy of a smooth real function. -/
@[expose]
def sobolevTestEnergy {d : ℕ} (p : ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (|φ x| ^ p + ‖fderiv ℝ φ x‖ ^ p)

/-- Defining equation of `sobolevTestEnergy`. -/
theorem sobolevTestEnergy_def {d : ℕ} (p : ℝ) (φ : EuclideanSpace ℝ (Fin d) → ℝ) :
    sobolevTestEnergy p φ = ∫⁻ x, ENNReal.ofReal (|φ x| ^ p + ‖fderiv ℝ φ x‖ ^ p) := rfl

/-- Variational `C_{1,p}` capacity on compact sets, using smooth compactly supported tests. -/
@[expose]
def compactSobolevCapacity {d : ℕ} (p : ℝ) (K : Set (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ⨅ (φ : EuclideanSpace ℝ (Fin d) → ℝ) (_h : IsCapacityAdmissible K φ), sobolevTestEnergy p φ

/-- Defining equation of `compactSobolevCapacity`. -/
theorem compactSobolevCapacity_def {d : ℕ} (p : ℝ) (K : Set (EuclideanSpace ℝ (Fin d))) :
    compactSobolevCapacity p K =
      ⨅ (φ : EuclideanSpace ℝ (Fin d) → ℝ) (_h : IsCapacityAdmissible K φ),
        sobolevTestEnergy p φ := rfl

/-- The compact capacity is at most the energy of each admissible test. -/
theorem compactSobolevCapacity_le {d : ℕ} (p : ℝ) {K : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : IsCapacityAdmissible K φ) :
    compactSobolevCapacity p K ≤ sobolevTestEnergy p φ :=
  iInf₂_le φ hφ

/-- Compact Sobolev capacity in the unbundled smooth-cutoff formulation. -/
theorem compactSobolevCapacity_eq_iInf {d : ℕ} (p : ℝ) (K : Set (EuclideanSpace ℝ (Fin d))) :
    compactSobolevCapacity p K = ⨅ (φ : EuclideanSpace ℝ (Fin d) → ℝ)
      (_hs : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) (_hc : HasCompactSupport φ)
      (_hK : ∃ U, IsOpen U ∧ K ⊆ U ∧ ∀ x ∈ U, 1 ≤ φ x), sobolevTestEnergy p φ := by
  simp only [compactSobolevCapacity, IsCapacityAdmissible, iInf_and]

/-- Outer Sobolev capacity, extended from compact sets through open sets. -/
@[expose]
def sobolevCapacity {d : ℕ} (p : ℝ) (A : Set (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ⨅ (U : Set (EuclideanSpace ℝ (Fin d))) (_hU : IsOpen U) (_hAU : A ⊆ U),
    ⨆ (K : Set (EuclideanSpace ℝ (Fin d))) (_hK : IsCompact K) (_hKU : K ⊆ U),
      compactSobolevCapacity p K

/-- Defining equation of `sobolevCapacity`. -/
theorem sobolevCapacity_def {d : ℕ} (p : ℝ) (A : Set (EuclideanSpace ℝ (Fin d))) :
    sobolevCapacity p A =
      ⨅ (U : Set (EuclideanSpace ℝ (Fin d))) (_hU : IsOpen U) (_hAU : A ⊆ U),
        ⨆ (K : Set (EuclideanSpace ℝ (Fin d))) (_hK : IsCompact K) (_hKU : K ⊆ U),
          compactSobolevCapacity p K := rfl

/-- The Sobolev capacity is monotone. -/
theorem sobolevCapacity_mono {d : ℕ} (p : ℝ) {A B : Set (EuclideanSpace ℝ (Fin d))}
    (hAB : A ⊆ B) : sobolevCapacity p A ≤ sobolevCapacity p B :=
  le_iInf₂ fun U hU ↦ le_iInf fun hBU ↦ iInf₂_le_of_le U hU (iInf_le_of_le (hAB.trans hBU) le_rfl)

/-- Quasicontinuity for Sobolev capacity, with an open exceptional set at every scale. -/
@[expose]
def IsSobolevQuasicontinuous {d : ℕ} (p : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ U, IsOpen U ∧ sobolevCapacity p U < ENNReal.ofReal ε ∧
    ContinuousOn f Uᶜ

/-- Unfolding quasicontinuity. -/
theorem isSobolevQuasicontinuous_iff {d : ℕ} {p : ℝ} {f : EuclideanSpace ℝ (Fin d) → ℝ} :
    IsSobolevQuasicontinuous p f ↔ ∀ ε : ℝ, 0 < ε → ∃ U, IsOpen U ∧
      sobolevCapacity p U < ENNReal.ofReal ε ∧ ContinuousOn f Uᶜ := Iff.rfl

/-- For `p ≠ 0` the empty set has zero compact capacity, tested by the zero function. -/
theorem compactSobolevCapacity_empty {d : ℕ} {p : ℝ} (hp : p ≠ 0) :
    compactSobolevCapacity p (∅ : Set (EuclideanSpace ℝ (Fin d))) = 0 := by
  refine le_antisymm ((compactSobolevCapacity_le p (φ := 0) ⟨contDiff_const,
    HasCompactSupport.zero, ∅, isOpen_empty, subset_rfl, by simp⟩).trans ?_) bot_le
  simp [sobolevTestEnergy, Real.zero_rpow hp]

/-- For `p ≠ 0` the empty set has zero Sobolev capacity. -/
theorem sobolevCapacity_empty {d : ℕ} {p : ℝ} (hp : p ≠ 0) :
    sobolevCapacity p (∅ : Set (EuclideanSpace ℝ (Fin d))) = 0 := by
  refine le_antisymm (iInf₂_le_of_le ∅ isOpen_empty (iInf_le_of_le subset_rfl ?_)) bot_le
  refine iSup₂_le fun K _ ↦ iSup_le fun hK ↦ ?_
  rw [Set.subset_empty_iff.mp hK, compactSobolevCapacity_empty hp]

/-- For `p ≠ 0` a continuous function is quasicontinuous, with empty exceptional set. -/
theorem isSobolevQuasicontinuous_of_continuous {d : ℕ} {p : ℝ} (hp : p ≠ 0)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f) : IsSobolevQuasicontinuous p f :=
  fun _ hε ↦ ⟨∅, isOpen_empty, by simpa [sobolevCapacity_empty hp] using hε, hf.continuousOn⟩

/-- **26.31**: every weak first-order Sobolev function has a quasicontinuous representative. -/
theorem exists_sobolevQuasicontinuous_representative {d : ℕ}
    {p : ℝ} (hp : 1 < p) {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemLp u (ENNReal.ofReal p) volume)
    {U : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    (hU : MemLp U (ENNReal.ofReal p) volume) (hw : TauCeti.HasWeakFDerivOn volume ⊤ u U) :
    ∃ v, v =ᵐ[volume] u ∧ IsSobolevQuasicontinuous p v := by
  sorry

/-- Such representatives are unique outside a capacity-zero set. -/
theorem sobolevQuasicontinuous_unique {d : ℕ} {p : ℝ} (hp : 1 < p)
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} (hu : IsSobolevQuasicontinuous p u)
    (hv : IsSobolevQuasicontinuous p v) (heq : u =ᵐ[volume] v) :
    sobolevCapacity p {x | u x ≠ v x} = 0 := by
  sorry

/-- Fractional Gagliardo `p`-energy, allowing infinite values. -/
@[expose]
def fractionalPEnergy {d : ℕ} (s p : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, ENNReal.ofReal (|u x - u y| ^ p) /
    ENNReal.ofReal (‖x - y‖ ^ ((d : ℝ) + s * p))

/-- Defining equation of `fractionalPEnergy`. -/
theorem fractionalPEnergy_def {d : ℕ} (s p : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ) :
    fractionalPEnergy s p u = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (|u x - u y| ^ p) /
      ENNReal.ofReal (‖x - y‖ ^ ((d : ℝ) + s * p)) := rfl

/-- The BBM constant written with a unit-ball moment rather than an ambiguously normalized
surface measure: radial integration gives `(d+p)/p` times this ball moment. -/
@[expose]
def bbmConstant {d : ℕ} (j : Fin d) (p : ℝ) : ℝ :=
  ((d : ℝ) + p) / p * ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1, |x j| ^ p

/-- Defining equation of `bbmConstant`. -/
theorem bbmConstant_def {d : ℕ} (j : Fin d) (p : ℝ) :
    bbmConstant j p =
      ((d : ℝ) + p) / p * ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1, |x j| ^ p := rfl

/-- **26.42**: the Bourgain–Brezis–Mironescu limit for real scalar weak Sobolev functions,
including `p=1`, with the exact Fourier-independent geometric normalization. -/
theorem tendsto_fractionalPEnergy_bbm {d : ℕ} (j : Fin d) {p : ℝ} (hp : 1 ≤ p)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : MemLp u (ENNReal.ofReal p) volume)
    {U : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    (hU : MemLp U (ENNReal.ofReal p) volume) (hw : TauCeti.HasWeakFDerivOn volume ⊤ u U) :
    Tendsto (fun s : ℝ ↦ ENNReal.ofReal (1 - s) * fractionalPEnergy s p u)
      (𝓝[<] 1) (𝓝 (ENNReal.ofReal (bbmConstant j p) *
        ∫⁻ x, ENNReal.ofReal (‖U x‖ ^ p))) := by
  sorry

end CKMA
