/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.PDE.Euclidean
public import CKMA.Analysis.Potential.Cutoff
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Sobolev capacity, quasicontinuity and the BBM limit

Inhomogeneous first-order Sobolev capacity and quasicontinuous representatives, unique
outside capacity-zero sets. Fractional Gagliardo p-energy converges to gradient energy
in the Bourgain–Brezis–Mironescu limit, including p=1. The exact constant is a unit-ball
moment with factor `(d+p)/p`. Weak derivatives reuse TauCeti; extended energies and
integration use Mathlib. Sources: GAPS 26.31 and 26.42.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Inhomogeneous first-order `p`-energy of a smooth real function. -/
def sobolevTestEnergy {d : ℕ} (p : ℝ) (φ : EuclideanRealSpace d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (|φ x| ^ p + ‖fderiv ℝ φ x‖ ^ p)

/-- Variational `C_{1,p}` capacity on compact sets, using smooth compactly supported tests. -/
def compactSobolevCapacity {d : ℕ} (p : ℝ) (K : Set (EuclideanRealSpace d)) : ℝ≥0∞ :=
  ⨅ (φ : EuclideanRealSpace d → ℝ) (_h : IsCapacityAdmissible K φ), sobolevTestEnergy p φ

/-- Compact Sobolev capacity in the unbundled smooth-cutoff formulation. -/
theorem compactSobolevCapacity_eq_iInf {d : ℕ} (p : ℝ) (K : Set (EuclideanRealSpace d)) :
    compactSobolevCapacity p K = ⨅ (φ : EuclideanRealSpace d → ℝ)
      (_hs : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) (_hc : HasCompactSupport φ)
      (_hK : ∃ U, IsOpen U ∧ K ⊆ U ∧ ∀ x ∈ U, 1 ≤ φ x), sobolevTestEnergy p φ := by
  simp only [compactSobolevCapacity, IsCapacityAdmissible, iInf_and]

/-- Outer Sobolev capacity, extended from compact sets through open sets. -/
def sobolevCapacity {d : ℕ} (p : ℝ) (A : Set (EuclideanRealSpace d)) : ℝ≥0∞ :=
  ⨅ (U : Set (EuclideanRealSpace d)) (_hU : IsOpen U) (_hAU : A ⊆ U),
    ⨆ (K : Set (EuclideanRealSpace d)) (_hK : IsCompact K) (_hKU : K ⊆ U),
      compactSobolevCapacity p K

/-- Quasicontinuity for Sobolev capacity, with an open exceptional set at every scale. -/
def IsSobolevQuasicontinuous {d : ℕ} (p : ℝ) (f : EuclideanRealSpace d → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ U, IsOpen U ∧ sobolevCapacity p U < ENNReal.ofReal ε ∧
    ContinuousOn f Uᶜ

/-- **26.31**: every weak first-order Sobolev function has a quasicontinuous representative. -/
theorem exists_sobolevQuasicontinuous_representative {d : ℕ} (hd : 0 < d)
    {p : ℝ} (hp : 1 < p) {u : EuclideanRealSpace d → ℝ}
    (hu : MemLp u (ENNReal.ofReal p) volume)
    {U : EuclideanRealSpace d → EuclideanRealSpace d →L[ℝ] ℝ}
    (hU : MemLp U (ENNReal.ofReal p) volume) (hw : TauCeti.HasWeakFDerivOn volume ⊤ u U) :
    ∃ v, v =ᵐ[volume] u ∧ IsSobolevQuasicontinuous p v := by
  sorry

/-- Such representatives are unique outside a capacity-zero set. -/
theorem sobolevQuasicontinuous_unique {d : ℕ} {p : ℝ} (hp : 1 < p)
    {u v : EuclideanRealSpace d → ℝ} (hu : IsSobolevQuasicontinuous p u)
    (hv : IsSobolevQuasicontinuous p v) (heq : u =ᵐ[volume] v) :
    sobolevCapacity p {x | u x ≠ v x} = 0 := by
  sorry

/-- Fractional Gagliardo `p`-energy, allowing infinite values. -/
def fractionalPEnergy {d : ℕ} (s p : ℝ) (u : EuclideanRealSpace d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, ENNReal.ofReal (|u x - u y| ^ p) /
    ENNReal.ofReal (‖x - y‖ ^ ((d : ℝ) + s * p))

/-- The BBM constant written with a unit-ball moment rather than an ambiguously normalized
surface measure: radial integration gives `(d+p)/p` times this ball moment. -/
def bbmConstant {d : ℕ} (j : Fin d) (p : ℝ) : ℝ :=
  ((d : ℝ) + p) / p * ∫ x in Metric.ball (0 : EuclideanRealSpace d) 1, |x j| ^ p

/-- **26.42**: the Bourgain–Brezis–Mironescu limit for real scalar weak Sobolev functions,
including `p=1`, with the exact Fourier-independent geometric normalization. -/
theorem tendsto_fractionalPEnergy_bbm {d : ℕ} (j : Fin d) {p : ℝ} (hp : 1 ≤ p)
    {u : EuclideanRealSpace d → ℝ} (hu : MemLp u (ENNReal.ofReal p) volume)
    {U : EuclideanRealSpace d → EuclideanRealSpace d →L[ℝ] ℝ}
    (hU : MemLp U (ENNReal.ofReal p) volume) (hw : TauCeti.HasWeakFDerivOn volume ⊤ u U) :
    Tendsto (fun s : ℝ ↦ ENNReal.ofReal (1 - s) * fractionalPEnergy s p u)
      (𝓝[<] 1) (𝓝 (ENNReal.ofReal (bbmConstant j p) *
        ∫⁻ x, ENNReal.ofReal (‖U x‖ ^ p))) := by
  sorry

end CKMA
