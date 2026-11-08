/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Algebra.Support

/-!
# Smooth cutoffs for variational capacities

Capacity-admissible functions are smooth compactly supported real functions at least one
on an open neighbourhood of the prescribed set. This common condition is used for both
homogeneous Newtonian and inhomogeneous Sobolev energies. Smoothness, topological support
and open neighbourhoods use Mathlib.
-/

@[expose] public section

namespace CKMA

/-- Smooth compactly supported cutoff functions at least one on a neighbourhood of `K`. -/
@[expose] def IsCapacityAdmissible {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d)))
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ContDiff ℝ (↑(⊤ : ℕ∞)) φ ∧ HasCompactSupport φ ∧
    ∃ U, IsOpen U ∧ K ⊆ U ∧ ∀ x ∈ U, 1 ≤ φ x

/-- Admissibility for a larger set implies admissibility for a smaller one. -/
theorem IsCapacityAdmissible.mono {d : ℕ} {K L : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : IsCapacityAdmissible L φ) (hKL : K ⊆ L) :
    IsCapacityAdmissible K φ := by
  obtain ⟨hd, hs, U, hU, hL, hval⟩ := hφ
  exact ⟨hd, hs, U, hU, hKL.trans hL, hval⟩

end CKMA
