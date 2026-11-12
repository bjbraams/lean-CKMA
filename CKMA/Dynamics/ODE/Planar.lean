/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.Flow
public import CKMA.Dynamics.ODE.Planar.Bendixson
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Dynamics.Flow
public import Mathlib.Dynamics.OmegaLimit

/-!
# Planar omega-limit sets (31.38)

`poincare_bendixson` identifies a compactly trapped planar orbit's omega-limit set with a
whole periodic orbit when that limit set contains no equilibrium. The generator is C¹
and is related to the existing global flow through `FlowHasGenerator`.

The plane is the real Euclidean space on `Fin 2`; all differential and omega-limit
conventions come from Mathlib and the common `CKMA.Dynamics.Flow` interface.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Set Topology

/-- **31.38**: a compact planar omega-limit set without equilibria is a periodic orbit.
The compact forward absorbing set supplies nonemptiness, and the conclusion identifies
all points of the omega-limit set, not just one periodic point. -/
theorem poincare_bendixson (φ : Flow ℝ (EuclideanSpace ℝ (Fin 2)))
    (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) (hF : ContDiff ℝ 1 F)
    (hgen : FlowHasGenerator φ F) (x : EuclideanSpace ℝ (Fin 2))
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : IsCompact K)
    (hstay : ∀ t : ℝ, 0 ≤ t → φ t x ∈ K)
    (hrest : ∀ y ∈ omegaLimit atTop φ {x}, F y ≠ 0) :
    ∃ y : EuclideanSpace ℝ (Fin 2), ∃ T : ℝ, 0 < T ∧ φ T y = y ∧
      omegaLimit atTop φ {x} = Set.range (fun t : ℝ ↦ φ t y) := by
  let e := planeEquivComplex
  let ψ : Flow ℝ ℂ := conjFlow e φ
  let G : ℂ → ℂ := fun z ↦ e (F (e.symm z))
  have hG : ContDiff ℝ 1 G := contDiff_conjGenerator hF
  have hgenψ : FlowHasGenerator ψ G := conjFlow_hasGenerator hgen
  have hKimg : IsCompact (e '' K) := hK.image e.continuous_toFun
  have hstay' : ∀ t : ℝ, 0 ≤ t → ψ t (e x) ∈ e '' K := by
    intro t ht
    have hpt : ψ t (e x) = e (φ t x) := by
      simp [ψ, conjFlow, e.symm_apply_apply]
    rw [hpt]
    exact mem_image_of_mem e (hstay t ht)
  have hrest' : ∀ z ∈ omegaLimit atTop ψ {e x}, G z ≠ 0 := by
    intro z hz hz0
    have hzimg : z ∈ e '' omegaLimit atTop φ {x} := by
      have hz' : z ∈ omegaLimit atTop (conjFlow e φ) {e x} := by
        simpa [ψ] using hz
      simpa [omegaLimit_conjFlow e φ x] using hz'
    obtain ⟨y0, hy0, rfl⟩ := hzimg
    have hzero : e (F y0) = 0 := by
      simpa [G, e.symm_apply_apply] using hz0
    exact hrest y0 hy0 ((e.toLinearEquiv.map_eq_zero_iff).mp hzero)
  obtain ⟨y, T, hT0, hper, hlim⟩ :=
    poincare_bendixson_complex ψ G hG hgenψ (e x) (e '' K) hKimg hstay' hrest'
  refine ⟨e.symm y, T, hT0, ?_, ?_⟩
  · have hback : e (φ T (e.symm y)) = y := by
      simpa [ψ, conjFlow] using hper
    simpa [e.symm_apply_apply] using congrArg e.symm hback
  · have horb : e '' range (fun t : ℝ ↦ φ t (e.symm y)) =
        range (fun t : ℝ ↦ ψ t y) := by
      ext z
      constructor
      · intro hz
        rw [mem_image] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        obtain ⟨t, rfl⟩ := hw
        exact ⟨t, by simp [ψ, conjFlow]⟩
      · rintro ⟨t, rfl⟩
        change ψ t y ∈ e '' range (fun s : ℝ ↦ φ s (e.symm y))
        have hpt : ψ t y = e (φ t (e.symm y)) := by simp [ψ, conjFlow]
        rw [hpt]
        exact mem_image_of_mem e ⟨t, rfl⟩
    apply e.injective.image_injective
    calc
      e '' omegaLimit atTop φ {x} = omegaLimit atTop ψ {e x} := by
        simpa [ψ] using (omegaLimit_conjFlow e φ x).symm
      _ = range (fun t : ℝ ↦ ψ t y) := hlim
      _ = e '' range (fun t : ℝ ↦ φ t (e.symm y)) := horb.symm

end CKMA
