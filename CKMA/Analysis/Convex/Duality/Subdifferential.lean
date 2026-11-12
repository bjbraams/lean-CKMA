/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Order.Basic
public import TauCeti.Analysis.Convex.FenchelMoreau

/-!
# Subgradients from a nonempty epigraph interior

A convex extended-real function that is finite at a point and bounded above nearby has a
subgradient there. The graph point is separated from the interior of the real epigraph in
`E × ℝ`; the resulting hyperplane is non-vertical because a point strictly above the graph
lies in that interior.

The argument is the Hahn–Banach step of the continuity-qualified Fenchel–Rockafellar theorem
and of the Banach subdifferential sum rule. Sources: Borwein–Lewis, *Convex Analysis and
Nonlinear Optimization*, Theorem 4.1.6; GAPS 12.21 and 12.39.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped Pointwise Topology
open Set ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E]

/-- A function continuous and finite at a point is bounded above on a neighborhood. -/
theorem exists_boundedAbove_of_continuousAt {f : E → EReal} {x : E}
    (hcont : ContinuousAt f x) (htop : f x ≠ ⊤) (hbot : f x ≠ ⊥) :
    ∃ U ∈ 𝓝 x, ∃ M : ℝ, ∀ y ∈ U, f y ≤ (M : EReal) := by
  set r : ℝ := (f x).toReal
  have hr : f x = (r : EReal) := (EReal.coe_toReal htop hbot).symm
  have hnhds : Iio ((r + 1 : ℝ) : EReal) ∈ 𝓝 (f x) := by
    rw [hr]
    exact Iio_mem_nhds (EReal.coe_lt_coe_iff.mpr (lt_add_one r))
  obtain ⟨U, hU, hUle⟩ := (hcont.eventually hnhds).exists_mem
  exact ⟨U, hU, r + 1, fun y hy => (hUle y hy).le⟩

variable [NormedSpace ℝ E]

/-- A convex function, finite at `x` and bounded above on a neighborhood of `x`, has a
subgradient at `x` for the continuous-dual pairing. -/
theorem exists_mem_subdifferential_of_boundedAbove {f : E → EReal}
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) {x : E}
    (hx : f x ≠ ⊤) (hbd : ∃ U ∈ 𝓝 x, ∃ M : ℝ, ∀ y ∈ U, f y ≤ (M : EReal)) :
    ∃ u : StrongDual ℝ E,
      u ∈ TauCeti.subdifferential (topDualPairing ℝ E).flip f x := by
  obtain ⟨U₀, hU₀, M, hM⟩ := hbd
  obtain ⟨U, ⟨hxU, hUopen⟩, hUU⟩ := (nhds_basis_opens x).mem_iff.mp hU₀
  have hU : ∀ y ∈ U, f y ≤ (M : EReal) := fun y hy => hM y (hUU hy)
  set epi : Set (E × ℝ) := {p : E × ℝ | f p.1 ≤ p.2}
  set c : ℝ := (f x).toReal
  have hfc : f x = (c : EReal) := (EReal.coe_toReal hx (hbot x)).symm
  have hcM : c ≤ M := by
    have hxle : f x ≤ (M : EReal) := hU x hxU
    rw [hfc, EReal.coe_le_coe_iff] at hxle
    exact hxle
  have hbox : U ×ˢ Ioi M ⊆ epi := by
    intro p hp
    exact (hU p.1 hp.1).trans (EReal.coe_le_coe_iff.mpr hp.2.le)
  have hopen : IsOpen (U ×ˢ Ioi M) := IsOpen.prod hUopen isOpen_Ioi
  have hsubint : U ×ˢ Ioi M ⊆ interior epi := interior_maximal hbox hopen
  have hint : (x, M + 1) ∈ interior epi :=
    hsubint ⟨hxU, lt_add_of_pos_right M one_pos⟩
  have hnot : (x, c) ∉ interior epi := by
    intro hmem
    obtain ⟨u, hu, v, hv, hsub⟩ :=
      mem_nhds_prod_iff.mp (mem_interior_iff_mem_nhds.mp hmem)
    obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hIoo⟩ := (nhds_basis_Ioo c).mem_iff.mp hv
    have hmid : (a + c) / 2 ∈ Ioo a b := by
      constructor <;> linarith
    have hpt : (x, (a + c) / 2) ∈ epi :=
      hsub ⟨mem_of_mem_nhds hu, hIoo hmid⟩
    have hlt : f x ≤ ((a + c) / 2 : ℝ) := hpt
    rw [hfc, EReal.coe_le_coe_iff] at hlt
    linarith
  have hintne : (interior epi).Nonempty := ⟨(x, M + 1), hint⟩
  obtain ⟨sep, hsep⟩ :=
    geometric_hahn_banach_open_point hf.interior isOpen_interior hnot
  have hle (p : E × ℝ) (hp : p ∈ epi) : sep p ≤ sep (x, c) := by
    have hcl := hf.closure_interior_eq_closure_of_nonempty_interior hintne
    have hpcl : p ∈ closure (interior epi) := by
      rw [hcl]
      exact subset_closure hp
    have hclosed : IsClosed {q : E × ℝ | sep q ≤ sep (x, c)} :=
      isClosed_le sep.continuous continuous_const
    exact closure_minimal (fun q hq => (hsep q hq).le) hclosed hpcl
  let lin : E →L[ℝ] ℝ := sep.comp (inl ℝ E ℝ)
  let slope : ℝ := sep (0, 1)
  have hdecomp (y : E) (r : ℝ) : sep (y, r) = lin y + r * slope := by
    have hinr : (sep.comp (inr ℝ E ℝ)) r = r * slope := by
      have hsmul := (sep.comp (inr ℝ E ℝ)).map_smul r (1 : ℝ)
      simpa [slope, inr_apply, smul_eq_mul] using hsmul
    have hsum := comp_inl_add_comp_inr sep (y, r)
    simpa [lin, hinr] using hsum.symm
  have hslope : slope < 0 := by
    have hstrict := hsep _ hint
    rw [hdecomp x (M + 1), hdecomp x c] at hstrict
    have hmul : (M + 1 - c) * slope < 0 := by linarith
    have hpos : 0 < M + 1 - c := by linarith [hcM]
    have hdiv : slope = ((M + 1 - c) * slope) / (M + 1 - c) := by
      field_simp
    rw [hdiv]
    exact div_neg_of_neg_of_pos hmul hpos
  have hineq (y : E) (r : ℝ) (hr : f y ≤ (r : ℝ)) :
      lin y - lin x ≤ (-slope) * (r - c) := by
    have hsep' : lin y + r * slope ≤ lin x + c * slope := by
      rw [← hdecomp, ← hdecomp]
      exact hle (y, r) hr
    linarith
  refine ⟨(-slope)⁻¹ • lin, ?_⟩
  rw [TauCeti.mem_subdifferential_iff_forall_toReal_add_le
    (topDualPairing ℝ E).flip hbot hx]
  intro y hy
  have hsub := hineq y (f y).toReal (EReal.le_coe_toReal hy)
  have hpos : 0 < -slope := neg_pos.mpr hslope
  have hscale :
      (-slope)⁻¹ * (lin y - lin x) ≤ (f y).toReal - c := by
    calc
      (-slope)⁻¹ * (lin y - lin x)
          ≤ (-slope)⁻¹ * ((-slope) * ((f y).toReal - c)) :=
            mul_le_mul_of_nonneg_left hsub (inv_pos.mpr hpos).le
      _ = (f y).toReal - c := by
            rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  have happ :
      ((-slope)⁻¹ • lin) (y - x) = (-slope)⁻¹ * (lin y - lin x) := by
    rw [smul_apply, map_sub]
    ring
  simp only [LinearMap.flip_apply, topDualPairing_apply, happ]
  linarith

/-- Every point of a finite-dimensional real convex function has a subgradient. -/
theorem exists_mem_subdifferential_of_convexOn [FiniteDimensional ℝ E] {f : E → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (x : E) :
    ∃ u : StrongDual ℝ E,
      u ∈ TauCeti.subdifferential (topDualPairing ℝ E).flip
        (fun y : E => (f y : EReal)) x := by
  have hcont : Continuous f :=
    continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  have hE : Continuous fun y : E => (f y : EReal) :=
    continuous_coe_real_ereal.comp hcont
  have hconv : Convex ℝ {p : E × ℝ | (f p.1 : EReal) ≤ p.2} := by
    have hset :
        {p : E × ℝ | (f p.1 : EReal) ≤ p.2} = {p : E × ℝ | f p.1 ≤ p.2} := by
      ext p
      simp [EReal.coe_le_coe_iff]
    have hepi := hf.convex_epigraph
    rw [hset]
    simpa using hepi
  have hbot : ∀ y : E, (f y : EReal) ≠ ⊥ := fun _ => EReal.coe_ne_bot _
  obtain ⟨U, hU, M, hM⟩ :=
    exists_boundedAbove_of_continuousAt hE.continuousAt (EReal.coe_ne_top _) (hbot x)
  exact exists_mem_subdifferential_of_boundedAbove hconv hbot (EReal.coe_ne_top _)
    ⟨U, hU, M, hM⟩

end CKMA
