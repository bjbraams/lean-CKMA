/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.Flow
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Dynamics.Flow
public import Mathlib.Dynamics.OmegaLimit
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Orbits of a continuously differentiable flow

A global flow with a `C¹` generator has unique integral curves, so an equilibrium is a fixed
point and a return `φ T y = y` with `T > 0` makes the orbit of `y` periodic. The omega-limit
set of a positively trapped orbit is nonempty, compact, invariant and preconnected, and the
omega-limit set of a periodic orbit is the orbit itself.

The standard plane is identified with `ℂ` by the coordinate equivalence `planeEquivComplex`,
so Jordan separation, which is stated for subsets of `ℂ`, applies to planar flows.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option linter.unusedSectionVars false

/-- Two integral curves of a `C¹` vector field that meet at one time coincide at every time. -/
theorem eq_of_hasDerivAt_generator {F : E → E} (hF : ContDiff ℝ 1 F) {α β : ℝ → E}
    (hα : ∀ t, HasDerivAt α (F (α t)) t) (hβ : ∀ t, HasDerivAt β (F (β t)) t)
    {t₀ : ℝ} (h₀ : α t₀ = β t₀) (t : ℝ) : α t = β t := by
  let s : Set ℝ := {t | α t = β t}
  have hαc : Continuous α := continuous_iff_continuousAt.mpr fun t ↦ (hα t).continuousAt
  have hβc : Continuous β := continuous_iff_continuousAt.mpr fun t ↦ (hβ t).continuousAt
  have hs : IsClopen s := by
    refine ⟨isClosed_eq hαc hβc, ?_⟩
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨K, u, hu, hLip⟩ := (hF.contDiffAt (x := α t)).exists_lipschitzOnWith
    have hαu : ∀ᶠ s in 𝓝 t, α s ∈ u := (hα t).continuousAt.eventually hu
    have hβu : ∀ᶠ s in 𝓝 t, β s ∈ u :=
      (hβ t).continuousAt.eventually (ht ▸ hu)
    have hα' : ∀ᶠ s in 𝓝 t, HasDerivAt α (F (α s)) s ∧ α s ∈ u :=
      (Eventually.of_forall hα).and hαu
    have hβ' : ∀ᶠ s in 𝓝 t, HasDerivAt β (F (β s)) s ∧ β s ∈ u :=
      (Eventually.of_forall hβ).and hβu
    exact ODE_solution_unique_of_eventually (v := fun _ ↦ F) (s := fun _ ↦ u)
      (Eventually.of_forall fun _ ↦ hLip) hα' hβ' ht
  have hne : s.Nonempty := ⟨t₀, h₀⟩
  have huniv : s = univ := hs.eq_univ hne
  have ht : t ∈ s := by
    rw [huniv]
    exact mem_univ t
  simpa [s] using ht

/-- An equilibrium of a `C¹` generator is a fixed point of the flow. -/
theorem eq_self_of_generator_eq_zero {φ : Flow ℝ E} {F : E → E} (hF : ContDiff ℝ 1 F)
    (hgen : FlowHasGenerator φ F) {y : E} (hy : F y = 0) (t : ℝ) : φ t y = y := by
  have hconst : ∀ s, HasDerivAt (fun _ : ℝ ↦ y) (F y) s := by
    intro s
    simpa [hy] using hasDerivAt_const s y
  exact eq_of_hasDerivAt_generator hF (hgen y) hconst (φ.map_zero_apply y) t

/-- A point fixed by the whole flow is an equilibrium of the generator. -/
theorem generator_eq_zero_of_forall_eq {φ : Flow ℝ E} {F : E → E}
    (hgen : FlowHasGenerator φ F) {y : E} (h : ∀ t, φ t y = y) : F y = 0 := by
  have hder := hgen y 0
  have hfun : (fun s ↦ φ s y) = fun _ ↦ y := funext h
  rw [hfun] at hder
  have hzero := (hasDerivAt_const (0 : ℝ) y).unique hder
  simpa [φ.map_zero_apply] using hzero.symm

/-- Shifting by one period does not move a returning point. -/
theorem flow_add_period {φ : Flow ℝ E} {y : E} {T : ℝ} (hT : φ T y = y) (t : ℝ) :
    φ (t + T) y = φ t y := by
  rw [φ.map_add, hT]

/-- Shifting by any number of periods does not move a returning point. -/
theorem flow_add_nat_period {φ : Flow ℝ E} {y : E} {T : ℝ} (hT : φ T y = y) (t : ℝ) (n : ℕ) :
    φ (t + n * T) y = φ t y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show t + ((n + 1 : ℕ) : ℝ) * T = t + (n : ℝ) * T + T by rw [Nat.cast_succ]; ring,
      flow_add_period hT, ih]

/-- A positive return time makes the real orbit the image of one period. -/
theorem range_eq_image_Icc_of_periodic {φ : Flow ℝ E} {y : E} {T : ℝ} (hT0 : 0 < T)
    (hT : φ T y = y) :
    Set.range (fun t : ℝ ↦ φ t y) = (fun t : ℝ ↦ φ t y) '' Icc 0 T := by
  refine subset_antisymm ?_ (image_subset_range _ _)
  intro z hz
  obtain ⟨t, rfl⟩ := hz
  let s : ℝ := T * Int.fract (t / T)
  have hs0 : 0 ≤ s := mul_nonneg hT0.le (Int.fract_nonneg _)
  have hs_lt : s < T := by
    simpa [s, mul_one] using mul_lt_mul_of_pos_left (Int.fract_lt_one (t / T)) hT0
  have hs_mem : s ∈ Icc 0 T := ⟨hs0, hs_lt.le⟩
  let n : ℤ := ⌊t / T⌋
  have hsign : t = s + (n : ℝ) * T := by
    have hfrac : (n : ℝ) + Int.fract (t / T) = t / T := Int.floor_add_fract (t / T)
    calc
      t = T * (t / T) := (mul_div_cancel₀ t hT0.ne').symm
      _ = T * ((n : ℝ) + Int.fract (t / T)) := congrArg (fun r : ℝ ↦ T * r) hfrac.symm
      _ = T * (n : ℝ) + s := by rw [mul_add]
      _ = s + (n : ℝ) * T := by rw [add_comm, mul_comm]
  by_cases hn : 0 ≤ n
  · have hcoe : (n.toNat : ℝ) = (n : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hn]
    refine ⟨s, hs_mem, ?_⟩
    have hnat : φ (s + (n : ℝ) * T) y = φ s y := by
      simpa [hcoe] using flow_add_nat_period hT s n.toNat
    simpa [hsign] using hnat.symm
  · have hnneg : n ≤ 0 := le_of_not_ge hn
    have hcoe : ((-n).toNat : ℝ) = -(n : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (neg_nonneg.mpr hnneg), Int.cast_neg]
    have hsum : t + ((-n).toNat : ℝ) * T = s := by
      rw [hcoe]
      linarith
    have hnat := flow_add_nat_period hT t (-n).toNat
    rw [hsum] at hnat
    exact ⟨s, hs_mem, hnat⟩

/-- The omega-limit set of a periodic orbit is the orbit. -/
theorem omegaLimit_eq_range_of_periodic {φ : Flow ℝ E} {y : E} {T : ℝ} (hT0 : 0 < T)
    (hT : φ T y = y) :
    omegaLimit atTop φ {y} = Set.range (fun t : ℝ ↦ φ t y) := by
  have hrange := range_eq_image_Icc_of_periodic (φ := φ) hT0 hT
  have hcompact : IsCompact (Set.range (fun t : ℝ ↦ φ t y)) := by
    rw [hrange]
    exact isCompact_Icc.image (continuous_id.flow φ continuous_const)
  have hclosed : IsClosed (Set.range (fun t : ℝ ↦ φ t y)) := hcompact.isClosed
  have htail (S : ℝ) : (fun t : ℝ ↦ φ t y) '' Ici S = Set.range (fun t : ℝ ↦ φ t y) := by
    refine subset_antisymm (image_subset_range _ _) ?_
    intro z hz
    obtain ⟨t, rfl⟩ := hz
    obtain ⟨n, hn⟩ := exists_nat_ge ((S - t) / T)
    have hge : S ≤ t + (n : ℝ) * T := by
      linarith [(div_le_iff₀ hT0).mp hn]
    refine ⟨t + n * T, hge, ?_⟩
    exact flow_add_nat_period hT t n
  apply subset_antisymm
  · intro z hz
    have hsub := omegaLimit_subset_closure_image2 atTop φ {y} (Ici_mem_atTop (0 : ℝ)) hz
    rw [show image2 φ (Ici (0 : ℝ)) {y} = (fun t : ℝ ↦ φ t y) '' Ici 0 by
      ext w
      simp [image2, mem_Ici]] at hsub
    rw [htail 0] at hsub
    exact hclosed.closure_eq ▸ hsub
  · intro z hz
    rw [mem_omegaLimit_iff_frequently₂]
    intro n hn
    rw [Filter.frequently_atTop]
    intro S
    have hz' : z ∈ (fun t : ℝ ↦ φ t y) '' Ici S := htail S ▸ hz
    obtain ⟨t, ht, rfl⟩ := hz'
    refine ⟨t, ht, ⟨φ t y, ⟨y, rfl, rfl⟩, mem_of_mem_nhds hn⟩⟩

/-- Transport of a flow along a continuous linear equivalence. -/
def conjFlow {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (φ : Flow ℝ E) : Flow ℝ F where
  toFun t z := e (φ t (e.symm z))
  cont' := e.continuous.comp
    (φ.cont'.comp (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))
  map_add' t₁ t₂ z := by simp [φ.map_add]
  map_zero' z := by simp

/-- The conjugated flow is generated by the conjugated vector field. -/
theorem conjFlow_hasGenerator {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {e : E ≃L[ℝ] F} {φ : Flow ℝ E} {G : E → E} (hgen : FlowHasGenerator φ G) :
    FlowHasGenerator (conjFlow e φ) (fun z ↦ e (G (e.symm z))) := by
  intro z t
  have hderiv :=
    (e.toContinuousLinearMap.hasFDerivAt (x := φ t (e.symm z))).comp_hasDerivAt t
      (hgen (e.symm z) t)
  simpa [conjFlow, Function.comp_def, e.symm_apply_apply] using hderiv

/-- Conjugation by a linear equivalence preserves continuous differentiability. -/
theorem contDiff_conjGenerator {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {e : E ≃L[ℝ] F} {G : E → E} (hG : ContDiff ℝ 1 G) :
    ContDiff ℝ 1 (fun z : F ↦ e (G (e.symm z))) := by
  have hright : ContDiff ℝ 1 (G ∘ ⇑e.symm) := (e.symm.contDiff_comp_iff).mpr hG
  have hleft : ContDiff ℝ 1 (⇑e ∘ G ∘ ⇑e.symm) := (e.comp_contDiff_iff).mpr hright
  simpa only [Function.comp_def] using hleft

/-- Omega-limit sets are transported by the conjugating equivalence. -/
theorem omegaLimit_conjFlow {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (φ : Flow ℝ E) (x : E) :
    omegaLimit atTop (conjFlow e φ) {e x} = e '' omegaLimit atTop φ {x} := by
  have hto : MapsTo e (omegaLimit atTop φ {x})
      (omegaLimit atTop (conjFlow e φ) {e x}) :=
    mapsTo_omegaLimit (f := atTop) (ϕ := φ) (s := {x}) (ϕ' := conjFlow e φ)
      (s' := {e x}) (ga := e) (by simp [MapsTo]) (gb := e)
      (fun t y ↦ by simp [conjFlow]) e.continuous
  have hfrom : MapsTo e.symm (omegaLimit atTop (conjFlow e φ) {e x})
      (omegaLimit atTop φ {x}) :=
    mapsTo_omegaLimit (f := atTop) (ϕ := conjFlow e φ) (s := {e x}) (ϕ' := φ)
      (s' := {x}) (ga := e.symm) (by simp [MapsTo]) (gb := e.symm)
      (fun t z ↦ by simp [conjFlow]) e.symm.continuous
  refine subset_antisymm ?_ ?_
  · intro z hz
    refine ⟨e.symm z, hfrom hz, ?_⟩
    simp
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact hto hy

/-- The coordinate equivalence of the standard plane with `ℂ`. -/
def planeEquivComplex : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℂ :=
  (EuclideanSpace.equiv (Fin 2) ℝ).trans
    ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).trans Complex.equivRealProdCLM.symm)

/-- A forward orbit trapped in a closed set has its omega-limit set in that set. -/
theorem omegaLimit_subset_of_forward {φ : Flow ℝ E} {x : E} {K : Set E}
    (hK : IsClosed K) (hstay : ∀ t : ℝ, 0 ≤ t → φ t x ∈ K) :
    omegaLimit atTop φ {x} ⊆ K := by
  intro y hy
  have htail : closure (image2 φ (Ici 0) {x}) ⊆ K := by
    refine closure_minimal ?_ hK
    intro z hz
    obtain ⟨t, ht, w, hw, rfl⟩ := mem_image2.mp hz
    obtain rfl : w = x := mem_singleton_iff.mp hw
    exact hstay t (mem_Ici.mp ht)
  exact htail (omegaLimit_subset_closure_image2 atTop φ {x} (Ici_mem_atTop 0) hy)

/-- A forward orbit trapped in a compact set has nonempty omega-limit set. -/
theorem nonempty_omegaLimit_of_forward {φ : Flow ℝ E} {x : E} {K : Set E}
    (hK : IsCompact K) (hstay : ∀ t : ℝ, 0 ≤ t → φ t x ∈ K) :
    (omegaLimit atTop φ {x}).Nonempty := by
  have htail : closure (image2 φ (Ici 0) {x}) ⊆ K := by
    refine closure_minimal ?_ hK.isClosed
    intro z hz
    obtain ⟨t, ht, w, hw, rfl⟩ := mem_image2.mp hz
    obtain rfl : w = x := mem_singleton_iff.mp hw
    exact hstay t (mem_Ici.mp ht)
  exact nonempty_omegaLimit_of_isCompact_absorbing atTop φ {x} hK
    ⟨Ici 0, Ici_mem_atTop 0, htail⟩ (singleton_nonempty x)

/-- A downward-directed intersection of compact preconnected sets is preconnected.
The two pieces of a separation of the intersection are disjoint compacts, so a Hausdorff space
puts them in disjoint open sets, and `exists_subset_nhds_of_isCompact` puts one member of the
family into that cover. This is the argument of `TauCeti.isPreconnected_iInter_of_directed`. -/
private theorem isPreconnected_iInter_of_directed {ι : Type*} [Nonempty ι] {t : ι → Set E}
    (htd : Directed (· ⊇ ·) t) (htc : ∀ i, IsCompact (t i))
    (htp : ∀ i, IsPreconnected (t i)) : IsPreconnected (⋂ i, t i) := by
  rintro u v hu hv hCuv ⟨a, haC, hau⟩ ⟨b, hbC, hbv⟩
  by_contra hcon
  have hCcl : IsClosed (⋂ i, t i) := isClosed_iInter fun i => (htc i).isClosed
  have hCco : IsCompact (⋂ i, t i) :=
    (htc (Nonempty.some inferInstance)).of_isClosed_subset hCcl (iInter_subset _ _)
  have hmem : ∀ x ∈ ⋂ i, t i, x ∈ u → x ∉ v := fun x hx hxu hxv => hcon ⟨x, hx, hxu, hxv⟩
  have haA : a ∈ (⋂ i, t i) \ v := ⟨haC, hmem a haC hau⟩
  have hbB : b ∈ (⋂ i, t i) \ u := ⟨hbC, fun hbu => hmem b hbC hbu hbv⟩
  have hdisj : Disjoint ((⋂ i, t i) \ v) ((⋂ i, t i) \ u) := by
    refine disjoint_left.mpr fun x hx hx' => ?_
    rcases hCuv hx.1 with hxu | hxv
    · exact hx'.2 hxu
    · exact hx.2 hxv
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hCco.diff hv) (hCco.diff hu) hdisj
  have hCUV : (⋂ i, t i) ⊆ U ∪ V := by
    intro x hx
    by_cases hxv : x ∈ v
    · exact Or.inr (hBV ⟨hx, fun hxu => hmem x hx hxu hxv⟩)
    · exact Or.inl (hAU ⟨hx, hxv⟩)
  obtain ⟨i, hi⟩ :=
    exists_subset_nhds_of_isCompact htd htc ((hU.union hV).mem_nhdsSet.mpr hCUV)
  obtain ⟨x, -, hxU, hxV⟩ :=
    htp i U V hU hV hi ⟨a, mem_iInter.mp haC i, hAU haA⟩ ⟨b, mem_iInter.mp hbC i, hBV hbB⟩
  exact disjoint_left.mp hUV hxU hxV

/-- Cluster points at `+∞` are the points in every tail closure. -/
private theorem setOf_mapClusterPt_atTop_eq_iInter (u : ℝ → E) (a : ℝ) :
    {x | MapClusterPt x atTop u} = ⋂ T : ↥(Ici a), closure (u '' Ici (T : ℝ)) := by
  ext x
  simp only [MapClusterPt, clusterPt_iff_forall_mem_closure, mem_iInter, mem_ofPred]
  constructor
  · intro h T
    exact h _ (image_mem_map (Ici_mem_atTop _))
  · intro h s hs
    obtain ⟨T, hT⟩ := mem_atTop_sets.mp (mem_map.mp hs)
    refine closure_mono ?_ (h ⟨max T a, mem_Ici.mpr (le_max_right T a)⟩)
    rintro _ ⟨t, ht, rfl⟩
    exact hT t ((le_max_left T a).trans ht)

/-- The omega-limit set of one forward orbit trapped in a compact set is preconnected. -/
theorem isPreconnected_omegaLimit_of_forward {φ : Flow ℝ E} {x : E} {K : Set E}
    (hK : IsCompact K) (hstay : ∀ t : ℝ, 0 ≤ t → φ t x ∈ K) :
    IsPreconnected (omegaLimit atTop φ {x}) := by
  let u : ℝ → E := fun t ↦ φ t x
  have hcont : ContinuousOn u (Ici 0) :=
    (continuous_id.flow φ continuous_const).continuousOn.mono (subset_univ _)
  have hmaps : MapsTo u (Ici 0) K := fun t ht ↦ hstay t (mem_Ici.mp ht)
  have hset : {y | MapClusterPt y atTop u} = omegaLimit atTop φ {x} := by
    ext y
    exact (mem_omegaLimit_singleton_iff_mapClusterPt (f := atTop) φ x y).symm
  rw [← hset, setOf_mapClusterPt_atTop_eq_iInter u 0]
  have : Nonempty ↥(Ici (0 : ℝ)) := ⟨⟨0, mem_Ici.mpr le_rfl⟩⟩
  refine isPreconnected_iInter_of_directed ?_ ?_ ?_
  · intro T₁ T₂
    refine ⟨⟨max (T₁ : ℝ) (T₂ : ℝ),
      mem_Ici.mpr (le_trans (mem_Ici.mp T₁.2) (le_max_left (T₁ : ℝ) (T₂ : ℝ)))⟩, ?_, ?_⟩
    · exact closure_mono (image_mono (Ici_subset_Ici.mpr (le_max_left _ _)))
    · exact closure_mono (image_mono (Ici_subset_Ici.mpr (le_max_right _ _)))
  · intro T
    refine hK.of_isClosed_subset isClosed_closure ?_
    refine closure_minimal ?_ hK.isClosed
    intro y hy
    obtain ⟨t, ht, rfl⟩ := hy
    exact hmaps (show t ∈ Ici 0 from (mem_Ici.mp T.2).trans ht)
  · intro T
    exact ((isPreconnected_Ici (a := (T : ℝ))).image u
      (hcont.mono (Ici_subset_Ici.mpr (mem_Ici.mp T.2)))).closure

/-- The omega-limit set of a real flow is invariant under every time shift. -/
theorem isInvariant_omegaLimit_atTop {φ : Flow ℝ E} (x : E) :
    IsInvariant φ (omegaLimit atTop φ {x}) :=
  Flow.isInvariant_omegaLimit atTop φ {x} fun t ↦
    tendsto_atTop_add_const_left atTop t tendsto_id

end CKMA
