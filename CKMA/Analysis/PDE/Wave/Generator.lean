/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import TauCeti.Analysis.Semigroups.CauchyProblem.Inhomogeneous
import TauCeti.Analysis.Semigroups.Dissipative.Hilbert
import TauCeti.Analysis.Semigroups.Generation.BoundedPerturbation

/-!
# The skew wave generator on a Hilbert product

For an injective map `J : V →L[ℝ] H` with dense range between real Hilbert spaces, the block
operator `(x, y) ↦ (J⁻¹ y, -J* x)` on the Hilbert product `V × H` (`WithLp 2 (V × H)`) is
m-dissipative. Its range condition is Mathlib's Lax–Milgram theorem for the coercive resolvent
`1 + J* J`. TauCeti's Lumer–Phillips generation, bounded perturbation and Duhamel theorems then
give mild trajectories of the forced system. With `J` the value map `H¹ → L²` this is the
abstract existence step for finite-energy waves.

## Main results

* `CKMA.exists_wavePhaseTrajectory`: continuous trajectories of the forced skew wave system
  satisfying its two integrated component equations.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory TauCeti Filter Metric Set TopologicalSpace
open scoped InnerProductSpace
open TauCeti.Semigroups

section WaveSkew

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The wave phase space uses the Hilbert product of position and velocity. -/
private abbrev WavePhase (V H : Type*) := WithLp 2 (V × H)

variable (J : V →L[ℝ] H)

/-- The graph of the skew wave block for the inhomogeneous Sobolev inner product. -/
private def waveSkewGraph : Submodule ℝ (WavePhase V H × WavePhase V H) where
  carrier := {p | J p.2.fst = p.1.snd ∧
    ∀ z : V, ⟪p.2.snd, J z⟫_ℝ = -⟪p.1.fst, z⟫_ℝ}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    obtain ⟨hp₁, hp₂⟩ := hp
    obtain ⟨hq₁, hq₂⟩ := hq
    refine ⟨?_, fun z => ?_⟩
    · simp only [Prod.fst_add, Prod.snd_add, WithLp.add_fst, WithLp.add_snd, map_add, hp₁, hq₁]
    · simp only [Prod.fst_add, Prod.snd_add, WithLp.add_fst, WithLp.add_snd, inner_add_left,
        hp₂ z, hq₂ z, neg_add]
  smul_mem' := by
    intro a p hp
    obtain ⟨hp₁, hp₂⟩ := hp
    refine ⟨?_, fun z => ?_⟩
    · simp only [Prod.smul_fst, Prod.smul_snd, WithLp.smul_fst, WithLp.smul_snd, map_smul, hp₁]
    · simp only [Prod.smul_fst, Prod.smul_snd, WithLp.smul_fst, WithLp.smul_snd,
        real_inner_smul_left, hp₂ z, mul_neg]

/-- The skew wave block on the product of the inhomogeneous Sobolev space and L². -/
private def waveSkew : WavePhase V H →ₗ.[ℝ] WavePhase V H :=
  (waveSkewGraph J).toLinearPMap

omit [CompleteSpace V] [CompleteSpace H] in
/-- The two component equations characterize membership in the skew wave graph. -/
private theorem mem_waveSkew_graph_iff (hJ : Function.Injective J) (hdense : DenseRange J)
    {x y : WavePhase V H} :
    (x, y) ∈ (waveSkew J).graph ↔ J y.fst = x.snd ∧
      ∀ z : V, ⟪y.snd, J z⟫_ℝ = -⟪x.fst, z⟫_ℝ := by
  rw [waveSkew, Submodule.toLinearPMap_graph_eq]
  · rfl
  · rintro ⟨x, y⟩ ⟨hy₁, hy₂⟩ rfl
    have hy₁' : y.fst = 0 := hJ (by simpa only [map_zero, WithLp.zero_snd] using hy₁)
    have hy₂' : y.snd = 0 := hdense.eq_zero_of_inner_left ℝ (by
      simpa only [WithLp.zero_fst, inner_zero_left, neg_zero] using hy₂)
    exact (WithLp.equiv 2 _).injective (Prod.ext hy₁' hy₂')

omit [CompleteSpace V] [CompleteSpace H] in
/-- The skew wave generator has vanishing real quadratic form. -/
private theorem inner_waveSkew_self (hJ : Function.Injective J) (hdense : DenseRange J)
    (x : (waveSkew J).domain) :
    ⟪waveSkew J x, (x : WavePhase V H)⟫_ℝ = 0 := by
  obtain ⟨hx, hy⟩ := (mem_waveSkew_graph_iff J hJ hdense).1 ((waveSkew J).mem_graph x)
  have hpair := hy ((waveSkew J x).fst)
  rw [hx, real_inner_comm (waveSkew J x).fst] at hpair
  simp only [WithLp.fst, WithLp.snd] at hpair
  simp only [WithLp.prod_inner_apply, hpair, add_neg_cancel]

/-- The coercive operator for the unit resolvent of the skew wave block. -/
private def waveResolventOp : V →L[ℝ] V :=
  1 + J.adjoint.comp J

/-- The resolvent operator is coercive by positivity of the L² value pairing. -/
private theorem waveResolventOp_coercive :
    IsCoercive ((innerSL ℝ).comp (waveResolventOp J)) := by
  refine ⟨1, zero_lt_one, fun z => ?_⟩
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, waveResolventOp,
    add_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply,
    inner_add_left, ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg ‖J z‖]

/-- Lax–Milgram gives the unit resolvent of the skew wave block. -/
private theorem waveSkew_surjective (hJ : Function.Injective J) (hdense : DenseRange J) :
    Function.Surjective fun x : (waveSkew J).domain => (x : WavePhase V H) - waveSkew J x := by
  intro y
  let w := (waveResolventOp_coercive J).continuousLinearEquivOfBilin.symm
    (J.adjoint y.snd - y.fst)
  have hw (z : V) :
      ⟪J w - y.snd, J z⟫_ℝ = -⟪y.fst + w, z⟫_ℝ := by
    have heq := (waveResolventOp_coercive J).continuousLinearEquivOfBilin_apply w z
    have hE : (waveResolventOp_coercive J).continuousLinearEquivOfBilin w =
        J.adjoint y.snd - y.fst :=
      (waveResolventOp_coercive J).continuousLinearEquivOfBilin.apply_symm_apply _
    rw [hE, ContinuousLinearMap.comp_apply, innerSL_apply_apply, waveResolventOp,
      add_apply, one_apply_eq_self, ContinuousLinearMap.comp_apply,
      inner_add_left, inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_left] at heq
    rw [inner_sub_left, inner_add_left]
    linarith
  let x : WavePhase V H := WithLp.toLp 2 (y.fst + w, J w)
  let z : WavePhase V H := WithLp.toLp 2 (w, J w - y.snd)
  have hg : (x, z) ∈ (waveSkew J).graph := (mem_waveSkew_graph_iff J hJ hdense).mpr ⟨rfl, hw⟩
  obtain ⟨u, hu₁, hu₂⟩ := (LinearPMap.mem_graph_iff _).mp hg
  refine ⟨u, ?_⟩
  dsimp only
  rw [hu₁, hu₂]
  apply (WithLp.equiv 2 _).injective
  exact Prod.ext (by simp [x, z]) (by simp [x, z])

/-- The skew wave block has dense domain by its vanishing quadratic form and unit resolvent. -/
private theorem waveSkew_dense (hJ : Function.Injective J) (hdense : DenseRange J) :
    Dense ((waveSkew J).domain : Set (WavePhase V H)) := by
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
    ← Submodule.orthogonal_orthogonal_eq_closure]
  suffices ((waveSkew J).domain)ᗮ = ⊥ by
    rw [this, Submodule.bot_orthogonal_eq_top, Submodule.top_coe]
  refine le_antisymm (fun y hy => ?_) bot_le
  obtain ⟨x, hx⟩ := waveSkew_surjective J hJ hdense y
  have hinner := Submodule.inner_right_of_mem_orthogonal x.property hy
  have horth := inner_waveSkew_self J hJ hdense x
  rw [real_inner_comm] at horth
  rw [← hx, inner_sub_right, horth, sub_zero, inner_self_eq_zero] at hinner
  have hx0 : x = 0 := Subtype.ext hinner
  exact (Submodule.mem_bot ℝ).mpr (by simpa [hx0] using hx.symm)

/-- Positive multiples of the skew wave block are maximally dissipative. -/
private theorem waveSkew_isMDissipative (hJ : Function.Injective J) (hdense : DenseRange J)
    {c : ℝ} (hc : 0 < c) :
    IsMDissipative (c • waveSkew J) := by
  have hdis : IsDissipative (waveSkew J) := (isDissipative_iff_real_inner_nonpos _).2
    fun x => (inner_waveSkew_self J hJ hdense x).le
  apply (hdis.smul hc.le).isMDissipative hc
  intro y
  obtain ⟨x, hx⟩ := waveSkew_surjective J hJ hdense (c⁻¹ • y)
  refine ⟨x, ?_⟩
  have he : c • ((x : WavePhase V H) - waveSkew J x) = y :=
    (congrArg (c • ·) hx).trans (smul_inv_smul₀ hc.ne' _)
  simpa only [smul_sub, LinearPMap.smul_apply] using he

/-- The velocity inclusion in the Hilbert product. -/
private def wavePhaseInr : H →L[ℝ] WavePhase V H :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ V H).symm.toContinuousLinearMap.comp
    (LinearIsometry.inr ℝ V H).toContinuousLinearMap

omit [CompleteSpace V] [CompleteSpace H] in
/-- The velocity inclusion has zero position and the given velocity. -/
private theorem wavePhaseInr_apply (v : H) :
    (wavePhaseInr : H →L[ℝ] WavePhase V H) v = WithLp.toLp 2 (0, v) := rfl

/-- The mass correction cancels the value term in the inhomogeneous Sobolev inner product. -/
private def waveMassCorrection (c : ℝ) : WavePhase V H →L[ℝ] WavePhase V H :=
  c • (wavePhaseInr.comp (J.comp (WithLp.fstL 2 ℝ V H)))

/-- Let `J : V →L[ℝ] H` be an injective map with dense range between real Hilbert spaces and
`0 < c`. For integrable forcing `f : ℝ → H` and initial point `x₀` of the Hilbert product
`V × H`, there is a continuous trajectory `Q` with `Q 0 = x₀` satisfying, for `t ≥ 0`, the two
integrated equations of the wave system `J q̇₁ = c q₂`, `q̇₂ = f - c J* (J q₁) + c q₁`, the
second tested against every `J w`. -/
theorem exists_wavePhaseTrajectory (hJ : Function.Injective J) (hdense : DenseRange J)
    {c : ℝ} (hc : 0 < c) (x₀ : WithLp 2 (V × H)) {f : ℝ → H} (hf : Integrable f) :
    ∃ Q : C(ℝ, WithLp 2 (V × H)), Q 0 = x₀ ∧
      ∀ t : ℝ, 0 ≤ t →
        J (Q t).fst = J x₀.fst + c • (∫ s in Ioc 0 t, (Q s).snd) ∧
        ∀ w : V,
          ⟪(Q t).snd, J w⟫_ℝ = ⟪x₀.snd, J w⟫_ℝ + ⟪∫ s in Ioc 0 t, f s, J w⟫_ℝ +
            c * (⟪J (∫ s in Ioc 0 t, (Q s).fst), J w⟫_ℝ -
              ⟪∫ s in Ioc 0 t, (Q s).fst, w⟫_ℝ) := by
  let B := waveMassCorrection J c
  have hD : Dense ((c • waveSkew J).domain : Set (WavePhase V H)) := by
    rw [LinearPMap.smul_domain]
    exact waveSkew_dense J hJ hdense
  obtain ⟨S, hgen, _⟩ :=
    (waveSkew_isMDissipative J hJ hdense hc).exists_stronglyContinuousSemigroup_generator_eq_vadd
      hD B
  let L : H →L[ℝ] WavePhase V H := wavePhaseInr
  let F : ℝ → WavePhase V H := fun t => L (f t)
  have hF : Integrable F := L.integrable_comp hf
  let q : ℝ → WavePhase V H := fun t => S.realOperator t x₀ + S.duhamel F t
  have hq := S.isForcedMildSolution_realOperator_add_duhamel
    hF.integrableOn.locallyIntegrableOn x₀
  let Q : C(ℝ, WavePhase V H) :=
    ⟨fun t => q (max 0 t), hq.continuousOn.comp_continuous
      (continuous_const.max continuous_id) (fun t => Set.mem_Ici.2 (le_max_left (0 : ℝ) t))⟩
  have hQ : IsForcedMildSolution S.generator F x₀ Q :=
    hq.congr fun t ht => congrArg q (max_eq_right ht).symm
  rw [hgen] at hQ
  refine ⟨Q, hQ.apply_zero, fun t ht => ?_⟩
  let z : (waveSkew J).domain := ⟨_, hQ.integral_mem_domain ht⟩
  have hz : B (z : WavePhase V H) + c • waveSkew J z =
      Q t - x₀ - ∫ s in Ioc 0 t, F s := hQ.map_integral_eq_sub ht
  obtain ⟨hpos, hvel⟩ := (mem_waveSkew_graph_iff J hJ hdense).1 ((waveSkew J).mem_graph z)
  have hint : IntegrableOn Q (Ioc 0 t) := (Q.continuous.intervalIntegrable 0 t).1
  have hfst : (z : WavePhase V H).fst = ∫ s in Ioc 0 t, (Q s).fst :=
    ((WithLp.fstL 2 ℝ V H).integral_comp_comm hint).symm
  have hsnd : (z : WavePhase V H).snd = ∫ s in Ioc 0 t, (Q s).snd :=
    ((WithLp.sndL 2 ℝ V H).integral_comp_comm hint).symm
  have hFint : (∫ s in Ioc 0 t, F s) = WithLp.toLp 2 (0, ∫ s in Ioc 0 t, f s) := by
    exact (L.integral_comp_comm hf.integrableOn).trans (wavePhaseInr_apply _)
  have hB : B z = WithLp.toLp 2 (0, c • J (z : WavePhase V H).fst) := by
    dsimp only [B]
    rw [waveMassCorrection, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, WithLp.fstL_apply, wavePhaseInr_apply]
    exact (WithLp.equiv 2 _).injective (Prod.ext (smul_zero c) rfl)
  constructor
  · have h := congrArg (fun a : WavePhase V H => J a.fst) hz
    simp only [hB, hFint, WithLp.add_fst, WithLp.sub_fst, WithLp.smul_fst, WithLp.toLp_fst,
      zero_add, sub_zero, map_smul, map_sub, hpos, hsnd] at h
    exact (sub_eq_iff_eq_add.mp h.symm).trans (add_comm _ _)
  · intro w
    have h := congrArg (fun a : WavePhase V H => ⟪a.snd, J w⟫_ℝ) hz
    simp only [hB, hFint, WithLp.add_snd, WithLp.sub_snd, WithLp.smul_snd, WithLp.toLp_snd,
      inner_add_left, inner_sub_left, real_inner_smul_left, hvel, hfst] at h
    linarith

end WaveSkew

end CKMA
