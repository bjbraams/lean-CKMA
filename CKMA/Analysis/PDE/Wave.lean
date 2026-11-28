/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.PDE.Wave.Basic

import CKMA.Analysis.PDE.Wave.Generator
import TauCeti.Analysis.Sobolev.W1p.ClosedOperator
import TauCeti.Analysis.Sobolev.W1p.Density

/-!
# Finite-energy waves: existence, uniqueness and finite propagation

Forced waves with position in TauCeti's first-order Sobolev space and velocity in L², as defined
in `CKMA.Analysis.PDE.Wave.Basic`. Existence applies the skew wave generator of
`CKMA.Analysis.PDE.Wave.Generator` to the value map `H¹ → L²`, which is injective with dense
range; uniqueness is `CKMA.IsWaveEnergySolution.unique`. Initial and forcing data agreeing on a
backward cone give spatial almost-everywhere agreement in its later balls.
Sources: GAPS 32.50 and 32.52.

## Main results

* `CKMA.existsUnique_waveEnergySolution` (**32.50**): existence and uniqueness of finite-energy
  wave solutions on a compact time interval.
* `CKMA.wave_finitePropagation` (**32.52**): finite speed of propagation on backward light cones.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory TauCeti Filter Metric Set TopologicalSpace
open scoped InnerProductSpace Interval Distributions

/-- The Sobolev value map is injective and has dense range in the velocity space. -/
private theorem wave_valueL_injective_dense (d : ℕ) :
    Function.Injective (W1p.valueL : WavePositionSpace d →L[ℝ] WaveVelocitySpace d) ∧
      DenseRange (W1p.valueL : WavePositionSpace d →L[ℝ] WaveVelocitySpace d) := by
  refine ⟨fun _ _ h => W1p.ext_value (by simpa only [W1p.valueL_apply] using h), ?_⟩
  have h := dense_domain_weakGradientPMap (mu := (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (Omega := ⊤)
  refine h.mono ?_
  intro f hf
  obtain ⟨u, hu⟩ := mem_domain_weakGradientPMap_iff.mp hf
  exact ⟨u, (W1p.valueL_apply u).trans hu⟩

/-- The Sobolev inner product splits into the value and gradient pairings. -/
private theorem wave_inner_position {d : ℕ} (u w : WavePositionSpace d) :
    ⟪u, w⟫_ℝ = ⟪W1p.valueL u, W1p.valueL w⟫_ℝ + ⟪W1p.gradientL u, W1p.gradientL w⟫_ℝ := by
  simp only [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
    ← sq, W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq, W1p.valueL_apply,
    W1p.gradientL_apply, W1p.value_sub, W1p.gradient_sub]
  ring

set_option maxHeartbeats 1400000 in
/-- Integrable forcing produces an energy solution via the perturbed skew wave semigroup. -/
private theorem exists_waveEnergySolution {d : ℕ} {c T : ℝ} (hc : 0 < c) (hT : 0 < T)
    (u₀ : WavePositionSpace d) (v₀ : WaveVelocitySpace d) {f : ℝ → WaveVelocitySpace d}
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) T)) :
    ∃ uv, IsWaveEnergySolution c T u₀ v₀ f uv := by
  let F := (Icc (0 : ℝ) T).indicator f
  have hF : Integrable F := (integrable_indicator_iff measurableSet_Icc).2 hf
  let J : WavePositionSpace d →L[ℝ] WaveVelocitySpace d := W1p.valueL
  obtain ⟨hJ, hJdense⟩ := wave_valueL_injective_dense d
  obtain ⟨Q, hQ0, hQ⟩ := exists_wavePhaseTrajectory J hJ hJdense hc
    (WithLp.toLp 2 (c • u₀, v₀)) hF
  let u : ℝ → WavePositionSpace d := fun s => c⁻¹ • (Q s).fst
  let v : ℝ → WaveVelocitySpace d := fun s => (Q s).snd
  have hq₁ : Continuous (fun s : ℝ => (Q s).fst) :=
    (WithLp.continuous_fst 2 _ _).comp Q.continuous
  have hucont : Continuous u := hq₁.const_smul c⁻¹
  have hvcont : Continuous v := (WithLp.continuous_snd 2 _ _).comp Q.continuous
  let up : C(Icc (0 : ℝ) T, WavePositionSpace d) :=
    ⟨fun t => u t.1, hucont.comp continuous_subtype_val⟩
  let vp : C(Icc (0 : ℝ) T, WaveVelocitySpace d) :=
    ⟨fun t => v t.1, hvcont.comp continuous_subtype_val⟩
  refine ⟨(up, vp), ?_, ?_, ?_⟩
  · intro t ht
    simp only [up, vp, ContinuousMap.coe_mk, u, v, ht, hQ0, WithLp.toLp_fst, WithLp.toLp_snd,
      inv_smul_smul₀ hc.ne', and_self]
  · intro t ht
    have hD := ((hvcont.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add (W1p.value u₀))
    refine hD.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
    rw [intervalCurveExtend_of_mem _ hsT]
    have h₁ : J (Q s).fst = c • J u₀ + c • (∫ τ in Ioc 0 s, v τ) := by
      simpa only [WithLp.toLp_fst, map_smul, v] using (hQ s hs.1.le).1
    have h₂ : J (u s) = J u₀ + ∫ τ in Ioc 0 s, v τ := by
      dsimp only [u]
      rw [map_smul, h₁, smul_add, inv_smul_smul₀ hc.ne', inv_smul_smul₀ hc.ne']
    simpa only [← intervalIntegral.integral_of_le hs.1.le, up, ContinuousMap.coe_mk,
      J, W1p.valueL_apply] using h₂
  · intro ψ hψ t
    let φ : 𝓓(⊤, ℝ) := ⟨ψ, hψ.1, hψ.2.1, by simp⟩
    have hintf : (∫ s in Ioc 0 t.1, F s) = ∫ s in (0 : ℝ)..t.1, f s := by
      rw [intervalIntegral.integral_of_le t.2.1]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.trans t.2.2⟩
      exact Set.indicator_of_mem hsT f
    let G := W1p.gradientL (mu := (volume : Measure (EuclideanSpace ℝ (Fin d)))) (Omega := ⊤)
      (p := 2)
    have hGrad :
        (∫ s in (0 : ℝ)..t.1, W1p.gradient (up (Set.projIcc 0 T hT.le s))) =
          c⁻¹ • G (∫ s in Ioc 0 t.1, (Q s).fst) := by
      have hcongr : (∫ s in (0 : ℝ)..t.1, W1p.gradient (up (Set.projIcc 0 T hT.le s))) =
          ∫ s in (0 : ℝ)..t.1, c⁻¹ • G ((Q s).fst) := by
        refine intervalIntegral.integral_congr ?_
        rw [uIcc_of_le t.2.1]
        intro s hs
        have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans t.2.2⟩
        dsimp only
        rw [Set.projIcc_of_mem hT.le hsT, ← W1p.gradientL_apply]
        exact G.map_smul c⁻¹ ((Q s).fst)
      rw [hcongr, intervalIntegral.integral_smul,
        G.intervalIntegral_comp_comm (hq₁.intervalIntegrable 0 t.1),
        intervalIntegral.integral_of_le t.2.1]
    let w : WavePositionSpace d := W1p.ofTestFunctionₗ volume ⊤ 2 φ
    have h₂ := (hQ t.1 t.2.1).2 w
    simp only [WithLp.toLp_snd, hintf, wave_inner_position] at h₂
    have hpair :
        ⟪v t.1, W1p.value w⟫_ℝ - ⟪v₀, W1p.value w⟫_ℝ -
            ⟪∫ s in (0 : ℝ)..t.1, f s, W1p.value w⟫_ℝ +
            c ^ 2 * ⟪∫ s in (0 : ℝ)..t.1, W1p.gradient (up (Set.projIcc 0 T hT.le s)),
              W1p.gradient w⟫_ℝ = 0 := by
      rw [hGrad, real_inner_smul_left, ← W1p.gradientL_apply w]
      have hc' : c ^ 2 * c⁻¹ = c := by field_simp
      rw [← mul_assoc, hc']
      simp only [v, W1p.valueL_apply, J, G] at h₂ ⊢
      linarith
    exact (wave_inner_residual_eq_zero_iff hT.le v₀ hf (up, vp) t φ).1 hpair

/-- **32.50**: existence and uniqueness of the finite-energy forced wave on a compact time
interval. -/
theorem existsUnique_waveEnergySolution {d : ℕ} {c T : ℝ} (hc : 0 < c) (hT : 0 < T)
    (u₀ : WavePositionSpace d) (v₀ : WaveVelocitySpace d) (f : ℝ → WaveVelocitySpace d)
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) T)) :
    ∃! uv, IsWaveEnergySolution c T u₀ v₀ f uv := by
  obtain ⟨uv, huv⟩ := exists_waveEnergySolution hc hT u₀ v₀ hf
  refine ⟨uv, huv, ?_⟩
  intro wv hwv
  exact hwv.unique huv hT hf

/-- **32.52**: data agreeing on an initial ball and forcing agreeing in its shrinking
backward cone give position representatives agreeing in every later shrinking ball.
The identified quantity is `TauCeti.W1p.value` of the position component. All spatial
identities are almost everywhere, as required for energy-space data. -/
theorem wave_finitePropagation {d : ℕ} {c T R : ℝ} (hc : 0 < c) (hT : 0 < T) (hR : 0 < R)
    (x₀ : EuclideanSpace ℝ (Fin d)) (u₀ u₁ : WavePositionSpace d)
    (v₀ v₁ : WaveVelocitySpace d) (f g : ℝ → WaveVelocitySpace d)
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) T)) (hg : IntegrableOn g (Set.Icc (0 : ℝ) T))
    (uv wv : C(Set.Icc (0 : ℝ) T, WavePositionSpace d) ×
      C(Set.Icc (0 : ℝ) T, WaveVelocitySpace d))
    (huv : IsWaveEnergySolution c T u₀ v₀ f uv) (hwv : IsWaveEnergySolution c T u₁ v₁ g wv)
    (hpos : TauCeti.W1p.value u₀ =ᵐ[volume.restrict (Metric.ball x₀ R)] TauCeti.W1p.value u₁)
    (hvel : v₀ =ᵐ[volume.restrict (Metric.ball x₀ R)] v₁)
    (hforce : ∀ᵐ s ∂volume.restrict (Set.Icc (0 : ℝ) T),
      f s =ᵐ[volume.restrict (Metric.ball x₀ (R - c * s))] g s) :
    ∀ t : Set.Icc (0 : ℝ) T, c * t.1 < R →
      TauCeti.W1p.value (uv.1 t) =ᵐ[volume.restrict (Metric.ball x₀ (R - c * t.1))]
        TauCeti.W1p.value (wv.1 t) := by
  sorry

end CKMA
