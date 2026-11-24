/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Fourier.Inequalities.Cutoff

import CKMA.Analysis.Fourier.LpSpace
import TauCeti.Analysis.Fourier.Continuous

/-!
# Coordinate uncertainty

Coordinate uncertainty for unit-norm L² data bounds the product of the physical and
Fourier-side second moments by `1/(4π)`, at Mathlib's `exp(-2πi x·ξ)` normalization.

Source: GAPS 27.13.

## Main results

* `CKMA.heisenberg_uncertainty`: **27.13** coordinate uncertainty inequality bounding the
  product of spatial and frequency `L²` coordinate moments from below by `1 / (4π)` for
  unit-norm `L²` functions.

## Notation

* `V`: local notation for `EuclideanSpace ℝ (Fin d)`.
-/

public section

noncomputable section

namespace CKMA

open Heisenberg Filter MeasureTheory FourierTransform Real Complex VectorFourier Topology
open scoped ENNReal FourierTransform RealInnerProductSpace ComplexInnerProductSpace LineDeriv
  Topology

section HeisenbergAux

variable {d : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin d)

/-- `L²` representative of the distributional derivative of `φₙ 𝓕 f`. -/
private def cutoffDerivLp (n : ℕ) (j : Fin d) (f : Lp ℂ 2 (volume : Measure V))
    (hx : MemLp (fun x ↦ coordFun j x * f x) 2 volume) : Lp ℂ 2 (volume : Measure V) :=
  HSMul.hSMul (γ := Lp ℂ 2 (volume : Measure V))
      ((memLp_top_freqBumpScaled (d := d) n).toLp (freqBumpScaled n) :
        Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure V))
      (𝓕 (-(2 * π * I : ℂ) • hx.toLp (fun x ↦ coordFun j x * f x))) +
    HSMul.hSMul (γ := Lp ℂ 2 (volume : Measure V))
      ((memLp_top_freqBumpDeriv n j).toLp (freqBumpDeriv n j) :
        Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure V)) (𝓕 f)

/-- The distributional derivative of the cutoff of `𝓕 f` is `cutoffDerivLp`. -/
private lemma lineDeriv_freqCutoff_eq (n : ℕ) (j : Fin d) (f : Lp ℂ 2 (volume : Measure V))
    (hx : MemLp (fun x ↦ coordFun j x * f x) 2 volume) :
    ∂_{coordVec j}
        ((memLp_freqBump_mul n (𝓕 f)).toLp (freqCutoff n (𝓕 f)) :
          TemperedDistribution V ℂ) =
      (cutoffDerivLp n j f hx : TemperedDistribution V ℂ) := by
  let Dû : Lp ℂ 2 (volume : Measure V) :=
    𝓕 (-(2 * π * I : ℂ) • hx.toLp (fun x ↦ coordFun j x * f x))
  rw [toLp_freqCutoff_eq_smulLeftCLM]
  rw [lineDeriv_smulLeftCLM_freqBumpScaled]
  nth_rw 1 [← Lp.fourier_toTemperedDistribution_eq f]
  rw [lineDeriv_fourier_lp_eq j f hx]
  rw [← toLp_freqCutoff_eq_smulLeftCLM n Dû]
  rw [← toLp_freqBumpDeriv_smul_eq_smulLeftCLM n j (𝓕 f)]
  rw [toLp_freqCutoff_eq_smul, cutoffDerivLp]
  exact ((Lp.toTemperedDistributionCLM ℂ (volume : Measure V) 2).map_add _ _).symm

/-- Multiplication by the cutoff derivative tends to zero in `L²`. -/
private lemma tendsto_freqBumpDeriv_smul (j : Fin d) (u : Lp ℂ 2 (volume : Measure V)) :
    Tendsto (fun n ↦ HSMul.hSMul (γ := Lp ℂ 2 (volume : Measure V))
      ((memLp_top_freqBumpDeriv n j).toLp (freqBumpDeriv n j) :
        Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure V)) u) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  obtain ⟨C, _, hCle⟩ := exists_norm_toLp_freqBumpDeriv_le j
  have hupper : Tendsto (fun n : ℕ ↦ C / ((n : ℝ) + 1) * ‖u‖) atTop (𝓝 (0 : ℝ)) := by
    have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    simpa [div_eq_mul_inv] using (hinv.const_mul C).mul_const ‖u‖
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hupper
  · exact (Lp.norm_smul_le _ _).trans
      (mul_le_mul_of_nonneg_right (hCle n) (norm_nonneg _))

/-- Frequency cutoff of the Fourier-side coordinate moment. -/
private abbrev freqMomentCut (n : ℕ) (j : Fin d) (f : Lp ℂ 2 (volume : Measure V))
    (hξ : MemLp (fun ξ ↦ coordFun j ξ * (𝓕 f) ξ) 2 volume) :
    Lp ℂ 2 (volume : Measure V) :=
  let ξLp := hξ.toLp (fun ξ ↦ coordFun j ξ * (𝓕 f) ξ)
  (memLp_freqBump_mul n ξLp).toLp (freqCutoff n ξLp)

/-- The coordinate derivative of the cutoff inverse transform is the weighted moment. -/
private lemma fderiv_cutoff_ae (n : ℕ) (j : Fin d) (f : Lp ℂ 2 (volume : Measure V))
    (hξ : MemLp (fun ξ ↦ coordFun j ξ * (𝓕 f) ξ) 2 volume) :
    (fun x ↦ fderiv ℝ (𝓕⁻ (freqCutoff n (𝓕 f))) x (coordVec j)) =ᵐ[volume]
      fun x ↦ (𝓕⁻ ((2 * π * I : ℂ) • freqMomentCut n j f hξ)) x := by
  let c : ℂ := 2 * π * I
  let ξLp : Lp ℂ 2 (volume : Measure V) := hξ.toLp (fun ξ ↦ coordFun j ξ * (𝓕 f) ξ)
  let ξCut : Lp ℂ 2 (volume : Measure V) := freqMomentCut n j f hξ
  let ψ : V → ℂ := fun v ↦ c * (v j : ℂ) * freqCutoff n (𝓕 f) v
  have hderiv : ∀ x, fderiv ℝ (𝓕⁻ (freqCutoff n (𝓕 f))) x (coordVec j) = 𝓕⁻ ψ x :=
    fun x ↦ fderiv_fourierInv_freqCutoff_coord n j (𝓕 f) x
  have hψ : ψ =ᵐ[volume] fun v ↦ c * freqCutoff n ξLp v := by
    filter_upwards [hξ.coeFn_toLp] with v hξv
    simp only [ψ, freqCutoff]
    rw [hξv]
    simp only [coordFun]
    ring
  have hcoe : (fun v ↦ (c • ξCut) v) =ᵐ[volume] fun v ↦ c * freqCutoff n ξLp v := by
    filter_upwards [Lp.coeFn_smul c ξCut, (memLp_freqBump_mul n ξLp).coeFn_toLp] with v hc hcut
    simp only [ξCut, freqMomentCut]
    rw [hc, Pi.smul_apply, smul_eq_mul, hcut]
  have hint : Integrable (fun v ↦ (c • ξCut) v) volume :=
    (integrable_congr hcoe).2 ((integrable_freqCutoff n ξLp).smul c)
  have hae := Integrable.coeFn_fourierInv_toLp hint (Lp.memLp (c • ξCut))
  filter_upwards [hae] with x hx
  rw [hderiv, Real.fourierInv_congr_ae hψ, Real.fourierInv_congr_ae hcoe.symm, ← hx,
    Lp.toLp_coeFn _ (Lp.memLp (c • ξCut))]

/-- Coordinate weight of the cutoff inverse transform, identified in `L²`. -/
private lemma coord_mul_cutoff_ae (n : ℕ) (j : Fin d) (f : Lp ℂ 2 (volume : Measure V))
    (hx : MemLp (fun x ↦ coordFun j x * f x) 2 volume) :
    (fun x ↦ coordFun j x * 𝓕⁻ (freqCutoff n (𝓕 f)) x) =ᵐ[volume]
      fun x ↦ ((-(2 * π * I : ℂ))⁻¹ • 𝓕⁻ (cutoffDerivLp n j f hx)) x := by
  let uLp : Lp ℂ 2 (volume : Measure V) :=
    (memLp_freqBump_mul n (𝓕 f)).toLp (freqCutoff n (𝓕 f))
  let w : Lp ℂ 2 (volume : Measure V) := cutoffDerivLp n j f hx
  let g : V → ℂ := 𝓕⁻ (freqCutoff n (𝓕 f))
  let gLp : Lp ℂ 2 (volume : Measure V) := 𝓕⁻ uLp
  let c : ℂ := -(2 * π * I)
  have hFT : 𝓕⁻ (w : TemperedDistribution V ℂ) =
      c • TemperedDistribution.smulLeftCLM ℂ (coordFun j) (gLp : TemperedDistribution V ℂ) := by
    have hderiv : (w : TemperedDistribution V ℂ) =
        ∂_{coordVec j} (uLp : TemperedDistribution V ℂ) :=
      (lineDeriv_freqCutoff_eq n j f hx).symm
    rw [hderiv]
    rw [TemperedDistribution.fourierInv_lineDerivOp_eq]
    rw [Lp.fourierInv_toTemperedDistribution_eq uLp]
    have hinner : coordFun j = fun x ↦ (inner ℝ x (coordVec j) : ℂ) := by
      ext x; exact coordFun_eq_inner j x
    have hsmul : TemperedDistribution.smulLeftCLM ℂ (coordFun j)
          (gLp : TemperedDistribution V ℂ) =
        TemperedDistribution.smulLeftCLM ℂ (fun x ↦ (inner ℝ x (coordVec j) : ℂ))
          (gLp : TemperedDistribution V ℂ) := by rw [hinner]
    rw [← hsmul]
  have hg_ae : g =ᵐ[volume] fun x ↦ gLp x :=
    (Integrable.coeFn_fourierInv_toLp (integrable_freqCutoff n (𝓕 f))
      (memLp_freqBump_mul n (𝓕 f))).symm
  apply ae_eq_of_integral_contDiff_smul_eq
    ((hasTemperateGrowth_coordFun j).1.continuous.mul
      (integrable_freqCutoff n (𝓕 f)).continuous_fourierInv).locallyIntegrable
    ((Lp.memLp (c⁻¹ • 𝓕⁻ w)).locallyIntegrable one_le_two)
  intro ψ hψ hsup
  let ψC : V → ℂ := fun x ↦ (ψ x : ℂ)
  have hψC : ContDiff ℝ (⊤ : ℕ∞) ψC := Complex.ofRealCLM.contDiff.comp hψ
  have hsupC : HasCompactSupport ψC := hsup.comp_left (g := Complex.ofReal) (by simp)
  let ζ : SchwartzMap V ℂ := hsupC.toSchwartzMap hψC
  have hcoe : (ζ : V → ℂ) = ψC := by ext x; rfl
  have hreal : ∀ x, ψ x • (coordFun j * g) x = ψC x * (coordFun j x * g x) := by
    intro x
    rw [Pi.mul_apply]
    simp [ψC, Complex.real_smul]
  have hreal' : ∀ x, ψ x • (c⁻¹ • 𝓕⁻ w) x = ψC x * (c⁻¹ • 𝓕⁻ w) x := by
    intro x; simp [ψC, Complex.real_smul]
  rw [integral_congr_ae (ae_of_all volume hreal), integral_congr_ae (ae_of_all volume hreal')]
  rw [Lp.fourierInv_toTemperedDistribution_eq] at hFT
  have happly := congrArg (fun T : TemperedDistribution V ℂ ↦ T ζ) hFT
  rw [smul_apply] at happly
  rw [TemperedDistribution.smulLeftCLM_apply_apply] at happly
  rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply] at happly
  simp only [smul_eq_mul] at happly
  have hζg : (fun x ↦ ((SchwartzMap.smulLeftCLM ℂ (coordFun j)) ζ) x * gLp x) =
      fun x ↦ ζ x * (coordFun j x * gLp x) := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_coordFun j)]
    simp only [smul_eq_mul]
    ring
  have hpair : ∫ (x : V), ζ x * (𝓕⁻ w) x =
      c * ∫ (x : V), ζ x * (coordFun j x * gLp x) := by
    simpa [hζg] using happly
  have hc : c ≠ 0 := by
    simpa only [c, neg_ne_zero] using Complex.two_pi_I_ne_zero
  have hmul : ∫ (x : V), ζ x * (c⁻¹ * (𝓕⁻ w) x) =
      ∫ (x : V), ζ x * (coordFun j x * gLp x) := by
    apply mul_left_cancel₀ hc
    have hscale : (fun x ↦ c * (ζ x * (c⁻¹ * (𝓕⁻ w) x))) =
        fun x ↦ ζ x * (𝓕⁻ w) x := by
      ext x
      have hrearr : c * (ζ x * (c⁻¹ * (𝓕⁻ w) x)) =
          (c * c⁻¹) * (ζ x * (𝓕⁻ w) x) := by ring
      rw [hrearr, mul_inv_cancel₀ hc, one_mul]
    calc
      c * ∫ (x : V), ζ x * (c⁻¹ * (𝓕⁻ w) x)
          = ∫ (x : V), c * (ζ x * (c⁻¹ * (𝓕⁻ w) x)) := by
            rw [← integral_const_mul]
      _ = ∫ (x : V), ζ x * (𝓕⁻ w) x := by rw [hscale]
      _ = c * ∫ (x : V), ζ x * (coordFun j x * gLp x) := hpair
  have hψζ : (fun x ↦ ψC x * (coordFun j x * g x)) =
      fun x ↦ ζ x * (coordFun j x * g x) := by
    ext x; rw [← congrFun hcoe x]
  have hζψ : (fun x ↦ ζ x * (c⁻¹ • 𝓕⁻ w) x) =
      fun x ↦ ψC x * (c⁻¹ • 𝓕⁻ w) x := by
    ext x; rw [congrFun hcoe x]
  calc
    ∫ (x : V), ψC x * (coordFun j x * g x)
        = ∫ (x : V), ζ x * (coordFun j x * g x) := by rw [hψζ]
    _ = ∫ (x : V), ζ x * (coordFun j x * gLp x) := by
          refine integral_congr_ae ?_
          filter_upwards [hg_ae] with x hxg
          rw [hxg]
    _ = ∫ (x : V), ζ x * (c⁻¹ * (𝓕⁻ w) x) := hmul.symm
    _ = ∫ (x : V), ζ x * (c⁻¹ • 𝓕⁻ w) x := by
          refine integral_congr_ae ?_
          filter_upwards [Lp.coeFn_smul c⁻¹ (𝓕⁻ w)] with x hsm
          rw [hsm, Pi.smul_apply, smul_eq_mul]
    _ = ∫ (x : V), ψC x * (c⁻¹ • 𝓕⁻ w) x := by rw [hζψ]

/-- Cutoff form of the commutator estimate. -/
private lemma cutoff_sq_le (n : ℕ) (j : Fin d) (f : Lp ℂ 2 (volume : Measure V))
    (hx : MemLp (fun x ↦ coordFun j x * f x) 2 volume)
    (hξ : MemLp (fun ξ ↦ coordFun j ξ * (𝓕 f) ξ) 2 volume) :
    ‖(memLp_freqBump_mul n (𝓕 f)).toLp (freqCutoff n (𝓕 f))‖ ^ 2 ≤
      2 * ‖cutoffDerivLp n j f hx‖ * ‖freqMomentCut n j f hξ‖ := by
  let uLp : Lp ℂ 2 (volume : Measure V) :=
    (memLp_freqBump_mul n (𝓕 f)).toLp (freqCutoff n (𝓕 f))
  let g : V → ℂ := 𝓕⁻ (freqCutoff n (𝓕 f))
  let c : ℂ := -(2 * π * I)
  have hgcont : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_fourierInv_freqCutoff n (𝓕 f)
  have hgae : g =ᵐ[volume] fun x ↦ (𝓕⁻ uLp) x :=
    (Integrable.coeFn_fourierInv_toLp (integrable_freqCutoff n (𝓕 f))
      (memLp_freqBump_mul n (𝓕 f))).symm
  have hgmem : MemLp g 2 volume := (Lp.memLp (𝓕⁻ uLp)).ae_eq hgae.symm
  have hxae := coord_mul_cutoff_ae n j f hx
  have hxmem : MemLp (fun x ↦ coordFun j x * g x) 2 volume :=
    (Lp.memLp (c⁻¹ • 𝓕⁻ (cutoffDerivLp n j f hx))).ae_eq hxae.symm
  have hdae := fderiv_cutoff_ae n j f hξ
  have hdmem : MemLp (fun x ↦ fderiv ℝ g x (coordVec j)) 2 volume :=
    (Lp.memLp (𝓕⁻ ((2 * π * I : ℂ) • freqMomentCut n j f hξ))).ae_eq hdae.symm
  have hNg : ‖hgmem.toLp g‖ = ‖uLp‖ := by
    rw [show hgmem.toLp g = 𝓕⁻ uLp from
      (MemLp.toLp_congr hgmem (Lp.memLp (𝓕⁻ uLp)) hgae).trans
        (Lp.toLp_coeFn (𝓕⁻ uLp) (Lp.memLp (𝓕⁻ uLp)))]
    exact Lp.norm_fourierInv_eq uLp
  have hNx : ‖hxmem.toLp (fun x ↦ coordFun j x * g x)‖ =
      ‖c⁻¹‖ * ‖cutoffDerivLp n j f hx‖ := by
    rw [show hxmem.toLp (fun x ↦ coordFun j x * g x) =
        c⁻¹ • 𝓕⁻ (cutoffDerivLp n j f hx) from
      (MemLp.toLp_congr hxmem (Lp.memLp (c⁻¹ • 𝓕⁻ (cutoffDerivLp n j f hx))) hxae).trans
        (Lp.toLp_coeFn _ (Lp.memLp _))]
    rw [norm_smul, Lp.norm_fourierInv_eq]
  have hNd : ‖hdmem.toLp (fun x ↦ fderiv ℝ g x (coordVec j))‖ =
      (2 * π) * ‖freqMomentCut n j f hξ‖ := by
    rw [show hdmem.toLp (fun x ↦ fderiv ℝ g x (coordVec j)) =
        𝓕⁻ ((2 * π * I : ℂ) • freqMomentCut n j f hξ) from
      (MemLp.toLp_congr hdmem
        (Lp.memLp (𝓕⁻ ((2 * π * I : ℂ) • freqMomentCut n j f hξ))) hdae).trans
        (Lp.toLp_coeFn _ (Lp.memLp _))]
    rw [Lp.norm_fourierInv_eq, norm_smul, norm_two_pi_I]
  have hinv : ‖c⁻¹‖ = (2 * π)⁻¹ := by rw [norm_inv, norm_neg, norm_two_pi_I]
  have hbase := integral_norm_sq_le_two_mul_coord j hgcont hgmem hxmem hdmem
  calc ‖uLp‖ ^ 2 = ‖hgmem.toLp g‖ ^ 2 := by rw [hNg]
    _ ≤ 2 * ‖hxmem.toLp (fun x ↦ coordFun j x * g x)‖ *
        ‖hdmem.toLp (fun x ↦ fderiv ℝ g x (coordVec j))‖ := hbase
    _ = 2 * (‖cutoffDerivLp n j f hx‖ * (2 * π)⁻¹) * ((2 * π) * ‖freqMomentCut n j f hξ‖) := by
      rw [hNx, hNd, hinv]
      ring
    _ = 2 * ‖cutoffDerivLp n j f hx‖ * ‖freqMomentCut n j f hξ‖ := by field_simp

/-- Unit-norm coordinate uncertainty for the explicit coordinate weight. -/
private lemma heisenberg_aux (j : Fin d) (f : Lp ℂ 2 (volume : Measure V)) (hf : ‖f‖ = 1)
    (hx : MemLp (fun x ↦ coordFun j x * f x) 2 volume)
    (hξ : MemLp (fun ξ ↦ coordFun j ξ * (𝓕 f) ξ) 2 volume) :
    (1 / (4 * π) : ℝ) ≤ (eLpNorm (fun x ↦ coordFun j x * f x) 2 volume).toReal *
      (eLpNorm (fun ξ ↦ coordFun j ξ * (𝓕 f) ξ) 2 volume).toReal := by
  let xf := hx.toLp (fun x ↦ coordFun j x * f x)
  let ξf := hξ.toLp (fun ξ ↦ coordFun j ξ * (𝓕 f) ξ)
  let Dû : Lp ℂ 2 (volume : Measure V) := 𝓕 (-(2 * π * I : ℂ) • xf)
  have hD : ‖Dû‖ = 2 * π * ‖xf‖ := norm_fourier_coord_eq j f hx
  have hun : Tendsto (fun n ↦ ‖(memLp_freqBump_mul n (𝓕 f)).toLp (freqCutoff n (𝓕 f))‖)
      atTop (𝓝 ‖f‖) := by
    have h := (continuous_norm.tendsto (𝓕 f)).comp (tendsto_freqBump_mul (𝓕 f))
    rwa [Lp.norm_fourier_eq] at h
  have hξn : Tendsto (fun n ↦ ‖freqMomentCut n j f hξ‖) atTop (𝓝 ‖ξf‖) :=
    (continuous_norm.tendsto ξf).comp (tendsto_freqBump_mul ξf)
  have hφ : Tendsto (fun n ↦ HSMul.hSMul (γ := Lp ℂ 2 (volume : Measure V))
      ((memLp_top_freqBumpScaled (d := d) n).toLp (freqBumpScaled n) :
        Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure V)) Dû) atTop (𝓝 Dû) :=
    (tendsto_congr fun n ↦ toLp_freqCutoff_eq_smul n Dû).mp (tendsto_freqBump_mul Dû)
  have hw : Tendsto (fun n ↦ ‖cutoffDerivLp n j f hx‖) atTop (𝓝 ‖Dû‖) := by
    have hsum := hφ.add (tendsto_freqBumpDeriv_smul j (𝓕 f))
    have hEq : ∀ n, cutoffDerivLp n j f hx =
        HSMul.hSMul (γ := Lp ℂ 2 (volume : Measure V))
          ((memLp_top_freqBumpScaled (d := d) n).toLp (freqBumpScaled n) :
            Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure V)) Dû +
        HSMul.hSMul (γ := Lp ℂ 2 (volume : Measure V))
          ((memLp_top_freqBumpDeriv n j).toLp (freqBumpDeriv n j) :
            Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure V)) (𝓕 f) := fun _ ↦ rfl
    have hsum0 : Tendsto (fun n ↦ cutoffDerivLp n j f hx) atTop (𝓝 Dû) :=
      (tendsto_congr fun n ↦ (hEq n).symm).mp (by simpa [add_zero] using hsum)
    exact (continuous_norm.tendsto Dû).comp hsum0
  have hineq : ∀ n, ‖(memLp_freqBump_mul n (𝓕 f)).toLp (freqCutoff n (𝓕 f))‖ ^ 2 ≤
      2 * ‖cutoffDerivLp n j f hx‖ * ‖freqMomentCut n j f hξ‖ :=
    fun n ↦ cutoff_sq_le n j f hx hξ
  have hlim : ‖f‖ ^ 2 ≤ 2 * ‖Dû‖ * ‖ξf‖ :=
    le_of_tendsto_of_tendsto' ((continuous_pow 2).tendsto ‖f‖ |>.comp hun)
      ((tendsto_const_nhds.mul hw).mul hξn) hineq
  have hfour : ‖f‖ ^ 2 ≤ 4 * π * ‖xf‖ * ‖ξf‖ := by
    rw [hD] at hlim
    calc ‖f‖ ^ 2 ≤ 2 * (2 * π * ‖xf‖) * ‖ξf‖ := hlim
      _ = 4 * π * ‖xf‖ * ‖ξf‖ := by ring
  have hunit : (1 : ℝ) ≤ 4 * π * ‖xf‖ * ‖ξf‖ := by simpa [hf] using hfour
  suffices (1 / (4 * π) : ℝ) ≤ ‖xf‖ * ‖ξf‖ by
    simpa only [xf, ξf, Lp.norm_toLp] using this
  rw [div_le_iff₀ (by positivity)]
  calc (1 : ℝ) ≤ 4 * π * ‖xf‖ * ‖ξf‖ := hunit
    _ = ‖xf‖ * ‖ξf‖ * (4 * π) := by ring

end HeisenbergAux

/-- **27.13**: coordinate uncertainty at Mathlib's `exp(-2πix·ξ)` normalization.
The input and Fourier-side second moments are explicit, and the input has unit `L²` norm. -/
theorem heisenberg_uncertainty {d : ℕ} (j : Fin d)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hf : ‖f‖ = 1)
    (hx : MemLp (fun x ↦ (x j : ℂ) * f x) 2 volume)
    (hξ : MemLp (fun ξ ↦ (ξ j : ℂ) * (𝓕 f) ξ) 2 volume) :
    (1 / (4 * Real.pi) : ℝ) ≤
      (eLpNorm (fun x ↦ (x j : ℂ) * f x) 2 volume).toReal *
      (eLpNorm (fun ξ ↦ (ξ j : ℂ) * (𝓕 f) ξ) 2 volume).toReal :=
  heisenberg_aux j f hf hx hξ

end CKMA
