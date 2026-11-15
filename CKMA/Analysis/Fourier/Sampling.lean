/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Fourier.Sampling.Band
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Bandlimited representatives and Shannon sampling

Inverse Fourier integration over `[-B,B]` gives a continuous representative from any
L² frequency datum. Shannon summands use samples at `k/(2B)` and the normalized sinc
`sin(πt)/(πt)`. Reconstruction converges pointwise, uniformly and in L², and the
representative satisfies an exact sampling Parseval identity. These statements depend
only on the datum inside the integration band.

Source: GAPS 29.58.

## Main results

* `CKMA.shannon_sampling`: **29.58** pointwise and uniform convergence of the Shannon
  sampling series to `bandlimitedRepresentative B u`.
* `CKMA.shannon_sampling_L2`: `L²` convergence of the Shannon sampling partial sums.
* `CKMA.shannon_norm_identity`: exact sampling Parseval identity.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory FourierTransform Filter Topology Metric
open scoped BigOperators ENNReal FourierTransform Real Interval SchwartzMap

variable {B : ℝ}

section Positive

variable (hB : 0 < B)

include hB

omit hB in
/-- Negation preserves the `atTop` filter of finite sets. -/
private lemma tendsto_image_neg :
    Tendsto (fun s : Finset ℤ => s.image Neg.neg) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  rw [eventually_atTop]
  refine ⟨b.image Neg.neg, fun s hs k hk => ?_⟩
  refine Finset.mem_image.2 ⟨-k, hs ?_, neg_neg k⟩
  exact Finset.mem_image.2 ⟨k, hk, rfl⟩

omit hB in
/-- The frequency partial sum, cut off to the band, is square-integrable. -/
private lemma memLp_freqBand (f : ℝ → ℂ) (s : Finset ℤ) :
    MemLp (freqBand B f s) 2 volume := by
  have hsupp : HasCompactSupport (freqBand B f s) := by
    refine HasCompactSupport.intro (K := Set.Icc (-B) B) isCompact_Icc ?_
    intro x hx
    simp [freqBand, bandCutoff, Set.indicator_of_notMem hx]
  have hmeas : AEStronglyMeasurable (freqBand B f s) volume :=
    (continuous_freqPartial f s).aestronglyMeasurable.indicator measurableSet_Icc
  refine hsupp.memLp_of_bound hmeas
    (∑ k ∈ s, ‖((2 * B)⁻¹ : ℝ) • f (k / (2 * B))‖) ?_
  filter_upwards with x
  rw [freqBand, bandCutoff]
  by_cases hx : x ∈ Set.Icc (-B) B
  · simp only [hx, Set.indicator_of_mem, freqPartial]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_samplingCharacter k x, mul_one]
  · rw [Set.indicator_of_notMem hx, norm_zero]
    positivity

/-- `L²` norm of the frequency remainder tends to zero along finite sets. -/
private lemma tendsto_lpNorm_remainder (u : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun s : Finset ℤ =>
      lpNorm (bandCutoff B (⇑u) - freqBand B (bandlimitedRepresentative B u) s) 2 volume)
      atTop (𝓝 0) := by
  let c : ℤ → ℂ := fourierCoeffOn (band_lt hB) (⇑u)
  have hc : Summable fun i => ‖c i‖ ^ 2 :=
    (hasSum_sq_fourierCoeffOn (band_lt hB) (memLp_u_Ioc u)).summable
  have hsum : Tendsto (fun s : Finset ℤ => ∑ i ∈ s, ‖c i‖ ^ 2) atTop
      (𝓝 (∑' i, ‖c i‖ ^ 2)) := by
    simpa [HasSum, SummationFilter.unconditional_filter] using hc.hasSum
  have htail : Tendsto (fun s : Finset ℤ =>
      ∑' i, ‖c i‖ ^ 2 - ∑ i ∈ s.image Neg.neg, ‖c i‖ ^ 2) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : Finset ℤ => ∑' i, ‖c i‖ ^ 2) atTop
        (𝓝 (∑' i, ‖c i‖ ^ 2)) := tendsto_const_nhds
    have hsub := hconst.sub (hsum.comp tendsto_image_neg)
    simp only [Function.comp_apply] at hsub
    simpa only [sub_self] using hsub
  have hnn : ∀ s : Finset ℤ,
      0 ≤ ∑' i, ‖c i‖ ^ 2 - ∑ i ∈ s.image Neg.neg, ‖c i‖ ^ 2 := by
    intro s
    have hle := hc.sum_le_tsum (s.image Neg.neg) (fun _ _ => sq_nonneg _)
    linarith
  have hsqrt : Tendsto (fun s : Finset ℤ =>
      Real.sqrt ((2 * B) * (∑' i, ‖c i‖ ^ 2 -
        ∑ i ∈ s.image Neg.neg, ‖c i‖ ^ 2))) atTop (𝓝 0) := by
    have hmul := htail.const_mul (2 * B)
    have hzero : Tendsto (fun s : Finset ℤ => (2 * B) * (∑' i, ‖c i‖ ^ 2 -
        ∑ i ∈ Finset.image Neg.neg s, ‖c i‖ ^ 2)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hmul
    simpa [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hzero
  have heq : (fun s : Finset ℤ =>
      lpNorm (bandCutoff B (⇑u) - freqBand B (bandlimitedRepresentative B u) s) 2 volume) =
      fun s => Real.sqrt ((2 * B) * (∑' i, ‖c i‖ ^ 2 -
        ∑ i ∈ s.image Neg.neg, ‖c i‖ ^ 2)) := by
    ext s
    have hmem : MemLp (bandCutoff B (⇑u) -
        freqBand B (bandlimitedRepresentative B u) s) 2 volume :=
      (memLp_bandCutoff u).sub (memLp_freqBand _ s)
    rw [lpNorm_eq_integral_norm_rpow_toReal (by simp) (by simp) hmem.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat]
    simp_rw [Real.rpow_two]
    rw [integral_norm_sq_remainder hB u s]
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  rw [heq]
  exact hsqrt

/-- One sampling character, integrated against the inverse phase, is a normalized sinc. -/
private lemma integral_samplingCharacter (k : ℤ) (t : ℝ) :
    ∫ ξ in Set.Icc (-B) B,
        Complex.exp (2 * Real.pi * Complex.I * t * ξ) * samplingCharacter B k ξ =
      (2 * B : ℂ) * (normalizedSinc (2 * B * t - k) : ℂ) := by
  set alpha : ℝ := t - (k : ℝ) / (2 * B)
  have hphase : ∀ ξ : ℝ,
      Complex.exp (2 * Real.pi * Complex.I * t * ξ) * samplingCharacter B k ξ =
        Complex.exp (2 * Real.pi * Complex.I * alpha * ξ) := by
    intro ξ
    rw [samplingCharacter, ← Complex.exp_add]
    congr 1
    simp only [alpha]
    push_cast
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Icc fun ξ _ => hphase ξ,
    integral_exp_band hB]
  congr 1
  have hB0 : (2 * B : ℝ) ≠ 0 := mul_ne_zero two_ne_zero (ne_of_gt hB)
  congr 1
  simp only [alpha]
  field_simp [hB0]

/-- One frequency term inverts to one Shannon summand. -/
private lemma integral_one_shannonTerm (u : Lp ℂ 2 (volume : Measure ℝ)) (k : ℤ) (t : ℝ) :
    ∫ ξ in Set.Icc (-B) B,
        Complex.exp (2 * Real.pi * Complex.I * t * ξ) *
          (((2 * B)⁻¹ : ℝ) • bandlimitedRepresentative B u (k / (2 * B)) *
            samplingCharacter B k ξ) =
      shannonTerm B (bandlimitedRepresentative B u) k t := by
  have hpull : ∀ ξ : ℝ,
      Complex.exp (2 * Real.pi * Complex.I * t * ξ) *
          (((2 * B)⁻¹ : ℝ) • bandlimitedRepresentative B u (k / (2 * B)) *
            samplingCharacter B k ξ) =
        (((2 * B)⁻¹ : ℝ) • bandlimitedRepresentative B u (k / (2 * B))) *
          (Complex.exp (2 * Real.pi * Complex.I * t * ξ) * samplingCharacter B k ξ) := by
    intro ξ
    rw [mul_left_comm]
  simp_rw [hpull]
  rw [integral_const_mul, integral_samplingCharacter hB k t, shannonTerm]
  rw [Algebra.smul_def, mul_assoc]
  push_cast
  have hB0 : (B : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  field_simp [hB0]
  rw [mul_comm (bandlimitedRepresentative B u (k / (2 * B))) (B : ℂ)]
  rfl

/-- A Shannon partial sum is the inverse Fourier integral of the frequency partial sum. -/
private lemma shannonSum_eq_fourierInv (u : Lp ℂ 2 (volume : Measure ℝ))
    (s : Finset ℤ) (t : ℝ) :
    ∑ k ∈ s, shannonTerm B (bandlimitedRepresentative B u) k t =
      𝓕⁻ (freqBand B (bandlimitedRepresentative B u) s) t := by
  rw [Real.fourierInv_eq', freqBand, bandCutoff]
  simp_rw [Real.inner_apply, smul_eq_mul]
  have hmul : ∀ ξ : ℝ,
      Complex.exp (↑(2 * Real.pi * (ξ * t)) * Complex.I) *
          (Set.Icc (-B) B).indicator
            (freqPartial B (bandlimitedRepresentative B u) s) ξ =
        (Set.Icc (-B) B).indicator
          (fun ξ => Complex.exp (2 * Real.pi * Complex.I * t * ξ) *
            freqPartial B (bandlimitedRepresentative B u) s ξ) ξ := by
    intro ξ
    by_cases hξ : ξ ∈ Set.Icc (-B) B
    · simp only [hξ, Set.indicator_of_mem]
      congr 1
      simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
      ring
    · simp [hξ]
  simp_rw [hmul, integral_indicator measurableSet_Icc, freqPartial, Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simpa [mul_assoc] using (integral_one_shannonTerm hB u k t).symm
  · intro k _
    exact ((Complex.continuous_exp.comp (by fun_prop)).mul
      ((continuous_const.mul (continuous_samplingCharacter k)))).integrableOn_Icc

omit hB in
/-- Inverse Fourier integrals preserve differences of integrable functions. -/
private lemma fourierInv_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (t : ℝ) :
    𝓕⁻ (f - g) t = 𝓕⁻ f t - 𝓕⁻ g t := by
  rw [Real.fourierInv_eq, Real.fourierInv_eq, Real.fourierInv_eq]
  have hsub : (fun v => 𝐞 (inner ℝ v t) • (f - g) v) =
      (fun v => 𝐞 (inner ℝ v t) • f v) - fun v => 𝐞 (inner ℝ v t) • g v := by
    ext v
    simp [smul_sub, Pi.sub_apply]
  have hpoint : ((fun v => 𝐞 (inner ℝ v t) • f v) - fun v => 𝐞 (inner ℝ v t) • g v) =
      fun v => 𝐞 (inner ℝ v t) • f v - 𝐞 (inner ℝ v t) • g v := by
    ext v
    rfl
  rw [hsub, hpoint, integral_sub]
  · simpa [inner_neg_right, neg_neg] using (Real.fourierIntegral_convergent_iff (-t)).2 hf
  · simpa [inner_neg_right, neg_neg] using (Real.fourierIntegral_convergent_iff (-t)).2 hg

omit hB in
/-- Inner product on `ℝ` is symmetric, so negating it is invariant under flip. -/
private lemma neg_inner_flip : LinearMap.flip (-innerₗ ℝ) = -innerₗ ℝ := by
  ext
  simp [LinearMap.flip_apply, LinearMap.neg_apply]

omit hB in
/-- The integral inverse Fourier transform of an `L¹ ∩ L²` function agrees almost everywhere
with the `L²` inverse Fourier transform. -/
private lemma fourierInv_toLp_ae_eq {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2 volume) :
    (⇑(𝓕⁻ (hf2.toLp f) : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume] 𝓕⁻ f := by
  let F : Lp ℂ 2 volume := hf2.toLp f
  let G : Lp ℂ 2 volume := 𝓕⁻ F
  have hlocLp : LocallyIntegrable (⇑G) volume :=
    (Lp.memLp G).locallyIntegrable fact_one_le_two_ennreal.elim
  have hcontL : Continuous fun p : ℝ × ℝ => (innerₗ ℝ) p.1 p.2 :=
    continuous_snd.mul continuous_fst
  have hcontNeg : Continuous fun p : ℝ × ℝ => (-innerₗ ℝ) p.1 p.2 := by
    have hneg : (fun p : ℝ × ℝ => (-innerₗ ℝ) p.1 p.2) =
        fun p => -((innerₗ ℝ) p.1 p.2) := by
      ext p
      simp [LinearMap.neg_apply]
    rw [hneg]
    exact hcontL.neg
  have hcontF : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous (L := innerₗ ℝ)
      Real.continuous_fourierChar hcontL hf1
  have hlocInv : LocallyIntegrable (𝓕⁻ f) volume := by
    have heq : 𝓕⁻ f = fun w => 𝓕 f (-w) := by
      ext w
      exact Real.fourierInv_eq_fourier_neg f w
    rw [heq]
    exact (hcontF.comp continuous_neg).locallyIntegrable
  refine ae_eq_of_integral_contDiff_smul_eq hlocLp hlocInv ?_
  intro g hg_diff hg_supp
  let phiFun : ℝ → ℂ := fun x => (g x : ℂ)
  have hphiSupp : HasCompactSupport phiFun := hg_supp.comp_left Complex.ofReal_zero
  have hphiDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) phiFun :=
    (Complex.ofRealCLM.contDiff.of_le
      (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) le_top).comp hg_diff
  let phi : 𝓢(ℝ, ℂ) := hphiSupp.toSchwartzMap hphiDiff
  have hphiCoe : (phi : ℝ → ℂ) = phiFun := rfl
  have hsmul : ∀ x z, g x • z = phiFun x * z := by
    intro x z
    simp [phiFun, Algebra.smul_def]
  have hleft : ∫ x, g x • G x =
      ∫ x, phi x • G x := by
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [hphiCoe, hsmul]
    simp [smul_eq_mul]
  have hright : ∫ x, g x • 𝓕⁻ f x = ∫ x, phiFun x * 𝓕⁻ f x := by
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [hsmul]
  rw [hleft, hright]
  have hdist := congrArg (fun T : 𝓢'(ℝ, ℂ) => T phi)
     (Lp.fourierInv_toTemperedDistribution_eq F)
  simp only [TemperedDistribution.fourierInv_apply] at hdist
  rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply] at hdist
  have hcoe : (⇑F : ℝ → ℂ) =ᵐ[volume] f := hf2.coeFn_toLp
  have hswap : ∫ x, (𝓕⁻ phi) x • F x =
      ∫ x, (𝓕⁻ (phi : ℝ → ℂ)) x * f x := by
    refine integral_congr_ae ?_
    filter_upwards [hcoe] with x hx
    rw [hx, SchwartzMap.fourierInv_coe, smul_eq_mul]
  rw [hswap] at hdist
  have hFub : ∫ x, (𝓕⁻ (phi : ℝ → ℂ)) x * f x =
      ∫ x, phiFun x * 𝓕⁻ f x := by
    have hphiInt : Integrable (phi : ℝ → ℂ) := phi.integrable
    have hadj := VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (L := -innerₗ ℝ) (e := 𝐞)
      (ContinuousLinearMap.mul ℂ ℂ)
      Real.continuous_fourierChar hcontNeg hphiInt hf1
    simp only [ContinuousLinearMap.mul_apply', neg_inner_flip] at hadj
    have hFT : ∀ (g : ℝ → ℂ) (w : ℝ),
        VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ) g w = 𝓕⁻ g w := by
      intro g w
      rw [Real.fourierInv_eq, VectorFourier.fourierIntegral]
      refine integral_congr_ae (ae_of_all _ fun v => ?_)
      simp [LinearMap.neg_apply, innerₗ_apply_apply]
    simp_rw [hFT] at hadj
    simpa [hphiCoe] using hadj
  rw [← hdist, hFub]

omit hB in
/-- Plancherel: the integral inverse Fourier transform preserves the `L²` norm. -/
private lemma eLpNorm_fourierInv_eq {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2 volume) :
    eLpNorm (𝓕⁻ f) 2 volume = eLpNorm f 2 volume := by
  let F : Lp ℂ 2 volume := hf2.toLp f
  let G : Lp ℂ 2 volume := 𝓕⁻ F
  have hF : ⇑F =ᵐ[volume] f := hf2.coeFn_toLp
  have hinv : ⇑G =ᵐ[volume] 𝓕⁻ f := fourierInv_toLp_ae_eq hf1 hf2
  have hnorm : ‖G‖ = ‖F‖ := by
    rw [← Lp.norm_fourier_eq G, fourier_fourierInv_eq]
  have henn : eLpNorm (⇑G) 2 volume = eLpNorm (⇑F) 2 volume := by
    have hreal : (eLpNorm (⇑G) 2 volume).toReal =
        (eLpNorm (⇑F) 2 volume).toReal := by
      simp_rw [← Lp.norm_def]
      exact hnorm
    exact (ENNReal.toReal_eq_toReal_iff' (Lp.memLp G).eLpNorm_ne_top
      (Lp.memLp F).eLpNorm_ne_top).1 hreal
  rw [← eLpNorm_congr_ae hinv, henn, eLpNorm_congr_ae hF]

/-- Cauchy–Schwarz on the band upgrades an `L²` remainder to a uniform bound. -/
private lemma norm_shannon_remainder_le (u : Lp ℂ 2 (volume : Measure ℝ))
    (s : Finset ℤ) (t : ℝ) :
    ‖(∑ k ∈ s, shannonTerm B (bandlimitedRepresentative B u) k t) -
        bandlimitedRepresentative B u t‖ ≤
      Real.sqrt (2 * B) *
        lpNorm (bandCutoff B (⇑u) - freqBand B (bandlimitedRepresentative B u) s) 2 volume := by
  let r : ℝ → ℂ := fun ξ =>
    freqPartial B (bandlimitedRepresentative B u) s ξ - u ξ
  have hint : (∑ k ∈ s, shannonTerm B (bandlimitedRepresentative B u) k t) -
      bandlimitedRepresentative B u t =
      ∫ ξ in Set.Icc (-B) B, Complex.exp (2 * Real.pi * Complex.I * t * ξ) * r ξ := by
    have hfBand : Integrable (freqBand B (bandlimitedRepresentative B u) s) := by
      unfold freqBand bandCutoff
      rw [integrable_indicator_iff measurableSet_Icc]
      exact (continuous_freqPartial (bandlimitedRepresentative B u) s).integrableOn_Icc
    have hgCut : Integrable (bandCutoff B (⇑u)) := integrable_bandCutoff u
    rw [shannonSum_eq_fourierInv hB, bandlimitedRepresentative_eq_fourierInv,
      ← fourierInv_sub hfBand hgCut t]
    rw [Real.fourierInv_eq', freqBand]
    unfold bandCutoff
    simp_rw [Real.inner_apply, smul_eq_mul]
    have hsub : ∀ ξ : ℝ,
        Complex.exp (↑(2 * Real.pi * (ξ * t)) * Complex.I) *
            ((Set.Icc (-B) B).indicator
                (freqPartial B (bandlimitedRepresentative B u) s) -
              (Set.Icc (-B) B).indicator (⇑u)) ξ =
          (Set.Icc (-B) B).indicator
            (fun ξ => Complex.exp (2 * Real.pi * Complex.I * t * ξ) * r ξ) ξ := by
      intro ξ
      by_cases hξ : ξ ∈ Set.Icc (-B) B
      · rw [Pi.sub_apply, Set.indicator_of_mem hξ, Set.indicator_of_mem hξ,
          Set.indicator_of_mem hξ]
        congr 1
        · simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
          ring
      · rw [Pi.sub_apply, Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ,
          Set.indicator_of_notMem hξ, sub_self, mul_zero]
    rw [integral_congr_ae (ae_of_all volume hsub), integral_indicator measurableSet_Icc]
  rw [hint]
  have hL1 : IntegrableOn r (Set.Icc (-B) B) := by
    have hu : IntegrableOn (⇑u) (Set.Icc (-B) B) := by
      rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -B ≤ B)]
      exact intervalIntegrable_u hB u
    exact ((continuous_freqPartial _ s).integrableOn_Icc).sub hu
  have hphase : IntegrableOn
      (fun ξ : ℝ => Complex.exp (2 * Real.pi * Complex.I * t * ξ) * r ξ)
      (Set.Icc (-B) B) := by
    refine hL1.bdd_mul (c := 1) ?_ ?_
    · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mono_ac
        (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    · filter_upwards with ξ
      simp [norm_phase]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hnorm : ∫ ξ in Set.Icc (-B) B,
      ‖Complex.exp (2 * Real.pi * Complex.I * t * ξ) * r ξ‖ =
      ∫ ξ in Set.Icc (-B) B, ‖r ξ‖ := by
    refine setIntegral_congr_fun measurableSet_Icc fun ξ _ => ?_
    rw [norm_mul, norm_phase, one_mul]
  rw [hnorm]
  let μ : Measure ℝ := volume.restrict (Set.Icc (-B) B)
  have hr : MemLp r 2 μ := by
    have hu : MemLp (⇑u) 2 μ := (Lp.memLp u).restrict (Set.Icc (-B) B)
    have hp : MemLp (freqPartial B (bandlimitedRepresentative B u) s) 2 μ := by
      refine MemLp.of_bound
        ((continuous_freqPartial _ s).aestronglyMeasurable.mono_ac
          (Measure.absolutelyContinuous_of_le Measure.restrict_le_self))
        (∑ k ∈ s, ‖((2 * B)⁻¹ : ℝ) •
          bandlimitedRepresentative B u (k / (2 * B))‖) ?_
      filter_upwards with x
      unfold freqPartial
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [norm_mul, norm_samplingCharacter, mul_one]
    exact hp.sub hu
  have hone : MemLp (fun _ : ℝ => (1 : ℂ)) (ENNReal.ofReal 2) μ := by
    simpa [ENNReal.ofReal_ofNat] using (memLp_const (1 : ℂ) : MemLp (fun _ => (1 : ℂ)) 2 μ)
  have hr2 : MemLp r (ENNReal.ofReal 2) μ := by simpa [ENNReal.ofReal_ofNat] using hr
  have hholder := integral_mul_norm_le_Lp_mul_Lq (μ := μ)
    Real.HolderConjugate.two_two hr2 hone
  have honeInt : ∫ a, ‖(1 : ℂ)‖ ^ (2 : ℝ) ∂μ = 2 * B := by
    simp_rw [norm_one, Real.one_rpow]
    rw [integral_const]
    have hμ : μ.real Set.univ = 2 * B := by
      unfold μ
      rw [Measure.real, Measure.restrict_apply_univ]
      rw [show (volume (Set.Icc (-B) B)).toReal = B - (-B) by
        simpa [Measure.real] using
          Real.volume_real_Icc_of_le (by linarith : -B ≤ B)]
      ring
    rw [hμ, smul_eq_mul, mul_one]
  have hrInt : ∫ a, ‖r a‖ ^ (2 : ℝ) ∂μ =
      ∫ x, ‖(bandCutoff B (⇑u) - freqBand B (bandlimitedRepresentative B u) s) x‖ ^ 2 := by
    simp_rw [Real.rpow_two]
    rw [← integral_indicator measurableSet_Icc]
    refine integral_congr_ae ?_
    filter_upwards with x
    unfold freqBand
    unfold bandCutoff
    by_cases hx : x ∈ Set.Icc (-B) B
    · rw [Set.indicator_of_mem hx, Pi.sub_apply, Set.indicator_of_mem hx,
        Set.indicator_of_mem hx]
      simp [r, norm_sub_rev]
    · rw [Set.indicator_of_notMem hx, Pi.sub_apply, Set.indicator_of_notMem hx,
        Set.indicator_of_notMem hx, sub_self, norm_zero]
      norm_num
  have hleft : ∫ a, ‖r a‖ * ‖(1 : ℂ)‖ ∂μ = ∫ ξ in Set.Icc (-B) B, ‖r ξ‖ := by
    simp [μ, norm_one, mul_one]
  rw [hleft, honeInt, hrInt] at hholder
  have hlp : (∫ x, ‖(bandCutoff B (⇑u) -
        freqBand B (bandlimitedRepresentative B u) s) x‖ ^ 2) ^ (1 / 2 : ℝ) =
      lpNorm (bandCutoff B (⇑u) - freqBand B (bandlimitedRepresentative B u) s) 2 volume := by
    have hmem : MemLp (bandCutoff B (⇑u) -
        freqBand B (bandlimitedRepresentative B u) s) 2 volume :=
      (memLp_bandCutoff u).sub (memLp_freqBand _ s)
    rw [lpNorm_eq_integral_norm_rpow_toReal (by simp) (by simp) hmem.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat]
    simp_rw [Real.rpow_two]
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  have hsqrt : ((2 * B : ℝ) ^ (1 / 2 : ℝ)) = Real.sqrt (2 * B) := by
    rw [← Real.sqrt_eq_rpow]
  rw [hlp] at hholder
  rw [hsqrt, mul_comm] at hholder
  exact hholder

end Positive

/-- **29.58**: Shannon reconstruction for the integral representative, both pointwise and uniformly.
-/
theorem shannon_sampling {B : ℝ} (hB : 0 < B)
    (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (∀ t, HasSum (fun k : ℤ ↦ shannonTerm B (bandlimitedRepresentative B u) k t)
      (bandlimitedRepresentative B u t)) ∧
    TendstoUniformly
      (fun s : Finset ℤ ↦ fun t ↦ ∑ k ∈ s, shannonTerm B (bandlimitedRepresentative B u) k t)
      (bandlimitedRepresentative B u) atTop := by
  have hlp := tendsto_lpNorm_remainder hB u
  have hbound : ∀ s t,
      dist (∑ k ∈ s, shannonTerm B (bandlimitedRepresentative B u) k t)
        (bandlimitedRepresentative B u t) ≤
      Real.sqrt (2 * B) *
        lpNorm (bandCutoff B (⇑u) - freqBand B (bandlimitedRepresentative B u) s) 2 volume := by
    intro s t
    rw [dist_eq_norm]
    simpa [norm_sub_rev] using norm_shannon_remainder_le hB u s t
  have hzero : Tendsto (fun s : Finset ℤ =>
      Real.sqrt (2 * B) *
        lpNorm (bandCutoff B (⇑u) - freqBand B (bandlimitedRepresentative B u) s) 2 volume)
      atTop (𝓝 0) := by
    simpa using hlp.const_mul (Real.sqrt (2 * B))
  refine ⟨fun t => ?_, ?_⟩
  · rw [HasSum, SummationFilter.unconditional_filter]
    refine Metric.tendsto_atTop.2 fun ε hε => ?_
    have hε' := (tendsto_order.1 hzero).2 ε hε
    rw [Filter.eventually_atTop] at hε'
    rcases hε' with ⟨N, hN⟩
    exact ⟨N, fun s hs => (hbound s t).trans_lt (hN s hs)⟩
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hε' := (tendsto_order.1 hzero).2 ε hε
    filter_upwards [hε'] with s hs t
    rw [dist_comm]
    exact (hbound s t).trans_lt hs

/-- The same sampling sums converge in `L²`. -/
theorem shannon_sampling_L2 {B : ℝ} (hB : 0 < B)
    (u : Lp ℂ 2 (volume : Measure ℝ)) :
    Tendsto (fun s : Finset ℤ ↦ eLpNorm
      (fun t ↦ (∑ k ∈ s, shannonTerm B (bandlimitedRepresentative B u) k t) -
        bandlimitedRepresentative B u t) 2 volume) atTop (𝓝 0) := by
  have hintFreq : ∀ s : Finset ℤ,
      Integrable (freqBand B (bandlimitedRepresentative B u) s) := by
    intro s
    unfold freqBand bandCutoff
    rw [integrable_indicator_iff measurableSet_Icc]
    exact (continuous_freqPartial (bandlimitedRepresentative B u) s).integrableOn_Icc
  have hintCut : Integrable (bandCutoff B (⇑u)) := integrable_bandCutoff u
  have hpoint : ∀ s t,
      (∑ k ∈ s, shannonTerm B (bandlimitedRepresentative B u) k t) -
        bandlimitedRepresentative B u t =
      𝓕⁻ (freqBand B (bandlimitedRepresentative B u) s - bandCutoff B (⇑u)) t := by
    intro s t
    rw [shannonSum_eq_fourierInv hB, bandlimitedRepresentative_eq_fourierInv,
      ← fourierInv_sub (hintFreq s) hintCut]
  have hnorm : ∀ s, eLpNorm
      (fun t => (∑ k ∈ s, shannonTerm B (bandlimitedRepresentative B u) k t) -
        bandlimitedRepresentative B u t) 2 volume =
      eLpNorm (freqBand B (bandlimitedRepresentative B u) s - bandCutoff B (⇑u)) 2 volume := by
    intro s
    have hf1 : Integrable (freqBand B (bandlimitedRepresentative B u) s -
        bandCutoff B (⇑u)) := (hintFreq s).sub hintCut
    have hf2 : MemLp (freqBand B (bandlimitedRepresentative B u) s -
        bandCutoff B (⇑u)) 2 :=
      (memLp_freqBand _ s).sub (memLp_bandCutoff u)
    rw [show (fun t => (∑ k ∈ s, shannonTerm B (bandlimitedRepresentative B u) k t) -
          bandlimitedRepresentative B u t) =
        𝓕⁻ (freqBand B (bandlimitedRepresentative B u) s - bandCutoff B (⇑u)) by
      ext t
      exact hpoint s t, eLpNorm_fourierInv_eq hf1 hf2]
  have htail := tendsto_lpNorm_remainder hB u
  have hmem : ∀ s, MemLp (freqBand B (bandlimitedRepresentative B u) s - bandCutoff B (⇑u)) 2 :=
    fun s => (memLp_freqBand _ s).sub (memLp_bandCutoff u)
  have hreal : Tendsto (fun s =>
      lpNorm (freqBand B (bandlimitedRepresentative B u) s - bandCutoff B (⇑u)) 2 volume)
      atTop (𝓝 0) := by
    have heq : (fun s =>
        lpNorm (freqBand B (bandlimitedRepresentative B u) s - bandCutoff B (⇑u)) 2 volume) =
        fun s => lpNorm (bandCutoff B (⇑u) -
          freqBand B (bandlimitedRepresentative B u) s) 2 volume := by
      ext s
      rw [lpNorm_sub_comm]
    rw [heq]
    exact htail
  have henn : Tendsto (fun s =>
      eLpNorm (freqBand B (bandlimitedRepresentative B u) s - bandCutoff B (⇑u)) 2 volume)
      atTop (𝓝 0) := by
    have heq : (fun s =>
        eLpNorm (freqBand B (bandlimitedRepresentative B u) s - bandCutoff B (⇑u)) 2 volume) =
        fun s => ENNReal.ofReal
          (lpNorm (freqBand B (bandlimitedRepresentative B u) s - bandCutoff B (⇑u)) 2 volume) := by
      ext s
      exact (ofReal_lpNorm (hmem s)).symm
    rw [heq, ← ENNReal.ofReal_zero]
    exact (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  exact henn.congr fun s => (hnorm s).symm

/-- Exact sampling Parseval identity. -/
theorem shannon_norm_identity {B : ℝ} (hB : 0 < B)
    (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫⁻ t, ENNReal.ofReal (‖bandlimitedRepresentative B u t‖ ^ 2)) =
      ENNReal.ofReal ((2 * B)⁻¹) * ∑' k : ℤ,
        ENNReal.ofReal (‖bandlimitedRepresentative B u (k / (2 * B))‖ ^ 2) := by
  let c : ℤ → ℂ := fourierCoeffOn (band_lt hB) (⇑u)
  have hc : Summable fun i => ‖c i‖ ^ 2 :=
    (hasSum_sq_fourierCoeffOn (band_lt hB) (memLp_u_Ioc u)).summable
  have hparse : ∑' i, ‖c i‖ ^ 2 =
      (2 * B)⁻¹ * ∫ x, ‖bandCutoff B (⇑u) x‖ ^ 2 := by
    have hts := tsum_sq_fourierCoeffOn (band_lt hB) (memLp_u_Ioc u)
    have hscalar : (((-B + 2 * B) - (-B))⁻¹ : ℝ) = (2 * B)⁻¹ := by
      rw [band_period]
    rw [hscalar, smul_eq_mul] at hts
    have hint : ∫ x in -B..(-B + 2 * B), ‖u x‖ ^ 2 =
        ∫ x, ‖bandCutoff B (⇑u) x‖ ^ 2 := by
      rw [band_right]
      rw [intervalIntegral.integral_of_le (by linarith : -B ≤ B)]
      rw [setIntegral_congr_set
        (MeasureTheory.Ioc_ae_eq_Icc' (by simp : volume {(-B)} = 0))]
      rw [← integral_indicator measurableSet_Icc]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [bandCutoff]
      exact (norm_sq_indicator _ _ _).symm
    rw [hint] at hts
    exact hts
  have hcoeff : ∀ k : ℤ, ‖bandlimitedRepresentative B u (k / (2 * B))‖ ^ 2 =
      (2 * B) ^ 2 * ‖c (-k)‖ ^ 2 := by
    intro k
    have hc' : c (-k) = ((2 * B)⁻¹ : ℝ) • bandlimitedRepresentative B u (k / (2 * B)) :=
      fourierCoeffOn_neg_eq_sample hB u k
    have hrec : bandlimitedRepresentative B u (k / (2 * B)) = (2 * B : ℝ) • c (-k) := by
      rw [hc', smul_smul, mul_inv_cancel₀ (mul_ne_zero two_ne_zero (ne_of_gt hB)), one_smul]
    rw [hrec, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos two_pos hB)]
    ring
  have hsumm : Summable fun k : ℤ => ‖bandlimitedRepresentative B u (k / (2 * B))‖ ^ 2 := by
    have hre : Summable fun k : ℤ => ‖c (-k)‖ ^ 2 := hc.comp_injective neg_injective
    exact (summable_congr fun k => (hcoeff k).symm).mp (hre.mul_left ((2 * B) ^ 2))
  have htsum : ∑' k : ℤ, ‖bandlimitedRepresentative B u (k / (2 * B))‖ ^ 2 =
      (2 * B) * ∫ x, ‖bandCutoff B (⇑u) x‖ ^ 2 := by
    have hfun : (fun k : ℤ => ‖bandlimitedRepresentative B u (k / (2 * B))‖ ^ 2) =
        fun k => (2 * B) ^ 2 * ‖c (-k)‖ ^ 2 := by
      ext k
      exact hcoeff k
    rw [hfun, tsum_mul_left]
    have hneg : ∑' x : ℤ, ‖c (-x)‖ ^ 2 = ∑' i, ‖c i‖ ^ 2 :=
      (Equiv.neg ℤ).tsum_eq (fun i => ‖c i‖ ^ 2)
    rw [hneg, hparse]
    have hB0 : (2 * B : ℝ) ≠ 0 := mul_ne_zero two_ne_zero (ne_of_gt hB)
    field_simp [hB0]
  have hf1 : Integrable (bandCutoff B (⇑u)) := integrable_bandCutoff u
  have hf2 : MemLp (bandCutoff B (⇑u)) 2 := memLp_bandCutoff u
  have hplan : ∫ t, ‖bandlimitedRepresentative B u t‖ ^ 2 =
      ∫ x, ‖bandCutoff B (⇑u) x‖ ^ 2 := by
    have hrep : bandlimitedRepresentative B u = 𝓕⁻ (bandCutoff B (⇑u)) := by
      ext t
      exact bandlimitedRepresentative_eq_fourierInv u t
    have hmemRep : MemLp (bandlimitedRepresentative B u) 2 volume := by
      change eLpNorm (bandlimitedRepresentative B u) 2 volume < ⊤
      rw [hrep, eLpNorm_fourierInv_eq hf1 hf2]
      exact hf2
    have hlpRep := lpNorm_eq_integral_norm_rpow_toReal (p := 2) (by simp) (by simp)
      hmemRep.aestronglyMeasurable
    have hlpCut := lpNorm_eq_integral_norm_rpow_toReal (p := 2) (by simp) (by simp)
      hf2.aestronglyMeasurable
    simp only [ENNReal.toReal_ofNat] at hlpRep hlpCut
    simp_rw [Real.rpow_two] at hlpRep hlpCut
    have hsame : lpNorm (bandlimitedRepresentative B u) 2 volume =
        lpNorm (bandCutoff B (⇑u)) 2 volume := by
      rw [hrep, lpNorm, lpNorm, eLpNorm_fourierInv_eq hf1 hf2]
    have hsq : (∫ t, ‖bandlimitedRepresentative B u t‖ ^ 2) ^ (2 : ℝ)⁻¹ =
        (∫ x, ‖bandCutoff B (⇑u) x‖ ^ 2) ^ (2 : ℝ)⁻¹ := by
      rw [← hlpRep, ← hlpCut, hsame]
    have hnn1 : 0 ≤ ∫ t, ‖bandlimitedRepresentative B u t‖ ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    have hnn2 : 0 ≤ ∫ x, ‖bandCutoff B (⇑u) x‖ ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num] at hsq
    have hsqrt : Real.sqrt (∫ t, ‖bandlimitedRepresentative B u t‖ ^ 2) =
        Real.sqrt (∫ x, ‖bandCutoff B (⇑u) x‖ ^ 2) := by
      simpa [Real.sqrt_eq_rpow] using hsq
    exact (Real.sqrt_inj hnn1 hnn2).mp hsqrt
  have hreal : ∫ t, ‖bandlimitedRepresentative B u t‖ ^ 2 =
      (2 * B)⁻¹ * ∑' k : ℤ, ‖bandlimitedRepresentative B u (k / (2 * B))‖ ^ 2 := by
    rw [hplan, htsum]
    have hB0 : (2 * B : ℝ) ≠ 0 := mul_ne_zero two_ne_zero (ne_of_gt hB)
    field_simp [hB0]
  have hint : Integrable fun t => ‖bandlimitedRepresentative B u t‖ ^ 2 := by
    have hmem : MemLp (bandlimitedRepresentative B u) 2 volume := by
      have hfun : bandlimitedRepresentative B u = 𝓕⁻ (bandCutoff B (⇑u)) := by
        ext t
        exact bandlimitedRepresentative_eq_fourierInv u t
      change eLpNorm (bandlimitedRepresentative B u) 2 volume < ⊤
      rw [hfun, eLpNorm_fourierInv_eq hf1 hf2]
      exact hf2
    simpa [ENNReal.toReal_ofNat, Real.rpow_two] using
      hmem.integrable_norm_rpow (p := 2) (by simp) (by simp)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => sq_nonneg _)]
  rw [hreal, ENNReal.ofReal_mul (inv_nonneg.mpr (mul_nonneg two_pos.le hB.le)),
    ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hsumm]

end CKMA
