/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Fourier.CircleSummation

/-!
# Convergence of Fejer means

Fejer means of an integrable function on the probability circle converge uniformly
when the function is continuous, in every finite `Lᵖ` norm, and pointwise at every
circle Lebesgue point.

Source: GAPS 27.17.
-/

@[expose] public section

noncomputable section

namespace CKMA

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal Real ComplexConjugate

local instance : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩

local notation "𝕋" => AddCircle (1 : ℝ)

local notation "haar" => AddCircle.haarAddCircle (T := 1)

/-! ### Convergence of Fejer means -/

/-- The kernel times the absolute oscillation is integrable. -/
private lemma integrable_fejerKernel_mul_norm_sub {f : 𝕋 → ℂ} (hf : Integrable f haar)
    (N : ℕ) (x : 𝕋) :
    Integrable (fun t : 𝕋 => fejerKernel N t * ‖f (x - t) - f x‖) haar := by
  have hshift : Integrable (fun t : 𝕋 => f (x - t)) haar := hf.comp_sub_left x
  have hker : AEStronglyMeasurable (fun t : 𝕋 => (fejerKernel N t : ℂ)) haar :=
    (Complex.continuous_ofReal.comp (continuous_fejerKernel N)).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂haar, ‖(fejerKernel N t : ℂ)‖ ≤ (N + 1 : ℝ) :=
    ae_of_all _ fun t => by
      rw [Complex.norm_real, Real.norm_of_nonneg (fejerKernel_nonneg N t)]
      exact fejerKernel_le_succ N t
  have hint1 : Integrable (fun t => (fejerKernel N t : ℂ) * f (x - t)) haar :=
    hshift.bdd_mul hker hbound
  have hint2 : Integrable (fun t => (fejerKernel N t : ℂ) * f x) haar :=
    (integrable_of_continuous
      (Complex.continuous_ofReal.comp (continuous_fejerKernel N))).mul_const (f x)
  have hint : Integrable (fun t => (fejerKernel N t : ℂ) * (f (x - t) - f x)) haar :=
    (hint1.sub hint2).congr <| ae_of_all _ fun t => by
      simp only [Pi.sub_apply]
      rw [← mul_sub]
  exact hint.norm.congr <| ae_of_all _ fun t => by
    dsimp
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (fejerKernel_nonneg N t)]

/-- A Fejer mean stays within the kernel convolution of the absolute oscillation. -/
private lemma norm_fejerMean_sub_le_integral {f : 𝕋 → ℂ} (hf : Integrable f haar) (N : ℕ)
    (x : 𝕋) :
    ‖fejerMean f N x - f x‖ ≤ ∫ t, fejerKernel N t * ‖f (x - t) - f x‖ ∂haar := by
  rw [fejerMean_sub_eq_conv hf N x]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  exact integral_congr_ae <| ae_of_all _ fun t => by
    dsimp
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (fejerKernel_nonneg N t)]

/-- Continuous circle functions have uniformly convergent Fejer means. -/
theorem fejerMean_tendstoUniformly {f : AddCircle (1 : ℝ) → ℂ} (hf : Continuous f) :
    TendstoUniformly (fun N x ↦ fejerMean f N x) f atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have huc : UniformContinuous f := CompactSpace.uniformContinuous_of_continuous hf
  obtain ⟨δ, hδ, hdist⟩ :=
    (Metric.uniformContinuous_iff_le).1 huc (ε / 2) (half_pos hε)
  let F : BoundedContinuousFunction 𝕋 ℂ :=
    BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩
  have hF : ∀ y, ‖f y‖ ≤ ‖F‖ := fun y => by
    simpa [F, BoundedContinuousFunction.mkOfCompact_apply] using F.norm_coe_le_norm y
  have hη : 0 < ε / (2 * (2 * ‖F‖ + 1)) := by positivity
  have htail := tendsto_fejerKernel_tail hδ
  rw [Metric.tendsto_nhds] at htail
  have hkerTail : ∀ᶠ N in atTop,
      ∫ y in {y : 𝕋 | δ ≤ ‖y‖}, fejerKernel N y ∂haar <
        ε / (2 * (2 * ‖F‖ + 1)) := by
    filter_upwards [htail (ε / (2 * (2 * ‖F‖ + 1))) hη] with N hN
    have hs0 : MeasurableSet {y : 𝕋 | δ ≤ ‖y‖} :=
      measurableSet_le measurable_const continuous_norm.measurable
    have hnn := setIntegral_nonneg (μ := haar) hs0 fun y _ => fejerKernel_nonneg N y
    rwa [Real.dist_0_eq_abs, abs_of_nonneg hnn] at hN
  filter_upwards [hkerTail] with N hN x
  have hintf : Integrable f haar := integrable_of_continuous hf
  let s : Set 𝕋 := {y | δ ≤ ‖y‖}
  have hs : MeasurableSet s := measurableSet_le measurable_const continuous_norm.measurable
  let φ : 𝕋 → ℝ := fun t => fejerKernel N t * ‖f (x - t) - f x‖
  have hφ : Integrable φ haar := integrable_fejerKernel_mul_norm_sub hintf N x
  have hnearK : ∫ t in sᶜ, fejerKernel N t ∂haar ≤ 1 := by
    calc
      ∫ t in sᶜ, fejerKernel N t ∂haar ≤ ∫ t, fejerKernel N t ∂haar :=
        setIntegral_le_integral (integrable_fejerKernel N)
          (ae_of_all _ (fejerKernel_nonneg N))
      _ = 1 := integral_fejerKernel N
  have hnear : ∫ t in sᶜ, φ t ∂haar ≤ ε / 2 := by
    have hpt : ∀ t ∈ sᶜ, φ t ≤ (ε / 2) * fejerKernel N t := by
      intro t ht
      have hlt : ‖t‖ < δ := lt_of_not_ge <| by
        simpa [s, Set.mem_compl_iff, Set.mem_ofPred_eq] using ht
      have hosc : ‖f (x - t) - f x‖ ≤ ε / 2 := by
        have hleδ : dist (x - t) x ≤ δ := by
          rw [dist_eq_norm]
          have hsub : (x - t) - x = -t := by abel
          rw [hsub, norm_neg]
          exact hlt.le
        have hdu := hdist hleδ
        rwa [dist_eq_norm] at hdu
      calc
        φ t = fejerKernel N t * ‖f (x - t) - f x‖ := rfl
        _ ≤ fejerKernel N t * (ε / 2) :=
          mul_le_mul_of_nonneg_left hosc (fejerKernel_nonneg N t)
        _ = (ε / 2) * fejerKernel N t := by ring
    have hintMul : IntegrableOn (fun t => (ε / 2) * fejerKernel N t) sᶜ haar :=
      ((integrable_fejerKernel N).const_mul (ε / 2)).integrableOn
    have hmono := setIntegral_mono_on (μ := haar) hφ.integrableOn hintMul
      hs.compl hpt
    have hfac : ∫ t in sᶜ, (ε / 2) * fejerKernel N t ∂haar =
        (ε / 2) * ∫ t in sᶜ, fejerKernel N t ∂haar := by
      rw [← integral_indicator hs.compl, ← integral_indicator hs.compl]
      have hfun : (sᶜ.indicator fun t => (ε / 2) * fejerKernel N t) =
          fun t => (ε / 2) * sᶜ.indicator (fejerKernel N) t := by
        funext t
        exact Set.indicator_const_mul sᶜ (fejerKernel N) (ε / 2) t
      rw [hfun, integral_const_mul]
    calc
      ∫ t in sᶜ, φ t ∂haar ≤ ∫ t in sᶜ, (ε / 2) * fejerKernel N t ∂haar := hmono
      _ = (ε / 2) * ∫ t in sᶜ, fejerKernel N t ∂haar := hfac
      _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left hnearK (by positivity)
      _ = ε / 2 := mul_one _
  have hfarI : (2 * ‖F‖) * ∫ t in s, fejerKernel N t ∂haar < ε / 2 := by
    by_cases hC0 : ‖F‖ = 0
    · rw [hC0, mul_zero, zero_mul]
      exact half_pos hε
    · have hCpos : 0 < ‖F‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hC0)
      have hstrict : (2 * ‖F‖) * ∫ t in s, fejerKernel N t ∂haar <
          (2 * ‖F‖) * (ε / (2 * (2 * ‖F‖ + 1))) :=
        mul_lt_mul_of_pos_left hN (mul_pos two_pos hCpos)
      have hle : (2 * ‖F‖) * (ε / (2 * (2 * ‖F‖ + 1))) ≤ ε / 2 := by
        have hfrac : ‖F‖ / (2 * ‖F‖ + 1) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          linarith
        have hid : (2 * ‖F‖) * (ε / (2 * (2 * ‖F‖ + 1))) =
            ε * (‖F‖ / (2 * ‖F‖ + 1)) := by
          field_simp
        rw [hid]
        calc
          ε * (‖F‖ / (2 * ‖F‖ + 1)) ≤ ε * (1 / 2) :=
            mul_le_mul_of_nonneg_left hfrac hε.le
          _ = ε / 2 := by ring
      exact hstrict.trans_le hle
  have hfar : ∫ t in s, φ t ∂haar < ε / 2 := by
    have hpt : ∀ t ∈ s, φ t ≤ (2 * ‖F‖) * fejerKernel N t := by
      intro t _
      have hdiff : ‖f (x - t) - f x‖ ≤ 2 * ‖F‖ := by
        calc
          ‖f (x - t) - f x‖ ≤ ‖f (x - t)‖ + ‖f x‖ := norm_sub_le _ _
          _ ≤ ‖F‖ + ‖F‖ := add_le_add (hF _) (hF _)
          _ = 2 * ‖F‖ := by ring
      calc
        φ t = fejerKernel N t * ‖f (x - t) - f x‖ := rfl
        _ ≤ fejerKernel N t * (2 * ‖F‖) :=
          mul_le_mul_of_nonneg_left hdiff (fejerKernel_nonneg N t)
        _ = (2 * ‖F‖) * fejerKernel N t := by ring
    have hintMul : IntegrableOn (fun t => (2 * ‖F‖) * fejerKernel N t) s haar :=
      ((integrable_fejerKernel N).const_mul (2 * ‖F‖)).integrableOn
    have hmono := setIntegral_mono_on (μ := haar) hφ.integrableOn hintMul hs hpt
    have hfac : ∫ t in s, (2 * ‖F‖) * fejerKernel N t ∂haar =
        (2 * ‖F‖) * ∫ t in s, fejerKernel N t ∂haar := by
      rw [← integral_indicator hs, ← integral_indicator hs]
      have hfun : (s.indicator fun t => (2 * ‖F‖) * fejerKernel N t) =
          fun t => (2 * ‖F‖) * s.indicator (fejerKernel N) t := by
        funext t
        exact Set.indicator_const_mul s (fejerKernel N) (2 * ‖F‖) t
      rw [hfun, integral_const_mul]
    exact lt_of_le_of_lt (hmono.trans_eq hfac) hfarI
  have hsum : ∫ t, φ t ∂haar < ε := by
    calc
      ∫ t, φ t ∂haar = ∫ t in s, φ t ∂haar + ∫ t in sᶜ, φ t ∂haar :=
        (integral_add_compl hs hφ).symm
      _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le hfar hnear
      _ = ε := add_halves ε
  rw [dist_eq_norm, norm_sub_rev]
  exact lt_of_le_of_lt (norm_fejerMean_sub_le_integral hintf N x) hsum

/-- Fejer means are linear on integrable functions. -/
private lemma fejerMean_sub {f g : 𝕋 → ℂ} (hf : Integrable f haar) (hg : Integrable g haar)
    (N : ℕ) (x : 𝕋) :
    fejerMean (f - g) N x = fejerMean f N x - fejerMean g N x := by
  have hcoeff : ∀ k, fourierCoeff (f - g) k = fourierCoeff f k - fourierCoeff g k := by
    intro k
    have hpt : ∀ t, fourier (-k) t • (f - g) t =
        fourier (-k) t • f t - fourier (-k) t • g t := fun t => by
      simp only [Pi.sub_apply, smul_sub]
    simp_rw [fourierCoeff, hpt]
    exact integral_sub (hf.fourier_smul (-k)) (hg.fourier_smul (-k))
  have halg : ∀ (w a b z : ℂ), w * (a - b) * z = w * a * z - w * b * z :=
    set_option backward.isDefEq.respectTransparency true in by
      intro w a b z
      ring
  rw [fejerMean_eq_weighted, fejerMean_eq_weighted, fejerMean_eq_weighted]
  simp_rw [hcoeff, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => halg _ _ _ _

/-- Fejer means depend on the integrand only almost everywhere. -/
private lemma fejerMean_congr_ae {f g : 𝕋 → ℂ} (h : f =ᵐ[haar] g) (N : ℕ) :
    fejerMean f N = fejerMean g N := by
  ext x
  simp_rw [fejerMean_eq_weighted, fourierCoeff_congr_ae h]

/-- A Fejer mean is continuous, as a finite sum of characters. -/
private lemma continuous_fejerMean (f : 𝕋 → ℂ) (N : ℕ) : Continuous (fejerMean f N) := by
  have hfun : fejerMean f N = fun x =>
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (1 - (k.natAbs : ℂ) / (N + 1)) * fourierCoeff f k * fourier k x := by
    ext x
    exact fejerMean_eq_weighted f N x
  rw [hfun]
  exact continuous_finsetSum _ fun _ _ => continuous_const.mul (map_continuous (fourier _))

/-- Translation against the Fejer kernel preserves the Lebesgue integral. -/
private lemma lintegral_fejerKernel_shift (N : ℕ) {φ : 𝕋 → ℝ≥0∞}
    (hφ : AEMeasurable φ haar) :
    ∫⁻ x, ∫⁻ t, ENNReal.ofReal (fejerKernel N t) * φ (x - t) ∂haar ∂haar =
      ∫⁻ x, φ x ∂haar := by
  have hK : AEMeasurable (fun t : 𝕋 => ENNReal.ofReal (fejerKernel N t)) haar :=
    (ENNReal.continuous_ofReal.comp (continuous_fejerKernel N)).aemeasurable
  have hpair : AEMeasurable (fun p : 𝕋 × 𝕋 =>
      ENNReal.ofReal (fejerKernel N p.2) * φ (p.1 - p.2)) (Measure.prod haar haar) := by
    refine hK.comp_snd.mul ?_
    exact hφ.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub (μ := haar) (ν := haar))
  rw [lintegral_lintegral_swap (f := fun x t =>
      ENNReal.ofReal (fejerKernel N t) * φ (x - t)) hpair]
  have hinner : ∀ t, ∫⁻ x, ENNReal.ofReal (fejerKernel N t) * φ (x - t) ∂haar =
      ENNReal.ofReal (fejerKernel N t) * ∫⁻ x, φ x ∂haar := by
    intro t
    have hshift : AEMeasurable (fun x => φ (x + -t)) haar :=
      hφ.comp_quasiMeasurePreserving (quasiMeasurePreserving_add_right haar (-t))
    simp_rw [sub_eq_add_neg]
    rw [lintegral_const_mul'' _ hshift, lintegral_add_right_eq_self]
  simp_rw [hinner]
  rw [lintegral_mul_const'' _ hK, lintegral_fejerKernel, one_mul]

/-- Hölder splitting of a nonnegative kernel of mass one. -/
private lemma lintegral_kernel_holder {N : ℕ} {q : ℝ} (hq : 1 < q) {g : 𝕋 → ℝ≥0∞}
    (hg : Measurable g) (x : 𝕋) :
    (∫⁻ t, ENNReal.ofReal (fejerKernel N t) * g (x - t) ∂haar) ^ q ≤
      ∫⁻ t, ENNReal.ofReal (fejerKernel N t) * g (x - t) ^ q ∂haar := by
  let K : 𝕋 → ℝ≥0∞ := fun t => ENNReal.ofReal (fejerKernel N t)
  let r : ℝ := Real.conjExponent q
  have hrq : r.HolderConjugate q := (Real.HolderConjugate.conjExponent hq).symm
  have hr0 : r ≠ 0 := hrq.ne_zero
  have hq0 : q ≠ 0 := hrq.symm.ne_zero
  let f1 : 𝕋 → ℝ≥0∞ := fun t => K t ^ (1 / r)
  let f2 : 𝕋 → ℝ≥0∞ := fun t => K t ^ (1 / q) * g (x - t)
  have hK : Measurable K :=
    (ENNReal.continuous_ofReal.comp (continuous_fejerKernel N)).measurable
  have hgx : Measurable fun t => g (x - t) :=
    hg.comp (measurable_id.const_sub x)
  have hf1 : AEMeasurable f1 haar := (hK.pow_const _).aemeasurable
  have hf2 : AEMeasurable f2 haar := ((hK.pow_const _).mul hgx).aemeasurable
  have hprod : ∀ t, f1 t * f2 t = K t * g (x - t) := by
    intro t
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ hrq.one_div_nonneg hrq.symm.one_div_nonneg]
    have hsum : 1 / r + 1 / q = 1 := by simpa [one_div] using hrq.inv_add_inv_eq_one
    rw [hsum, ENNReal.rpow_one]
  have hpow1 : ∀ t, f1 t ^ r = K t := by
    intro t
    rw [← ENNReal.rpow_mul]
    exact congrArg (fun e => K t ^ e) (div_mul_cancel₀ (1 : ℝ) hr0) |>.trans (ENNReal.rpow_one _)
  have hpow2 : ∀ t, f2 t ^ q = K t * g (x - t) ^ q := by
    intro t
    rw [ENNReal.mul_rpow_of_nonneg _ _ (zero_le_one.trans hq.le), ← ENNReal.rpow_mul]
    exact congrArg (fun e => K t ^ e * g (x - t) ^ q)
      (div_mul_cancel₀ (1 : ℝ) hq0) |>.trans (by rw [ENNReal.rpow_one])
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq haar hrq hf1 hf2
  simp_rw [Pi.mul_apply] at hholder
  rw [lintegral_congr hprod, lintegral_congr hpow1, lintegral_congr hpow2,
    lintegral_fejerKernel, ENNReal.one_rpow, one_mul] at hholder
  have hqq : (1 / q) * q = 1 := div_mul_cancel₀ (1 : ℝ) hq0
  have hraise := ENNReal.rpow_le_rpow hholder (zero_le_one.trans hq.le)
  rw [← ENNReal.rpow_mul, hqq, ENNReal.rpow_one] at hraise
  exact hraise

/-- Pointwise size of a Fejer mean by the kernel convolution. -/
private lemma enorm_fejerMean_le {f : 𝕋 → ℂ} (hf : Integrable f haar) (N : ℕ) (x : 𝕋) :
    ‖fejerMean f N x‖ₑ ≤
      ∫⁻ t, ENNReal.ofReal (fejerKernel N t) * ‖f (x - t)‖ₑ ∂haar := by
  rw [fejerMean_eq_conv hf N x]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  refine lintegral_congr fun t => ?_
  rw [enorm_mul, ← ofReal_norm, Complex.norm_real,
    Real.norm_of_nonneg (fejerKernel_nonneg N t)]

/-- Fejer means contract the finite `L^p` norm. -/
private lemma eLpNorm_fejerMean_le {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p < ∞)
    {f : 𝕋 → ℂ} (hf : MemLp f p haar) (N : ℕ) :
    eLpNorm (fejerMean f N) p haar ≤ eLpNorm f p haar := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hfi : Integrable f haar := hf.integrable hp
  let g : 𝕋 → ℂ := hf.aestronglyMeasurable.mk f
  have hg_meas : Measurable g := hf.aestronglyMeasurable.measurable_mk
  have hg_ae : f =ᵐ[haar] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg_int : Integrable g haar := hfi.congr hg_ae
  have hg_mem : MemLp g p haar := hf.ae_eq hg_ae
  rw [fejerMean_congr_ae hg_ae N, eLpNorm_congr_ae hg_ae]
  have hASM : AEStronglyMeasurable (fejerMean g N) haar :=
    (continuous_fejerMean g N).aestronglyMeasurable
  have hgnorm : Measurable fun x => ‖g x‖ₑ :=
    continuous_enorm.measurable.comp hg_meas
  rcases lt_or_eq_of_le hp with hplt | hp1
  · have hq : 1 < p.toReal := by
      rw [← ENNReal.toReal_one]
      exact (ENNReal.toReal_lt_toReal (by simp) hpt.ne).mpr hplt
    have hpoint : ∀ x, ‖fejerMean g N x‖ₑ ^ p.toReal ≤
        ∫⁻ t, ENNReal.ofReal (fejerKernel N t) * ‖g (x - t)‖ₑ ^ p.toReal ∂haar := by
      intro x
      refine (ENNReal.rpow_le_rpow (enorm_fejerMean_le hg_int N x)
        (zero_le_one.trans hq.le)).trans ?_
      exact lintegral_kernel_holder hq hgnorm x
    have hint : ∫⁻ x, ‖fejerMean g N x‖ₑ ^ p.toReal ∂haar ≤
        ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂haar := by
      calc
        ∫⁻ x, ‖fejerMean g N x‖ₑ ^ p.toReal ∂haar
            ≤ ∫⁻ x, ∫⁻ t, ENNReal.ofReal (fejerKernel N t) *
                ‖g (x - t)‖ₑ ^ p.toReal ∂haar ∂haar := lintegral_mono hpoint
        _ = ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂haar :=
          lintegral_fejerKernel_shift N (hgnorm.pow_const _).aemeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt.ne hASM,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt.ne hg_mem.aestronglyMeasurable]
    exact ENNReal.rpow_le_rpow hint (by positivity)
  · rw [← hp1, eLpNorm_one_eq_lintegral_enorm hASM,
      eLpNorm_one_eq_lintegral_enorm hg_mem.aestronglyMeasurable]
    calc
      ∫⁻ x, ‖fejerMean g N x‖ₑ ∂haar
          ≤ ∫⁻ x, ∫⁻ t, ENNReal.ofReal (fejerKernel N t) * ‖g (x - t)‖ₑ ∂haar ∂haar :=
        lintegral_mono fun x => enorm_fejerMean_le hg_int N x
      _ = ∫⁻ x, ‖g x‖ₑ ∂haar := lintegral_fejerKernel_shift N hgnorm.aemeasurable

/-- **27.17**, the finite-p circle Fejer theorem. -/
theorem fejerMean_tendsto_Lp {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p < ∞)
    {f : AddCircle (1 : ℝ) → ℂ} (hf : MemLp f p AddCircle.haarAddCircle) :
    Tendsto (fun N ↦ eLpNorm (fun x ↦ fejerMean f N x - f x) p AddCircle.haarAddCircle)
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact Eventually.of_forall fun _ => le_top
  have hε3 : 0 < ε / 3 := ENNReal.div_pos hε.ne' (by simp)
  obtain ⟨g, hgLp, hgMem⟩ := hf.exists_boundedContinuous_eLpNorm_sub_le hpt.ne hε3.ne'
  have hintf : Integrable f haar := hf.integrable hp
  have hintg : Integrable (g : 𝕋 → ℂ) haar := integrable_of_continuous g.continuous
  have hdiffMem : MemLp (f - (g : 𝕋 → ℂ)) p haar := hf.sub hgMem
  have hgu := fejerMean_tendstoUniformly g.continuous
  rw [Metric.tendstoUniformly_iff] at hgu
  have hη : 0 < (ε / 3).toReal :=
    ENNReal.toReal_pos hε3.ne' (ENNReal.div_lt_top hεtop (by simp)).ne
  filter_upwards [hgu _ hη] with N hN
  have halg : ∀ (a b c d : ℂ), (a - b - (c - d)) + (b - d) = a - c :=
    set_option backward.isDefEq.respectTransparency true in by
      intro a b c d
      abel
  have hdecomp : (fun x => fejerMean f N x - f x) =
      (fun x => fejerMean (f - (g : 𝕋 → ℂ)) N x - ((f - (g : 𝕋 → ℂ)) x)) +
        fun x => fejerMean (g : 𝕋 → ℂ) N x - g x := by
    ext x
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [fejerMean_sub hintf hintg N x]
    exact (halg _ _ _ _).symm
  have hsplit : eLpNorm (fun x => fejerMean f N x - f x) p haar ≤
      eLpNorm (fun x => fejerMean (f - (g : 𝕋 → ℂ)) N x - (f - (g : 𝕋 → ℂ)) x) p haar +
        eLpNorm (fun x => fejerMean (g : 𝕋 → ℂ) N x - g x) p haar := by
    rw [hdecomp]
    exact eLpNorm_add_le (p := p) (μ := haar) hp
  have hrest : eLpNorm (fun x =>
      fejerMean (f - (g : 𝕋 → ℂ)) N x - (f - (g : 𝕋 → ℂ)) x) p haar ≤
      ε / 3 + ε / 3 := by
    have hfun : (fun x => fejerMean (f - (g : 𝕋 → ℂ)) N x - (f - (g : 𝕋 → ℂ)) x) =
        fun x => fejerMean (f - (g : 𝕋 → ℂ)) N x + (-((f - (g : 𝕋 → ℂ)) x)) := by
      ext x
      rw [sub_eq_add_neg]
    have hnegfun : -(f - (g : 𝕋 → ℂ)) = fun x => -((f - (g : 𝕋 → ℂ)) x) := by
      ext x
      simp [Pi.neg_apply]
    rw [hfun]
    calc
      eLpNorm (fun x => fejerMean (f - (g : 𝕋 → ℂ)) N x +
          (-((f - (g : 𝕋 → ℂ)) x))) p haar
          ≤ eLpNorm (fejerMean (f - (g : 𝕋 → ℂ)) N) p haar +
            eLpNorm (fun x => -((f - (g : 𝕋 → ℂ)) x)) p haar :=
        eLpNorm_add_le (p := p) (μ := haar) hp
      _ = eLpNorm (fejerMean (f - (g : 𝕋 → ℂ)) N) p haar +
          eLpNorm (f - (g : 𝕋 → ℂ)) p haar := by
        rw [← hnegfun, eLpNorm_neg]
      _ ≤ eLpNorm (f - (g : 𝕋 → ℂ)) p haar + eLpNorm (f - (g : 𝕋 → ℂ)) p haar :=
        add_le_add (eLpNorm_fejerMean_le hp hpt hdiffMem N) le_rfl
      _ ≤ ε / 3 + ε / 3 := add_le_add hgLp hgLp
  have happ : eLpNorm (fun x => fejerMean (g : 𝕋 → ℂ) N x - g x) p haar ≤ ε / 3 := by
    have hleη : ∀ x, ‖fejerMean (g : 𝕋 → ℂ) N x - g x‖ ≤ (ε / 3).toReal := by
      intro x
      have hlt := hN x
      rw [dist_eq_norm, norm_sub_rev] at hlt
      exact hlt.le
    have hasm : AEStronglyMeasurable (fun x => fejerMean (g : 𝕋 → ℂ) N x - g x) haar :=
      ((continuous_fejerMean (g : 𝕋 → ℂ) N).sub g.continuous).aestronglyMeasurable
    have hbound := eLpNorm_le_of_ae_bound (μ := haar) (p := p) hasm (ae_of_all _ hleη)
    calc
      eLpNorm (fun x => fejerMean (g : 𝕋 → ℂ) N x - g x) p haar
          ≤ haar Set.univ ^ (p.toReal)⁻¹ * ENNReal.ofReal ((ε / 3).toReal) := hbound
      _ = 1 ^ (p.toReal)⁻¹ * (ε / 3) := by
        rw [measure_univ, ENNReal.ofReal_toReal (ENNReal.div_lt_top hεtop (by simp)).ne]
      _ = ε / 3 := by rw [ENNReal.one_rpow, one_mul]
  have hsum : eLpNorm (fun x => fejerMean f N x - f x) p haar ≤
      ε / 3 + ε / 3 + ε / 3 := by
    calc
      eLpNorm (fun x => fejerMean f N x - f x) p haar
          ≤ eLpNorm (fun x => fejerMean (f - (g : 𝕋 → ℂ)) N x -
              (f - (g : 𝕋 → ℂ)) x) p haar +
            eLpNorm (fun x => fejerMean (g : 𝕋 → ℂ) N x - g x) p haar := hsplit
      _ ≤ ε / 3 + ε / 3 + ε / 3 := add_le_add hrest happ
  calc
    eLpNorm (fun x => fejerMean f N x - f x) p haar ≤ ε / 3 + ε / 3 + ε / 3 := hsum
    _ = 1 * (ε / 3) + 1 * (ε / 3) + 1 * (ε / 3) := by
      conv_lhs => rw [← one_mul (ε / 3)]
    _ = (1 + 1) * (ε / 3) + 1 * (ε / 3) := by
      conv_lhs => rw [← add_mul]
    _ = (1 + 1 + 1) * (ε / 3) := by
      conv_lhs => rw [← add_mul]
    _ = 3 * (ε / 3) := by
      have h3 : (1 + 1 + 1 : ℝ≥0∞) = 3 := by norm_num
      rw [h3]
    _ = (ε / 3) * 3 := mul_comm _ _
    _ = ε := ENNReal.div_mul_cancel (by simp) (by simp)

/-- Probability Haar integral equals the lift over `(-1/2, 1/2]`. -/
private lemma integral_haar_eq_intervalIntegral {g : 𝕋 → ℝ} :
    ∫ y, g y ∂haar = ∫ t in (-(1 / 2 : ℝ))..(1 / 2), g (t : 𝕋) := by
  rw [AddCircle.integral_haarAddCircle, inv_one, one_smul]
  rw [← AddCircle.intervalIntegral_preimage (T := 1) (-(1 / 2))]
  have hend : -(1 / 2 : ℝ) + 1 = 1 / 2 := by ring
  rw [hend]

/-- An integrable circle function lifts to an interval-integrable function on `[-1/2, 1/2]`. -/
private lemma intervalIntegrable_coe {g : 𝕋 → ℝ} (hg : Integrable g haar) :
    IntervalIntegrable (fun t : ℝ => g (t : 𝕋)) volume (-(1 / 2)) (1 / 2) := by
  have hgvol : Integrable g (volume : Measure 𝕋) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact (integrable_smul_measure (by simp) ENNReal.ofReal_ne_top).2 hg
  have hint :=
    ((AddCircle.measurePreserving_mk (T := 1) (-(1 / 2 : ℝ))).integrable_comp
      hgvol.aestronglyMeasurable).2 hgvol
  have hend : -(1 / 2 : ℝ) + 1 = 1 / 2 := by ring
  rw [hend] at hint
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)).2 hint

/-- The kernel times the forward oscillation is integrable. -/
private lemma integrable_fejerKernel_mul_norm_add {f : 𝕋 → ℂ} (hf : Integrable f haar)
    (N : ℕ) (x : 𝕋) :
    Integrable (fun t : 𝕋 => fejerKernel N t * ‖f (x + t) - f x‖) haar := by
  have hsub := integrable_fejerKernel_mul_norm_sub hf N x
  have hneg : Integrable (fun t => fejerKernel N (-t) * ‖f (x - -t) - f x‖) haar :=
    hsub.comp_neg
  exact hneg.congr <| ae_of_all _ fun t => by
    simp [fejerKernel_neg, sub_neg_eq_add]

/-- Evenness moves the oscillation estimate to the forward translate. -/
private lemma norm_fejerMean_sub_le_add {f : 𝕋 → ℂ} (hf : Integrable f haar) (N : ℕ)
    (x : 𝕋) :
    ‖fejerMean f N x - f x‖ ≤ ∫ t, fejerKernel N t * ‖f (x + t) - f x‖ ∂haar := by
  refine (norm_fejerMean_sub_le_integral hf N x).trans_eq ?_
  have hflip := integral_neg_eq_self
    (fun t => fejerKernel N t * ‖f (x - t) - f x‖) haar
  simp_rw [fejerKernel_neg, sub_neg_eq_add] at hflip
  exact hflip.symm

/-- The constant in one dyadic Fejer annulus. -/
private lemma fejer_annulus_const (N k : ℕ) (ε : ℝ) :
    (N + 1 : ℝ) / (4 * (4 : ℝ) ^ k) * (ε / 4) * (2 : ℝ) ^ (k + 1) / (N + 1) =
      (ε / 8) * (1 / 2) ^ k := by
  have hle : (k + 1) + (k + 1) = 2 + 2 * k := by omega
  have hpow : (2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ (2 + 2 * k) = (1 / 2) ^ (k + 1) := by
    have hne : (2 : ℝ) ^ (2 + 2 * k) ≠ 0 := by positivity
    apply (div_eq_iff hne).2
    have hcancel : (1 / 2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (k + 1) = 1 := by
      rw [← mul_pow, one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow]
    exact (calc
      (1 / 2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 + 2 * k)
          = (1 / 2 : ℝ) ^ (k + 1) * ((2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (k + 1)) := by
            rw [← pow_add, hle]
      _ = ((1 / 2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (k + 1)) * (2 : ℝ) ^ (k + 1) := by
            ring
      _ = 1 * (2 : ℝ) ^ (k + 1) := by rw [hcancel]
      _ = (2 : ℝ) ^ (k + 1) := one_mul _).symm
  have h4 : (4 : ℝ) * (4 : ℝ) ^ k = (2 : ℝ) ^ (2 + 2 * k) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul, ← pow_add]
  calc
    (N + 1 : ℝ) / (4 * (4 : ℝ) ^ k) * (ε / 4) * (2 : ℝ) ^ (k + 1) / (N + 1)
        = (ε / 4) * ((2 : ℝ) ^ (k + 1) / (4 * (4 : ℝ) ^ k)) := by
          field_simp
    _ = (ε / 4) * ((2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ (2 + 2 * k)) := by rw [h4]
    _ = (ε / 4) * (1 / 2) ^ (k + 1) := by rw [hpow]
    _ = (ε / 8) * (1 / 2) ^ k := by
      rw [pow_succ]
      ring

/-- On `(α, δ]`, the Fejer kernel integrates a controlled symmetric average below `ε / 4`. -/
private lemma integral_right_annulus_lt {φ : ℝ → ℝ} {ε δ α : ℝ} {N : ℕ}
    (hφ : ∀ t, 0 ≤ φ t)
    (hφint : IntervalIntegrable φ volume (-(1 / 2)) (1 / 2))
    (hε : 0 < ε) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hα0 : 0 < α) (hαδ : α < δ) (hα : α = 1 / (N + 1 : ℝ))
    (hsmall : ∀ r, 0 < r → r ≤ δ → ∫ t in (-r)..r, φ t < (ε / 4) * r) :
    ∫ t in α..δ, fejerKernelReal N t * φ t < ε / 4 := by
  let b : ℕ → ℝ := fun k => min δ ((2 : ℝ) ^ k * α)
  have hb0 : b 0 = α := by
    simp only [b, pow_zero, one_mul]
    exact min_eq_right hαδ.le
  have hbN : b N = δ := by
    have hpow : N < 2 ^ N := N.lt_two_pow_self
    have hle : (N + 1 : ℝ) ≤ (2 : ℝ) ^ N := by
      exact_mod_cast Nat.succ_le_of_lt hpow
    have hge : δ ≤ (2 : ℝ) ^ N * α := by
      rw [hα, mul_one_div, le_div_iff₀ (by positivity : 0 < (N + 1 : ℝ))]
      have hδ1 : δ ≤ 1 := hδhalf.trans (by norm_num)
      have hmul : δ * (N + 1) ≤ 1 * (N + 1) :=
        mul_le_mul_of_nonneg_right hδ1 (by positivity)
      rw [one_mul] at hmul
      exact hmul.trans hle
    simp [b, min_eq_left hge]
  have hbmono : ∀ k, b k ≤ b (k + 1) := by
    intro k
    simp only [b]
    exact min_le_min le_rfl <|
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two k.le_succ) hα0.le
  have hψint : IntervalIntegrable (fun t => fejerKernelReal N t * φ t) volume
      (-(1 / 2)) (1 / 2) :=
    hφint.continuousOn_mul (continuous_fejerKernelReal N).continuousOn
  have hpiece : ∀ k, IntervalIntegrable (fun t => fejerKernelReal N t * φ t) volume
      (b k) (b (k + 1)) := by
    intro k
    refine hψint.mono_set ?_
    rw [Set.uIcc_of_le (hbmono k),
      Set.uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)]
    refine Set.Icc_subset_Icc ?_ ?_
    · have hbk : 0 ≤ b k := by
        simp only [b]
        exact le_min hδ.le (mul_nonneg (pow_nonneg (by norm_num) _) hα0.le)
      linarith
    · have hbk : b (k + 1) ≤ δ := by simp [b]
      linarith
  have hintk : ∀ k ∈ Finset.range N,
      ∫ t in b k..b (k + 1), fejerKernelReal N t * φ t <
        (ε / 8) * (1 / 2) ^ k := by
    intro k hk
    by_cases hEq : b k = b (k + 1)
    · rw [hEq, intervalIntegral.integral_same]
      positivity
    · have hlt : b k < b (k + 1) := lt_of_le_of_ne (hbmono k) hEq
      have hbkδ : b k < δ := lt_of_lt_of_le hlt (by simp [b])
      have hαk : (2 : ℝ) ^ k * α < δ := by
        by_contra hge
        have hmin : b k = δ := by
          simp [b, min_eq_left (le_of_not_gt hge)]
        exact (hmin ▸ hbkδ).false
      have hbk : b k = (2 : ℝ) ^ k * α := by
        simp [b, min_eq_right hαk.le]
      have hbpos : 0 < b (k + 1) := lt_of_le_of_lt (by
        have : 0 ≤ b k := by rw [hbk]; positivity
        exact this) hlt
      have hbδ : b (k + 1) ≤ δ := by simp [b]
      have hC : ∀ t ∈ Set.Icc (b k) (b (k + 1)),
          fejerKernelReal N t ≤ (N + 1 : ℝ) / (4 * (4 : ℝ) ^ k) := by
        intro t ht
        have ht0 : t ≠ 0 := by
          have : 0 < b k := by rw [hbk]; positivity
          exact ne_of_gt (lt_of_lt_of_le this ht.1)
        have htabs : |t| ≤ 1 / 2 := by
          rw [abs_of_nonneg (le_trans (by
            have : 0 ≤ b k := by rw [hbk]; positivity
            exact this) ht.1)]
          exact le_trans ht.2 (hbδ.trans hδhalf)
        have hinv : fejerKernelReal N t ≤ 1 / (4 * (N + 1) * t ^ 2) :=
          fejerKernelReal_le_inv_sq ht0 htabs
        have ht2 : b k ^ 2 ≤ t ^ 2 :=
          pow_le_pow_left₀ (by rw [hbk]; positivity) ht.1 2
        have hden : 4 * (N + 1 : ℝ) * b k ^ 2 ≤ 4 * (N + 1) * t ^ 2 :=
          mul_le_mul_of_nonneg_left ht2 (by positivity)
        have hleC : 1 / (4 * (N + 1) * t ^ 2) ≤ 1 / (4 * (N + 1) * b k ^ 2) :=
          (one_div_le_one_div (by positivity) (by positivity)).2 hden
        have hbkC : 1 / (4 * (N + 1) * b k ^ 2) =
            (N + 1 : ℝ) / (4 * (4 : ℝ) ^ k) := by
          have hfour : (4 : ℝ) ^ k = (2 : ℝ) ^ (2 * k) := by
            rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul]
          rw [hbk, hα, mul_pow, ← pow_mul, hfour]
          field_simp
          ring
        exact hinv.trans (hleC.trans_eq hbkC)
      have hφk : IntervalIntegrable φ volume (b k) (b (k + 1)) := by
        refine hφint.mono_set ?_
        rw [Set.uIcc_of_le hlt.le,
          Set.uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)]
        refine Set.Icc_subset_Icc (by
          have : 0 ≤ b k := by rw [hbk]; positivity
          linarith) (by linarith [hbδ, hδhalf])
      have hprod : IntervalIntegrable (fun t => fejerKernelReal N t * φ t) volume
          (b k) (b (k + 1)) := hpiece k
      have hconst : IntervalIntegrable
          (fun t => (N + 1 : ℝ) / (4 * (4 : ℝ) ^ k) * φ t) volume
          (b k) (b (k + 1)) := hφk.const_mul _
      have hle : ∫ t in b k..b (k + 1), fejerKernelReal N t * φ t ≤
          (N + 1 : ℝ) / (4 * (4 : ℝ) ^ k) * ∫ t in b k..b (k + 1), φ t := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_mono_on hlt.le hprod hconst fun t ht =>
          mul_le_mul_of_nonneg_right (hC t ht) (hφ t)
      have hneg : -b (k + 1) ≤ b k := by
        have hbk0 : 0 ≤ b k := by rw [hbk]; positivity
        linarith
      have hsym : ∫ t in b k..b (k + 1), φ t ≤ ∫ t in (-b (k + 1))..b (k + 1), φ t :=
        intervalIntegral.integral_mono_interval hneg hlt.le le_rfl
          (ae_restrict_of_ae (ae_of_all _ hφ))
          (hφint.mono_set (by
            rw [Set.uIcc_of_le (by linarith [hbpos] : -b (k + 1) ≤ b (k + 1)),
              Set.uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)]
            refine Set.Icc_subset_Icc ?_ ?_
            · linarith [hbδ, hδhalf]
            · linarith [hbδ, hδhalf]))
      have hintφ : ∫ t in (-b (k + 1))..b (k + 1), φ t < (ε / 4) * b (k + 1) :=
        hsmall _ hbpos hbδ
      have hCpos : 0 < (N + 1 : ℝ) / (4 * (4 : ℝ) ^ k) := by positivity
      have hstrict : (N + 1 : ℝ) / (4 * (4 : ℝ) ^ k) *
          ∫ t in (-b (k + 1))..b (k + 1), φ t <
          (N + 1 : ℝ) / (4 * (4 : ℝ) ^ k) * ((ε / 4) * b (k + 1)) :=
        mul_lt_mul_of_pos_left hintφ hCpos
      have hbpow : b (k + 1) ≤ (2 : ℝ) ^ (k + 1) * α := by simp [b]
      have hcoef : 0 ≤ (N + 1 : ℝ) / (4 * (4 : ℝ) ^ k) * (ε / 4) := by positivity
      have hlast : (N + 1 : ℝ) / (4 * (4 : ℝ) ^ k) * ((ε / 4) * b (k + 1)) ≤
          (ε / 8) * (1 / 2) ^ k := by
        calc
          (N + 1 : ℝ) / (4 * (4 : ℝ) ^ k) * ((ε / 4) * b (k + 1))
              ≤ (N + 1 : ℝ) / (4 * (4 : ℝ) ^ k) * ((ε / 4) * ((2 : ℝ) ^ (k + 1) * α)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbpow (by positivity))
                  (by positivity)
          _ = (N + 1 : ℝ) / (4 * (4 : ℝ) ^ k) * (ε / 4) * (2 : ℝ) ^ (k + 1) * α := by
            ring
          _ = (ε / 8) * (1 / 2) ^ k := by
            rw [hα]
            simpa [div_eq_mul_inv, one_mul, mul_assoc] using fejer_annulus_const N k ε
      exact lt_of_le_of_lt (hle.trans (mul_le_mul_of_nonneg_left hsym (by positivity)))
        (hstrict.trans_le hlast)
  have hNpos : 0 < N := by
    have hhalf : α < 1 / 2 := hαδ.trans_le hδhalf
    rw [hα] at hhalf
    have hlt : (2 : ℝ) < N + 1 := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hhalf
      linarith
    have hnat : 2 < N + 1 := by exact_mod_cast hlt
    omega
  have hsum : ∑ k ∈ Finset.range N,
      ∫ t in b k..b (k + 1), fejerKernelReal N t * φ t <
      ∑ k ∈ Finset.range N, (ε / 8) * (1 / 2) ^ k :=
    Finset.sum_lt_sum_of_nonempty (by
      rw [Finset.nonempty_range_iff]
      exact hNpos.ne') hintk
  have hadj : ∑ k ∈ Finset.range N,
      ∫ t in b k..b (k + 1), fejerKernelReal N t * φ t =
      ∫ t in b 0..b N, fejerKernelReal N t * φ t :=
    intervalIntegral.sum_integral_adjacent_intervals fun k _ => hpiece k
  rw [hadj, hb0, hbN] at hsum
  have hgeom : ∑ k ∈ Finset.range N, (ε / 8) * (1 / 2 : ℝ) ^ k < ε / 4 := by
    rw [← Finset.mul_sum]
    have hsum2 : ∑ k ∈ Finset.range N, ((1 : ℝ) / 2) ^ k < 2 := by
      rw [geom_sum_eq (by norm_num : (1 : ℝ) / 2 ≠ 1) N]
      have : ((1 / 2 : ℝ) ^ N - 1) / (1 / 2 - 1) = 2 * (1 - (1 / 2) ^ N) := by ring
      rw [this]
      have hpos : 0 < ((1 : ℝ) / 2) ^ N := by positivity
      linarith
    calc
      (ε / 8) * ∑ k ∈ Finset.range N, ((1 : ℝ) / 2) ^ k < (ε / 8) * 2 :=
        mul_lt_mul_of_pos_left hsum2 (by positivity)
      _ = ε / 4 := by ring
  exact hsum.trans hgeom

/-- Nonnegative densities with vanishing symmetric averages are concentrated by the Fejer kernel. -/
private lemma tendsto_integral_fejerKernelReal_mul {φ : ℝ → ℝ} (hφ : ∀ t, 0 ≤ φ t)
    (hφint : IntervalIntegrable φ volume (-(1 / 2)) (1 / 2))
    (hφavg : Tendsto (fun r : ℝ => (2 * r)⁻¹ * ∫ t in (-r)..r, φ t) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun N : ℕ => ∫ t in (-(1 / 2))..(1 / 2), fejerKernelReal N t * φ t)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε8 : 0 < ε / 8 := by positivity
  rw [Metric.tendsto_nhds] at hφavg
  have hnear := hφavg (ε / 8) hε8
  rw [eventually_nhdsWithin_iff] at hnear
  obtain ⟨η, hη, hηφ⟩ := Metric.eventually_nhds_iff.mp hnear
  let δ : ℝ := min (η / 2) (1 / 2)
  have hδ : 0 < δ := by
    have : 0 < η / 2 := by positivity
    exact lt_min this (by norm_num)
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hδη : δ ≤ η / 2 := min_le_left _ _
  have hsmall : ∀ r, 0 < r → r ≤ δ → ∫ t in (-r)..r, φ t < (ε / 4) * r := by
    intro r hr0 hrδ
    have hdist : dist r 0 < η := by
      rw [Real.dist_0_eq_abs, abs_of_pos hr0]
      exact lt_of_le_of_lt hrδ (lt_of_le_of_lt hδη (half_lt_self hη))
    have havg : dist ((2 * r)⁻¹ * ∫ t in (-r)..r, φ t) 0 < ε / 8 :=
      hηφ hdist (by simpa [Set.mem_Ioi] using hr0)
    have hintnn : 0 ≤ ∫ t in (-r)..r, φ t :=
      intervalIntegral.integral_nonneg_of_forall (by linarith) hφ
    have havgnn : 0 ≤ (2 * r)⁻¹ * ∫ t in (-r)..r, φ t :=
      mul_nonneg (inv_nonneg.mpr (by positivity)) hintnn
    rw [Real.dist_0_eq_abs, abs_of_nonneg havgnn] at havg
    have hmul := mul_lt_mul_of_pos_left havg (by positivity : 0 < 2 * r)
    have hcancel : (2 * r) * ((2 * r)⁻¹ * ∫ t in (-r)..r, φ t) =
        ∫ t in (-r)..r, φ t := by
      rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    rw [hcancel] at hmul
    have hcoef : (2 * r) * (ε / 8) = (ε / 4) * r := by ring
    linarith
  let I : ℝ := ∫ t in (-(1 / 2))..(1 / 2), φ t
  have hI : 0 ≤ I :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) hφ
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have hfar0 : Tendsto (fun N : ℕ => I / (2 * δ ^ 2) * ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa [mul_zero] using tendsto_const_nhds.mul hinv
  have hε4 : 0 < ε / 4 := by positivity
  rw [Metric.tendsto_nhds] at hfar0
  have hfarEv := hfar0 (ε / 4) hε4
  filter_upwards [hinv.eventually (Metric.ball_mem_nhds 0 hδ), hfarEv] with N hαlt hfar
  rw [Real.dist_0_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity))] at hαlt
  have hα0 : 0 < 1 / (N + 1 : ℝ) := by positivity
  have hαδ : 1 / (N + 1 : ℝ) < δ := by
    rw [one_div]
    exact hαlt
  let α : ℝ := 1 / (N + 1)
  have hαdef : α = 1 / (N + 1 : ℝ) := rfl
  have hann := integral_right_annulus_lt hφ hφint hε hδ hδhalf hα0 hαδ hαdef hsmall
  have hφneg : ∀ t, 0 ≤ φ (-t) := fun t => hφ _
  have hφnegint : IntervalIntegrable (fun t => φ (-t)) volume (-(1 / 2)) (1 / 2) := by
    have hneg := (IntervalIntegrable.iff_comp_neg (f := φ)
      (a := -(1 / 2)) (b := 1 / 2)).mp hφint
    simpa [neg_neg] using hneg.symm
  have hsmallneg : ∀ r, 0 < r → r ≤ δ → ∫ t in (-r)..r, φ (-t) < (ε / 4) * r := by
    intro r hr0 hrδ
    rw [intervalIntegral.integral_comp_neg]
    simpa using hsmall r hr0 hrδ
  have hannneg := integral_right_annulus_lt hφneg hφnegint hε hδ hδhalf hα0 hαδ hαdef hsmallneg
  have hleft : ∫ t in (-δ)..(-α), fejerKernelReal N t * φ t =
      ∫ t in α..δ, fejerKernelReal N t * φ (-t) := by
    have hcomp := intervalIntegral.integral_comp_neg (a := -δ) (b := -α)
      (f := fun u => fejerKernelReal N u * φ (-u))
    simp_rw [fejerKernelReal_neg, neg_neg] at hcomp
    exact hcomp
  have hM : ∀ t, δ ≤ |t| → |t| ≤ 1 / 2 →
      fejerKernelReal N t ≤ 1 / (4 * (N + 1) * δ ^ 2) := by
    intro t htδ ht
    have ht0 : t ≠ 0 := by
      intro ht0
      simp [ht0] at htδ
      linarith
    have hinv : fejerKernelReal N t ≤ 1 / (4 * (N + 1) * t ^ 2) :=
      fejerKernelReal_le_inv_sq ht0 ht
    have ht2 : δ ^ 2 ≤ t ^ 2 := by
      have habs : δ ≤ |t| := htδ
      have := pow_le_pow_left₀ hδ.le habs 2
      simpa [sq_abs] using this
    have hden : 4 * (N + 1 : ℝ) * δ ^ 2 ≤ 4 * (N + 1) * t ^ 2 :=
      mul_le_mul_of_nonneg_left ht2 (by positivity)
    exact hinv.trans ((one_div_le_one_div (by positivity) (by positivity)).2 hden)
  have hfarR : ∫ t in δ..(1 / 2), fejerKernelReal N t * φ t ≤
      1 / (4 * (N + 1) * δ ^ 2) * I := by
    have hab : δ ≤ 1 / 2 := hδhalf
    by_cases hEq : δ = 1 / 2
    · rw [hEq, intervalIntegral.integral_same]
      exact mul_nonneg (by positivity) hI
    · have hlt : δ < 1 / 2 := lt_of_le_of_ne hab hEq
      have hφsub : IntervalIntegrable φ volume δ (1 / 2) :=
        hφint.mono_set (by
          rw [Set.uIcc_of_le hlt.le, Set.uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)]
          exact Set.Icc_subset_Icc (by linarith) le_rfl)
      have hprod : IntervalIntegrable (fun t => fejerKernelReal N t * φ t) volume δ (1 / 2) :=
        hφsub.continuousOn_mul (continuous_fejerKernelReal N).continuousOn
      have hconst : IntervalIntegrable
          (fun t => 1 / (4 * (N + 1 : ℝ) * δ ^ 2) * φ t) volume δ (1 / 2) :=
        hφsub.const_mul _
      have hle1 : ∫ t in δ..(1 / 2), fejerKernelReal N t * φ t ≤
          1 / (4 * (N + 1) * δ ^ 2) * ∫ t in δ..(1 / 2), φ t := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_mono_on hlt.le hprod hconst fun t ht =>
          mul_le_mul_of_nonneg_right (hM t
            (by
              rw [abs_of_nonneg (le_trans hδ.le ht.1)]
              exact ht.1)
            (by
              rw [abs_of_nonneg (le_trans hδ.le ht.1)]
              exact ht.2)) (hφ t)
      have hle2 : ∫ t in δ..(1 / 2), φ t ≤ I :=
        intervalIntegral.integral_mono_interval (by linarith) hlt.le le_rfl
          (ae_restrict_of_ae (ae_of_all _ hφ)) hφint
      exact hle1.trans (mul_le_mul_of_nonneg_left hle2 (by positivity))
  have hfarL : ∫ t in (-(1 / 2))..(-δ), fejerKernelReal N t * φ t ≤
      1 / (4 * (N + 1) * δ ^ 2) * I := by
    have hab : -(1 / 2 : ℝ) ≤ -δ := by linarith
    by_cases hEq : -(1 / 2 : ℝ) = -δ
    · rw [hEq, intervalIntegral.integral_same]
      exact mul_nonneg (by positivity) hI
    · have hlt : -(1 / 2 : ℝ) < -δ := lt_of_le_of_ne hab hEq
      have hφsub : IntervalIntegrable φ volume (-(1 / 2)) (-δ) :=
        hφint.mono_set (by
          rw [Set.uIcc_of_le hlt.le, Set.uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)]
          exact Set.Icc_subset_Icc le_rfl (by linarith))
      have hprod : IntervalIntegrable (fun t => fejerKernelReal N t * φ t) volume
          (-(1 / 2)) (-δ) :=
        hφsub.continuousOn_mul (continuous_fejerKernelReal N).continuousOn
      have hconst : IntervalIntegrable
          (fun t => 1 / (4 * (N + 1 : ℝ) * δ ^ 2) * φ t) volume
          (-(1 / 2)) (-δ) := hφsub.const_mul _
      have hle1 : ∫ t in (-(1 / 2))..(-δ), fejerKernelReal N t * φ t ≤
          1 / (4 * (N + 1) * δ ^ 2) * ∫ t in (-(1 / 2))..(-δ), φ t := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_mono_on hlt.le hprod hconst fun t ht =>
          mul_le_mul_of_nonneg_right (hM t
            (by
              have htneg : t ≤ 0 := le_trans ht.2 (neg_nonpos.mpr hδ.le)
              rw [abs_of_nonpos htneg]
              exact (neg_neg δ).symm.trans_le (neg_le_neg ht.2))
            (by
              have htneg : t ≤ 0 := le_trans ht.2 (neg_nonpos.mpr hδ.le)
              rw [abs_of_nonpos htneg]
              exact (neg_le_neg ht.1).trans_eq (neg_neg (1 / 2)))) (hφ t)
      have hle2 : ∫ t in (-(1 / 2))..(-δ), φ t ≤ I :=
        intervalIntegral.integral_mono_interval le_rfl hlt.le (by linarith)
          (ae_restrict_of_ae (ae_of_all _ hφ)) hφint
      exact hle1.trans (mul_le_mul_of_nonneg_left hle2 (by positivity))
  have hnear : ∫ t in (-α)..α, fejerKernelReal N t * φ t < ε / 4 := by
    have hφsub : IntervalIntegrable φ volume (-α) α :=
      hφint.mono_set (by
        rw [Set.uIcc_of_le (by linarith : -α ≤ α),
          Set.uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)]
        exact Set.Icc_subset_Icc (by linarith [hαδ, hδhalf]) (by linarith [hαδ, hδhalf]))
    have hprod : IntervalIntegrable (fun t => fejerKernelReal N t * φ t) volume (-α) α :=
      hφsub.continuousOn_mul (continuous_fejerKernelReal N).continuousOn
    have hconst : IntervalIntegrable (fun t => (N + 1 : ℝ) * φ t) volume (-α) α :=
      hφsub.const_mul _
    have hle : ∫ t in (-α)..α, fejerKernelReal N t * φ t ≤
        (N + 1 : ℝ) * ∫ t in (-α)..α, φ t := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_mono_on (by linarith : -α ≤ α) hprod hconst fun t _ =>
        mul_le_mul_of_nonneg_right (fejerKernelReal_le_succ N t) (hφ t)
    have hintφ : ∫ t in (-α)..α, φ t < (ε / 4) * α := hsmall α hα0 hαδ.le
    have : (N + 1 : ℝ) * ∫ t in (-α)..α, φ t < (N + 1 : ℝ) * ((ε / 4) * α) :=
      mul_lt_mul_of_pos_left hintφ (by positivity)
    have hcoef : (N + 1 : ℝ) * ((ε / 4) * α) = ε / 4 := by
      rw [hαdef]
      field_simp
    exact lt_of_le_of_lt hle (this.trans_eq hcoef)
  have hψ : IntervalIntegrable (fun t => fejerKernelReal N t * φ t) volume
      (-(1 / 2)) (1 / 2) :=
    hφint.continuousOn_mul (continuous_fejerKernelReal N).continuousOn
  have hmono (a b : ℝ) (hab : a ≤ b) (hca : -(1 / 2) ≤ a) (hbd : b ≤ 1 / 2) :
      IntervalIntegrable (fun t => fejerKernelReal N t * φ t) volume a b :=
    hψ.mono_set <| by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)]
      exact Set.Icc_subset_Icc hca hbd
  have hψ1 := hmono (-(1 / 2)) (-δ) (by linarith) le_rfl (by linarith)
  have hψ2 := hmono (-δ) (-α) (by linarith) (by linarith) (by linarith)
  have hψ3 := hmono (-α) α (by linarith) (by linarith) (by linarith)
  have hψ4 := hmono α δ hαδ.le (by linarith) (by linarith)
  have hψ5 := hmono δ (1 / 2) hδhalf (by linarith) le_rfl
  have hsplit :
      (∫ t in (-(1 / 2))..(-δ), fejerKernelReal N t * φ t) +
        (∫ t in (-δ)..(-α), fejerKernelReal N t * φ t) +
        (∫ t in (-α)..α, fejerKernelReal N t * φ t) +
        (∫ t in α..δ, fejerKernelReal N t * φ t) +
        (∫ t in δ..(1 / 2), fejerKernelReal N t * φ t) =
      ∫ t in (-(1 / 2))..(1 / 2), fejerKernelReal N t * φ t := by
    have h12 := intervalIntegral.integral_add_adjacent_intervals hψ1 hψ2
    have h123 := intervalIntegral.integral_add_adjacent_intervals (hψ1.trans hψ2) hψ3
    have h1234 := intervalIntegral.integral_add_adjacent_intervals
      ((hψ1.trans hψ2).trans hψ3) hψ4
    have h12345 := intervalIntegral.integral_add_adjacent_intervals
      (((hψ1.trans hψ2).trans hψ3).trans hψ4) hψ5
    calc
      (∫ t in (-(1 / 2))..(-δ), fejerKernelReal N t * φ t) +
          (∫ t in (-δ)..(-α), fejerKernelReal N t * φ t) +
          (∫ t in (-α)..α, fejerKernelReal N t * φ t) +
          (∫ t in α..δ, fejerKernelReal N t * φ t) +
          (∫ t in δ..(1 / 2), fejerKernelReal N t * φ t)
        = (∫ t in (-(1 / 2))..(-α), fejerKernelReal N t * φ t) +
            (∫ t in (-α)..α, fejerKernelReal N t * φ t) +
            (∫ t in α..δ, fejerKernelReal N t * φ t) +
            (∫ t in δ..(1 / 2), fejerKernelReal N t * φ t) := by
          rw [h12]
      _ = (∫ t in (-(1 / 2))..α, fejerKernelReal N t * φ t) +
            (∫ t in α..δ, fejerKernelReal N t * φ t) +
            (∫ t in δ..(1 / 2), fejerKernelReal N t * φ t) := by
          rw [h123]
      _ = (∫ t in (-(1 / 2))..δ, fejerKernelReal N t * φ t) +
            (∫ t in δ..(1 / 2), fejerKernelReal N t * φ t) := by
          rw [h1234]
      _ = ∫ t in (-(1 / 2))..(1 / 2), fejerKernelReal N t * φ t := h12345
  have hnn : 0 ≤ ∫ t in (-(1 / 2))..(1 / 2), fejerKernelReal N t * φ t :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) fun t =>
      mul_nonneg (fejerKernelReal_nonneg N t) (hφ t)
  rw [Real.dist_0_eq_abs, abs_of_nonneg hnn, ← hsplit]
  have hILann : ∫ t in (-δ)..(-α), fejerKernelReal N t * φ t < ε / 4 := by
    rw [hleft]
    exact hannneg
  have hIRann : ∫ t in α..δ, fejerKernelReal N t * φ t < ε / 4 := hann
  have hfarlt : I / (2 * δ ^ 2) * ((N : ℝ) + 1)⁻¹ < ε / 4 := by
    have hnnI : 0 ≤ I / (2 * δ ^ 2) * ((N : ℝ) + 1)⁻¹ := by positivity
    rwa [Real.dist_0_eq_abs, abs_of_nonneg hnnI] at hfar
  have htwo : (∫ t in (-(1 / 2))..(-δ), fejerKernelReal N t * φ t) +
      (∫ t in δ..(1 / 2), fejerKernelReal N t * φ t) < ε / 4 := by
    refine lt_of_le_of_lt ?_ hfarlt
    calc
      (∫ t in (-(1 / 2))..(-δ), fejerKernelReal N t * φ t) +
          (∫ t in δ..(1 / 2), fejerKernelReal N t * φ t)
        ≤ 1 / (4 * (N + 1) * δ ^ 2) * I + 1 / (4 * (N + 1) * δ ^ 2) * I :=
          add_le_add hfarL hfarR
      _ = I / (2 * δ ^ 2) * ((N : ℝ) + 1)⁻¹ := by
          field_simp
          ring
  have hrest : (∫ t in (-δ)..(-α), fejerKernelReal N t * φ t) +
      (∫ t in (-α)..α, fejerKernelReal N t * φ t) +
      (∫ t in α..δ, fejerKernelReal N t * φ t) < ε / 4 + ε / 4 + ε / 4 :=
    add_lt_add (add_lt_add hILann hnear) hIRann
  have hjoin :
      (∫ t in (-(1 / 2))..(-δ), fejerKernelReal N t * φ t) +
        (∫ t in (-δ)..(-α), fejerKernelReal N t * φ t) +
        (∫ t in (-α)..α, fejerKernelReal N t * φ t) +
        (∫ t in α..δ, fejerKernelReal N t * φ t) +
        (∫ t in δ..(1 / 2), fejerKernelReal N t * φ t) =
      ((∫ t in (-(1 / 2))..(-δ), fejerKernelReal N t * φ t) +
        (∫ t in δ..(1 / 2), fejerKernelReal N t * φ t)) +
        ((∫ t in (-δ)..(-α), fejerKernelReal N t * φ t) +
          (∫ t in (-α)..α, fejerKernelReal N t * φ t) +
          (∫ t in α..δ, fejerKernelReal N t * φ t)) := by
    set_option backward.isDefEq.respectTransparency true in abel
  rw [hjoin]
  have hεeq : ε / 4 + (ε / 4 + ε / 4 + ε / 4) = ε := by ring
  exact (add_lt_add htwo hrest).trans_eq hεeq

/-- Fejer means recover the value at every circle Lebesgue point. -/
theorem fejerMean_tendsto_at_lebesguePoint {f : AddCircle (1 : ℝ) → ℂ}
    (hf : Integrable f AddCircle.haarAddCircle) {x : AddCircle (1 : ℝ)}
    (hx : IsCircleLebesguePoint f x) :
    Tendsto (fun N ↦ fejerMean f N x) atTop (𝓝 (f x)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp_rw [dist_eq_norm]
  have hshift : Integrable (fun y : 𝕋 => f (x + y)) haar := hf.comp_add_left x
  have hconst : Integrable (fun _ : 𝕋 => f x) haar := integrable_const _
  have hdiff : Integrable (fun y : 𝕋 => f (x + y) - f x) haar := by
    have hpt : (fun y : 𝕋 => f (x + y)) - (fun _ : 𝕋 => f x) =
        fun y : 𝕋 => f (x + y) - f x := by
      ext y
      simp only [Pi.sub_apply]
    rw [← hpt]
    exact hshift.sub hconst
  have hnorm : Integrable (fun y : 𝕋 => ‖f (x + y) - f x‖) haar := hdiff.norm
  have hφint : IntervalIntegrable (fun t : ℝ => ‖f (x + (t : 𝕋)) - f x‖) volume
      (-(1 / 2)) (1 / 2) := intervalIntegrable_coe hnorm
  have hker := tendsto_integral_fejerKernelReal_mul (fun _ => norm_nonneg _) hφint hx
  refine squeeze_zero (fun _ => norm_nonneg _) ?_ hker
  intro N
  have hle := norm_fejerMean_sub_le_add hf N x
  have heq : ∫ t, fejerKernel N t * ‖f (x + t) - f x‖ ∂haar =
      ∫ t in (-(1 / 2))..(1 / 2),
        fejerKernel N (t : 𝕋) * ‖f (x + (t : 𝕋)) - f x‖ :=
    integral_haar_eq_intervalIntegral
      (g := fun y => fejerKernel N y * ‖f (x + y) - f x‖)
  rw [heq] at hle
  simp_rw [← fejerKernelReal_eq] at hle
  exact hle

end CKMA
