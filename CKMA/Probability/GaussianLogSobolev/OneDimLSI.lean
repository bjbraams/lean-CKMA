/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.GaussianLogSobolev.Entropy
public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# One-dimensional Gaussian logarithmic Sobolev inequality

The Ornstein–Uhlenbeck entropy derivative of `Entropy.lean` yields the inequality for smooth
positive functions with bounded derivatives. Compactly supported squares are reduced to that case
by adding a positive constant, and a general smooth square-integrable function is recovered by
smooth cutoffs and Fatou's lemma. The constant is the sharp constant `2` of `gaussianReal 0 1`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory Set Filter InformationTheory
open scoped NNReal ENNReal Real Topology

/-- Extended entropy of a real function, written with Mathlib's `klFun`. -/
def entropyExpr {E : Type*} [MeasurableSpace E] (μ : Measure E) (h : E → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (∫ x, h x ∂μ) *
    ∫⁻ x, ENNReal.ofReal (klFun (h x / ∫ y, h y ∂μ)) ∂μ

/-- A nonnegative number at most `M` satisfies `|t log t| ≤ (max M 1) ^ 2`. -/
lemma abs_mul_log_le {t M : ℝ} (ht : 0 ≤ t) (hM : t ≤ M) :
    |t * Real.log t| ≤ max M 1 * max M 1 := by
  have hmax1 : (1 : ℝ) ≤ max M 1 := le_max_right _ _
  rcases ht.eq_or_lt with rfl | ht0
  · simp
  · by_cases hle : t ≤ 1
    · have habs : |t * Real.log t| < 1 := by
        rw [mul_comm]
        exact Real.abs_log_mul_self_lt t ht0 hle
      have hone : (1 : ℝ) ≤ max M 1 * max M 1 := by nlinarith [hmax1]
      exact habs.le.trans hone
    · have h1 : 1 ≤ t := le_of_not_ge hle
      have hlog : Real.log t ≤ t := Real.log_le_self ht
      have hnonneg : 0 ≤ t * Real.log t := mul_nonneg ht (Real.log_nonneg h1)
      rw [abs_of_nonneg hnonneg]
      have hsq : t * Real.log t ≤ t * t := mul_le_mul_of_nonneg_left hlog ht
      have htmax : t ≤ max M 1 := le_trans hM (le_max_left _ _)
      have hmax0 : (0 : ℝ) ≤ max M 1 := le_trans (by norm_num) hmax1
      nlinarith [hsq, htmax, hmax0]

/-- The derivative vanishes where a smooth function is identically zero outside an interval. -/
lemma deriv_eq_zero_of_zero_outside {φ : ℝ → ℝ} {R : ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) (h0 : ∀ x, R ≤ |x| → φ x = 0) {x : ℝ}
    (hx : R ≤ |x|) : deriv φ x = 0 := by
  by_cases hR : R ≤ 0
  · have hzero : φ = fun _ => 0 := by
      funext y
      exact h0 y (le_trans hR (abs_nonneg y))
    simp [hzero, deriv_const']
  · have hR0 : 0 < R := lt_of_not_ge hR
    have hcont : Continuous (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2.continuous
    have hstrict : ∀ {y : ℝ}, R < |y| → deriv φ y = 0 := by
      intro y hy
      have hEq : φ =ᶠ[nhds y] fun _ => (0 : ℝ) := by
        by_cases hy0 : 0 ≤ y
        · have hyR : R < y := by rwa [abs_of_nonneg hy0] at hy
          filter_upwards [Ioo_mem_nhds (show (y + R) / 2 < y by linarith)
              (show y < y + 1 by linarith)] with z hz
          have hz0 : 0 ≤ z := by linarith [hz.1, hyR, hR0]
          have hzR : R ≤ z := by linarith [hz.1, hyR]
          exact h0 z (by rw [abs_of_nonneg hz0]; exact hzR)
        · have hyneg : y < 0 := lt_of_not_ge hy0
          have hyR : y < -R := by
            rw [abs_of_neg hyneg] at hy
            linarith
          filter_upwards [Ioo_mem_nhds (show y - 1 < y by linarith)
              (show y < (y - R) / 2 by linarith)] with z hz
          have hzneg : z < 0 := by linarith [hz.2, hyR, hR0]
          have hzR : z ≤ -R := by linarith [hz.2, hyR]
          exact h0 z (by rw [abs_of_neg hzneg]; linarith)
      rw [hEq.deriv_eq]
      simp [deriv_const']
    rcases lt_or_eq_of_le hx with hlt | heq
    · exact hstrict hlt
    · have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp
          (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
      by_cases hx0 : 0 ≤ x
      · have hxR : x = R := by
          rw [abs_of_nonneg hx0] at heq
          exact heq.symm
        let s : ℕ → ℝ := fun n => x + ((n : ℝ) + 1)⁻¹
        have hseq : Tendsto s atTop (𝓝 x) := by
          simpa [s] using tendsto_const_nhds.add hinv
        have h0n : ∀ n, deriv φ (s n) = 0 := by
          intro n
          have hpos : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
          have hs0 : 0 ≤ s n := by dsimp [s]; linarith [hR0, hpos]
          have hsR : R < s n := by dsimp [s]; linarith [hxR, hpos]
          exact hstrict (by rwa [abs_of_nonneg hs0])
        have htd : Tendsto (fun n => deriv φ (s n)) atTop (𝓝 (deriv φ x)) :=
          (hcont.tendsto x).comp hseq
        have htd0 : Tendsto (fun n => deriv φ (s n)) atTop (𝓝 (0 : ℝ)) := by
          have heq0 : (fun n => deriv φ (s n)) =ᶠ[atTop] fun _ => (0 : ℝ) := by
            filter_upwards with n
            exact h0n n
          exact tendsto_const_nhds.congr' (EventuallyEq.symm heq0)
        exact tendsto_nhds_unique htd htd0
      · have hxneg : x < 0 := lt_of_not_ge hx0
        have hxR : x = -R := by
          rw [abs_of_neg hxneg] at heq
          linarith
        let s : ℕ → ℝ := fun n => x - ((n : ℝ) + 1)⁻¹
        have hseq : Tendsto s atTop (𝓝 x) := by
          simpa [s] using tendsto_const_nhds.sub hinv
        have h0n : ∀ n, deriv φ (s n) = 0 := by
          intro n
          have hpos : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
          have hsneg : s n < 0 := by dsimp [s]; linarith [hpos]
          have hsR : R < |s n| := by
            rw [abs_of_neg hsneg]
            dsimp [s]
            linarith [hxR, hpos]
          exact hstrict hsR
        have htd : Tendsto (fun n => deriv φ (s n)) atTop (𝓝 (deriv φ x)) :=
          (hcont.tendsto x).comp hseq
        have htd0 : Tendsto (fun n => deriv φ (s n)) atTop (𝓝 (0 : ℝ)) := by
          have heq0 : (fun n => deriv φ (s n)) =ᶠ[atTop] fun _ => (0 : ℝ) := by
            filter_upwards with n
            exact h0n n
          exact tendsto_const_nhds.congr' (EventuallyEq.symm heq0)
        exact tendsto_nhds_unique htd htd0

/-- A continuous function vanishing outside a compact interval is bounded. -/
lemma exists_abs_bound_of_zero_outside {f : ℝ → ℝ} {R : ℝ} (hf : Continuous f)
    (h0 : ∀ x, R ≤ |x| → f x = 0) : ∃ B, ∀ x, |f x| ≤ B := by
  by_cases hR : R ≤ 0
  · exact ⟨0, fun x => by simp [h0 x (le_trans hR (abs_nonneg x))]⟩
  · have hlt : 0 < R := lt_of_not_ge hR
    have hne : (Icc (-R) R).Nonempty := ⟨0, by constructor <;> linarith⟩
    obtain ⟨x0, _, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hf.abs.continuousOn
    refine ⟨|f x0|, fun x => ?_⟩
    by_cases hx : |x| ≤ R
    · exact hmax (abs_le.mp hx)
    · simp [h0 x (le_of_not_ge hx)]

/-- Derivative of a square shifted by a constant. -/
lemma deriv_sq_add {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) (δ x : ℝ) :
    deriv (fun y => φ y ^ 2 + δ) x = 2 * φ x * deriv φ x := by
  have hsq := deriv_fun_pow (hφ x) 2
  rw [deriv_add_const (f := fun y => φ y ^ 2) δ, hsq]
  simp [pow_one]

/-- Algebraic form of `m * klFun (t / m)`, valid at `t = 0`. -/
lemma mul_klFun_div {t m : ℝ} (hm : 0 < m) (ht : 0 ≤ t) :
    m * klFun (t / m) = t * Real.log t - t * Real.log m + m - t := by
  rcases ht.eq_or_lt with rfl | ht0
  · simp [klFun, Real.log_zero, zero_div]
  · rw [klFun, Real.log_div ht0.ne' hm.ne']
    have h1 : m * (t / m) = t := mul_div_cancel₀ t hm.ne'
    have h2 : m * ((t / m) * (Real.log t - Real.log m)) =
        t * (Real.log t - Real.log m) := by
      rw [← mul_assoc, h1]
    calc
      m * ((t / m) * (Real.log t - Real.log m) + 1 - t / m)
          = m * ((t / m) * (Real.log t - Real.log m)) + m * 1 - m * (t / m) := by ring
      _ = t * (Real.log t - Real.log m) + m - t := by rw [h2, h1]; ring
      _ = t * Real.log t - t * Real.log m + m - t := by ring

/-- Integral form of the entropy identity for a bounded nonnegative continuous function. -/
lemma integral_mul_klFun_eq {h : ℝ → ℝ} (hcont : Continuous h) (hnn : ∀ x, 0 ≤ h x)
    (hbd : ∃ M, ∀ x, h x ≤ M) (hm : 0 < ∫ x, h x ∂gaussianReal 0 1) :
    (∫ x, h x ∂gaussianReal 0 1) *
        ∫ x, klFun (h x / ∫ y, h y ∂gaussianReal 0 1) ∂gaussianReal 0 1 =
      (∫ x, h x * Real.log (h x) ∂gaussianReal 0 1) -
        (∫ x, h x ∂gaussianReal 0 1) *
          Real.log (∫ x, h x ∂gaussianReal 0 1) := by
  let γ : Measure ℝ := gaussianReal 0 1
  let m : ℝ := ∫ x, h x ∂γ
  have hm' : 0 < m := by simpa [m, γ] using hm
  obtain ⟨M, hM⟩ := hbd
  have hint_h : Integrable h γ :=
    integrable_of_abs_le hcont.aestronglyMeasurable fun x => by
      rw [abs_of_nonneg (hnn x)]
      exact hM x
  have hint_log : Integrable (fun x => h x * Real.log (h x)) γ :=
    integrable_of_abs_le (Real.continuous_mul_log.comp hcont).aestronglyMeasurable
      fun x => abs_mul_log_le (hnn x) (hM x)
  have hint_lin : Integrable (fun x => h x * Real.log m) γ := hint_h.mul_const _
  have hint_const : Integrable (fun _ : ℝ => m) γ := integrable_const _
  have hint_rhs : Integrable (fun x =>
      h x * Real.log (h x) - h x * Real.log m + m - h x) γ :=
    ((hint_log.sub hint_lin).add hint_const).sub hint_h
  have hpt : ∀ x, m * klFun (h x / m) =
      h x * Real.log (h x) - h x * Real.log m + m - h x :=
    fun x => mul_klFun_div hm' (hnn x)
  have hint_mul : Integrable (fun x => m * klFun (h x / m)) γ := by
    refine hint_rhs.congr ?_
    filter_upwards with x
    exact (hpt x).symm
  have hint_kl : Integrable (fun x => klFun (h x / m)) γ :=
    (integrable_const_mul_iff (IsUnit.mk0 m hm'.ne')
      (fun x => klFun (h x / m))).1 hint_mul
  have hint_eq : ∫ x, m * klFun (h x / m) ∂γ =
      ∫ x, (h x * Real.log (h x) - h x * Real.log m + m - h x) ∂γ := by
    refine integral_congr_ae ?_
    filter_upwards with x
    exact hpt x
  have hA : Integrable (fun x => h x * Real.log (h x) - h x * Real.log m) γ :=
    hint_log.sub hint_lin
  have hB : Integrable
      (fun x => h x * Real.log (h x) - h x * Real.log m + m) γ := hA.add hint_const
  have hsplit : ∫ x, (h x * Real.log (h x) - h x * Real.log m + m - h x) ∂γ =
      (∫ x, h x * Real.log (h x) ∂γ) - (∫ x, h x * Real.log m ∂γ) +
        (∫ _x, m ∂γ) - ∫ x, h x ∂γ := by
    rw [integral_sub hB hint_h, integral_add hA hint_const, integral_sub hint_log hint_lin]
  rw [integral_const_mul] at hint_eq
  have hconst : ∫ _x, m ∂γ = m := by simp [integral_const, probReal_univ]
  have hlin : ∫ x, h x * Real.log m ∂γ = m * Real.log m := by
    rw [integral_mul_const]
  have hfin : m * ∫ x, klFun (h x / m) ∂γ =
      (∫ x, h x * Real.log (h x) ∂γ) - m * Real.log m := by
    rw [hint_eq, hsplit, hconst, hlin]
    ring
  simpa [m, γ, hint_kl] using hfin

/-- The `klFun` entropy equals the real entropy for a bounded positive-mass integrand. -/
lemma entropyExpr_eq_ofReal {h : ℝ → ℝ} (hcont : Continuous h) (hnn : ∀ x, 0 ≤ h x)
    (hbd : ∃ M, ∀ x, h x ≤ M) (hm : 0 < ∫ x, h x ∂gaussianReal 0 1) :
    entropyExpr (gaussianReal 0 1) h =
      ENNReal.ofReal ((∫ x, h x * Real.log (h x) ∂gaussianReal 0 1) -
        (∫ x, h x ∂gaussianReal 0 1) *
          Real.log (∫ x, h x ∂gaussianReal 0 1)) := by
  let γ : Measure ℝ := gaussianReal 0 1
  let m : ℝ := ∫ x, h x ∂γ
  have hm' : 0 < m := by simpa [m, γ] using hm
  have hid := integral_mul_klFun_eq hcont hnn hbd hm
  obtain ⟨M, hM⟩ := hbd
  have hint_h : Integrable h γ :=
    integrable_of_abs_le hcont.aestronglyMeasurable fun x => by
      rw [abs_of_nonneg (hnn x)]; exact hM x
  have hint_log : Integrable (fun x => h x * Real.log (h x)) γ :=
    integrable_of_abs_le (Real.continuous_mul_log.comp hcont).aestronglyMeasurable
      fun x => abs_mul_log_le (hnn x) (hM x)
  have hint_lin : Integrable (fun x => h x * Real.log m) γ := hint_h.mul_const _
  have hint_const : Integrable (fun _ : ℝ => m) γ := integrable_const _
  have hint_rhs : Integrable (fun x =>
      h x * Real.log (h x) - h x * Real.log m + m - h x) γ :=
    ((hint_log.sub hint_lin).add hint_const).sub hint_h
  have hpt : ∀ x, m * klFun (h x / m) =
      h x * Real.log (h x) - h x * Real.log m + m - h x :=
    fun x => mul_klFun_div hm' (hnn x)
  have hint_mul : Integrable (fun x => m * klFun (h x / m)) γ := by
    refine hint_rhs.congr ?_
    filter_upwards with x
    exact (hpt x).symm
  have hint_kl : Integrable (fun x => klFun (h x / m)) γ :=
    (integrable_const_mul_iff (IsUnit.mk0 m hm'.ne')
      (fun x => klFun (h x / m))).1 hint_mul
  have hkl_nn : 0 ≤ᵐ[γ] fun x => klFun (h x / m) :=
    ae_of_all _ fun x => klFun_nonneg (div_nonneg (hnn x) hm'.le)
  unfold entropyExpr
  rw [← ofReal_integral_eq_lintegral_ofReal hint_kl hkl_nn]
  rw [← ENNReal.ofReal_mul hm'.le]
  exact congrArg ENNReal.ofReal (by simpa [m, γ] using hid)

/-- Real Gaussian entropy of `φ ^ 2 + δ` for smooth compactly supported `φ`. -/
lemma gaussian_realEntropy_sq_add_le {φ : ℝ → ℝ} {R δ : ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) (h0 : ∀ x, R ≤ |x| → φ x = 0) (hδ : 0 < δ) :
    (∫ x, (φ x ^ 2 + δ) * Real.log (φ x ^ 2 + δ) ∂gaussianReal 0 1) -
        (∫ x, (φ x ^ 2 + δ) ∂gaussianReal 0 1) *
          Real.log (∫ x, (φ x ^ 2 + δ) ∂gaussianReal 0 1) ≤
      2 * ∫ x, (deriv φ x) ^ 2 ∂gaussianReal 0 1 := by
  let γ : Measure ℝ := gaussianReal 0 1
  let f : ℝ → ℝ := fun x => φ x ^ 2 + δ
  have htwo : (2 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have hdiff : Differentiable ℝ φ := (contDiff_infty_iff_deriv.mp hφ).1
  have hfC : ContDiff ℝ (↑(⊤ : ℕ∞)) f := by
    simpa [f] using (hφ.pow 2).add contDiff_const
  have hf2 : ContDiff ℝ 2 f := hfC.of_le htwo
  have hδf : ∀ x, δ ≤ f x := fun x => by
    simp only [f]
    exact le_add_of_nonneg_left (sq_nonneg _)
  have hderiv : ∀ x, deriv f x = 2 * φ x * deriv φ x := fun x => by
    simpa [f] using deriv_sq_add hdiff δ x
  have hφ0 : ∀ x, R ≤ |x| → deriv φ x = 0 := fun x hx =>
    deriv_eq_zero_of_zero_outside hφ h0 hx
  have hφ'C : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  obtain ⟨Bφ, hBφ⟩ := exists_abs_bound_of_zero_outside hφ.continuous h0
  obtain ⟨Bφ', hBφ'⟩ := exists_abs_bound_of_zero_outside hφ'C.continuous hφ0
  have hBφ0 : 0 ≤ Bφ := le_trans (abs_nonneg _) (hBφ 0)
  have hBφ'0 : 0 ≤ Bφ' := le_trans (abs_nonneg _) (hBφ' 0)
  have hf'0 : ∀ x, R ≤ |x| → deriv f x = 0 := by
    intro x hx
    rw [hderiv x, h0 x hx, hφ0 x hx]
    ring
  have hf'C : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv f) := (contDiff_infty_iff_deriv.mp hfC).2
  have hf''0 : ∀ x, R ≤ |x| → deriv (deriv f) x = 0 := fun x hx =>
    deriv_eq_zero_of_zero_outside hf'C hf'0 hx
  obtain ⟨Bf', hBf'⟩ := exists_abs_bound_of_zero_outside hf'C.continuous hf'0
  obtain ⟨Bf'', hBf''⟩ := exists_abs_bound_of_zero_outside
    ((contDiff_infty_iff_deriv.mp hf'C).2.continuous) hf''0
  have hM : ∀ x, |f x| ≤ Bφ ^ 2 + δ := by
    intro x
    have hnn : 0 ≤ f x := le_trans hδ.le (hδf x)
    rw [abs_of_nonneg hnn]
    have hsq : φ x ^ 2 ≤ Bφ ^ 2 :=
      sq_le_sq.mpr (by simpa [abs_of_nonneg hBφ0] using hBφ x)
    simpa [f] using add_le_add_right hsq δ
  have hhalf := gaussian_entropy_le_half_fisher hf2 hδ hδf ⟨Bf', hBf'⟩ ⟨Bf'', hBf''⟩
    ⟨Bφ ^ 2 + δ, hM⟩
  have hpoint : ∀ x, (deriv f x) ^ 2 / f x ≤ 4 * (deriv φ x) ^ 2 := by
    intro x
    rw [hderiv x]
    have hpos : 0 < f x := lt_of_lt_of_le hδ (hδf x)
    rw [div_le_iff₀ hpos]
    have : (2 * φ x * deriv φ x) ^ 2 ≤ 4 * (deriv φ x) ^ 2 * f x := by
      simp only [f]
      nlinarith [sq_nonneg (φ x), sq_nonneg (deriv φ x), hδ.le]
    simpa [f] using this
  have hcont_q : Continuous (fun x => (deriv f x) ^ 2 / f x) := by
    have hdf : Continuous (deriv f) := hf'C.continuous
    exact (hdf.pow 2).div hfC.continuous fun x => (lt_of_lt_of_le hδ (hδf x)).ne'
  have hBd : ∀ x, |(deriv f x) ^ 2 / f x| ≤ Bf' ^ 2 / δ := by
    intro x
    have hpos : 0 < f x := lt_of_lt_of_le hδ (hδf x)
    rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hpos.le)]
    have hnum : (deriv f x) ^ 2 ≤ Bf' ^ 2 := by
      have hB0 : 0 ≤ Bf' := le_trans (abs_nonneg _) (hBf' 0)
      exact sq_le_sq.mpr (by simpa [abs_of_nonneg hB0] using hBf' x)
    rw [div_le_div_iff₀ hpos hδ]
    exact mul_le_mul hnum (hδf x) hδ.le (sq_nonneg _)
  have hint1 : Integrable (fun x => (deriv f x) ^ 2 / f x) γ :=
    integrable_of_abs_le hcont_q.aestronglyMeasurable hBd
  have hcont_p : Continuous (fun x => 4 * (deriv φ x) ^ 2) := by fun_prop
  have hBp : ∀ x, |4 * (deriv φ x) ^ 2| ≤ 4 * Bφ' ^ 2 := by
    intro x
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))]
    have hsq : (deriv φ x) ^ 2 ≤ Bφ' ^ 2 :=
      sq_le_sq.mpr (by simpa [abs_of_nonneg hBφ'0] using hBφ' x)
    nlinarith [hsq]
  have hint2 : Integrable (fun x => 4 * (deriv φ x) ^ 2) γ :=
    integrable_of_abs_le hcont_p.aestronglyMeasurable hBp
  have hmono := integral_mono hint1 hint2 hpoint
  have hmul : (1 / 2) * ∫ x, 4 * (deriv φ x) ^ 2 ∂γ =
      2 * ∫ x, (deriv φ x) ^ 2 ∂γ := by
    rw [integral_const_mul]
    ring
  calc
    (∫ x, f x * Real.log (f x) ∂γ) - (∫ x, f x ∂γ) * Real.log (∫ x, f x ∂γ)
        ≤ (1 / 2) * ∫ x, (deriv f x) ^ 2 / f x ∂γ := by simpa [f, γ] using hhalf
    _ ≤ (1 / 2) * ∫ x, 4 * (deriv φ x) ^ 2 ∂γ :=
        mul_le_mul_of_nonneg_left hmono (by norm_num)
    _ = 2 * ∫ x, (deriv φ x) ^ 2 ∂γ := hmul

/-- Entropy of `φ ^ 2 + δ` for smooth compactly supported `φ`. -/
lemma entropyExpr_sq_add_support_le {φ : ℝ → ℝ} {R δ : ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) (h0 : ∀ x, R ≤ |x| → φ x = 0) (hδ : 0 < δ) :
    entropyExpr (gaussianReal 0 1) (fun x => φ x ^ 2 + δ) ≤
      ENNReal.ofReal (2 * ∫ x, (deriv φ x) ^ 2 ∂gaussianReal 0 1) := by
  let γ : Measure ℝ := gaussianReal 0 1
  let h : ℝ → ℝ := fun x => φ x ^ 2 + δ
  have hcont : Continuous h := by
    simpa [h] using (hφ.continuous.fun_pow 2).fun_add continuous_const
  have hnn : ∀ x, 0 ≤ h x := fun x => by
    dsimp [h]; positivity
  obtain ⟨Bφ, hBφ⟩ := exists_abs_bound_of_zero_outside hφ.continuous h0
  have hBφ0 : 0 ≤ Bφ := le_trans (abs_nonneg _) (hBφ 0)
  have hbd : ∀ x, h x ≤ Bφ ^ 2 + δ := by
    intro x
    dsimp [h]
    have hsq : φ x ^ 2 ≤ Bφ ^ 2 :=
      sq_le_sq.mpr (by simpa [abs_of_nonneg hBφ0] using hBφ x)
    linarith
  have hm : 0 < ∫ x, h x ∂γ := by
    have hge : ∀ x, δ ≤ h x := fun x => by dsimp [h]; exact le_add_of_nonneg_left (sq_nonneg _)
    have hint : Integrable h γ :=
      integrable_of_abs_le hcont.aestronglyMeasurable fun x => by
        rw [abs_of_nonneg (hnn x)]
        exact hbd x
    have hconst : ∫ x, δ ∂γ = δ := by simp [integral_const, probReal_univ]
    have hmono := integral_mono (integrable_const δ) hint hge
    rw [hconst] at hmono
    exact lt_of_lt_of_le hδ hmono
  rw [entropyExpr_eq_ofReal hcont hnn ⟨Bφ ^ 2 + δ, hbd⟩ (by simpa [h, γ] using hm)]
  exact ENNReal.ofReal_le_ofReal (by simpa [h, γ] using gaussian_realEntropy_sq_add_le hφ h0 hδ)

/-- Smooth cutoff equal to `1` on `[-R, R]` and to `0` outside `[-R - 1, R + 1]`. -/
def oneDimCutoff (R x : ℝ) : ℝ :=
  Real.smoothTransition (R + 1 - x) * Real.smoothTransition (R + 1 + x)

/-- The one-dimensional cutoff is smooth. -/
lemma contDiff_oneDimCutoff (R : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (oneDimCutoff R) := by
  unfold oneDimCutoff
  fun_prop

/-- The cutoff takes values in `[0, 1]`. -/
lemma oneDimCutoff_mem_Icc (R x : ℝ) : oneDimCutoff R x ∈ Icc (0 : ℝ) 1 := by
  unfold oneDimCutoff
  refine ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _), ?_⟩
  have hmul : Real.smoothTransition (R + 1 - x) * Real.smoothTransition (R + 1 + x) ≤ 1 * 1 :=
    mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
      (Real.smoothTransition.nonneg _) zero_le_one
  rw [mul_one] at hmul
  exact hmul

/-- The cutoff equals `1` on `[-R, R]`. -/
lemma oneDimCutoff_eq_one_of_abs_le {R x : ℝ} (hx : |x| ≤ R) : oneDimCutoff R x = 1 := by
  have h1 : 1 ≤ R + 1 - x := by linarith [le_abs_self x, hx]
  have h2 : 1 ≤ R + 1 + x := by linarith [neg_le_abs x, hx]
  simp [oneDimCutoff, Real.smoothTransition.one_of_one_le h1,
    Real.smoothTransition.one_of_one_le h2]

/-- The cutoff vanishes for `|x| ≥ R + 1`. -/
lemma oneDimCutoff_eq_zero_of_le {R x : ℝ} (hx : R + 1 ≤ |x|) : oneDimCutoff R x = 0 := by
  by_cases hx0 : 0 ≤ x
  · have _hx' : R + 1 ≤ x := by rwa [abs_of_nonneg hx0] at hx
    simp [oneDimCutoff, Real.smoothTransition.zero_of_nonpos (by linarith : R + 1 - x ≤ 0)]
  · have hxneg : x < 0 := lt_of_not_ge hx0
    have _hx' : x ≤ -(R + 1) := by
      rw [abs_of_neg hxneg] at hx
      linarith
    simp [oneDimCutoff, Real.smoothTransition.zero_of_nonpos (by linarith : R + 1 + x ≤ 0)]

/-- The derivative of `Real.smoothTransition` is bounded. -/
lemma exists_smoothTransition_deriv_bound :
    ∃ C, 0 ≤ C ∧ ∀ x, |deriv Real.smoothTransition x| ≤ C := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp (Real.smoothTransition.contDiff (n := ⊤))).2.continuous
  have hzero : ∀ {x : ℝ}, x ∉ Icc (0 : ℝ) 1 → deriv Real.smoothTransition x = 0 := by
    intro x hx
    have hEq : (Real.smoothTransition =ᶠ[nhds x] fun _ => (0 : ℝ)) ∨
        (Real.smoothTransition =ᶠ[nhds x] fun _ => (1 : ℝ)) := by
      by_cases hx0 : x < 0
      · left
        filter_upwards [Ioo_mem_nhds (show x - 1 < x by linarith) (show x < 0 by exact hx0)]
          with y hy
        exact Real.smoothTransition.zero_of_nonpos hy.2.le
      · right
        have hx1 : 1 < x := by
          have hxI : x < 0 ∨ 1 < x := by
            by_contra hnot
            push Not at hnot
            exact hx ⟨hnot.1, hnot.2⟩
          rcases hxI with h0 | h1
          · exact (hx0 h0).elim
          · exact h1
        filter_upwards [Ioo_mem_nhds (show 1 < x by exact hx1) (show x < x + 1 by linarith)]
          with y hy
        exact Real.smoothTransition.one_of_one_le hy.1.le
    rcases hEq with hEq | hEq
    · rw [hEq.deriv_eq]; simp [deriv_const']
    · rw [hEq.deriv_eq]; simp [deriv_const']
  have hne : (Icc (0 : ℝ) 1).Nonempty := ⟨0, by simp⟩
  obtain ⟨x0, hx0, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont.abs.continuousOn
  refine ⟨|deriv Real.smoothTransition x0|, abs_nonneg _, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · exact hmax hx
  · simp [hzero hx]

/-- Derivative of the product defining `oneDimCutoff`. -/
lemma deriv_oneDimCutoff (R x : ℝ) :
    deriv (oneDimCutoff R) x =
      deriv Real.smoothTransition (R + 1 - x) * (-1) * Real.smoothTransition (R + 1 + x) +
        Real.smoothTransition (R + 1 - x) *
          (deriv Real.smoothTransition (R + 1 + x) * 1) := by
  have hρ : Differentiable ℝ Real.smoothTransition :=
    (contDiff_infty_iff_deriv.mp (Real.smoothTransition.contDiff (n := ⊤))).1
  have hsub : HasDerivAt (fun y => R + 1 - y) (-1) x :=
    HasDerivAt.const_sub (R + 1) (hasDerivAt_id' x)
  have hadd : HasDerivAt (fun y => R + 1 + y) 1 x :=
    (hasDerivAt_const_add_iff (c := R + 1) (f := fun y : ℝ => y) (f' := 1) (x := x)).2
      (hasDerivAt_id' x)
  have hleft : deriv (fun y => Real.smoothTransition (R + 1 - y)) x =
      deriv Real.smoothTransition (R + 1 - x) * -1 := by
    have hcomp := ((hρ (R + 1 - x)).hasDerivAt).comp x hsub
    have hfun : HasDerivAt (fun y => Real.smoothTransition (R + 1 - y))
        (deriv Real.smoothTransition (R + 1 - x) * -1) x :=
      hcomp.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (by funext y; rfl))
    exact hfun.deriv
  have hright : deriv (fun y => Real.smoothTransition (R + 1 + y)) x =
      deriv Real.smoothTransition (R + 1 + x) * 1 := by
    have hcomp := ((hρ (R + 1 + x)).hasDerivAt).comp x hadd
    have hfun : HasDerivAt (fun y => Real.smoothTransition (R + 1 + y))
        (deriv Real.smoothTransition (R + 1 + x) * 1) x :=
      hcomp.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (by funext y; rfl))
    exact hfun.deriv
  unfold oneDimCutoff
  have hdl : DifferentiableAt ℝ (fun y => Real.smoothTransition (R + 1 - y)) x :=
    (hρ.differentiableAt).comp x hsub.differentiableAt
  have hdr : DifferentiableAt ℝ (fun y => Real.smoothTransition (R + 1 + y)) x :=
    (hρ.differentiableAt).comp x hadd.differentiableAt
  rw [deriv_fun_mul hdl hdr, hleft, hright]

/-- The cutoff derivative is bounded independently of the radius. -/
lemma abs_deriv_oneDimCutoff_le {C R x : ℝ} (_hC0 : 0 ≤ C)
    (hC : ∀ y, |deriv Real.smoothTransition y| ≤ C) :
    |deriv (oneDimCutoff R) x| ≤ 2 * C := by
  rw [deriv_oneDimCutoff]
  have hρ1 : |Real.smoothTransition (R + 1 + x)| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hρ2 : |Real.smoothTransition (R + 1 - x)| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hsum := abs_add_le
    (deriv Real.smoothTransition (R + 1 - x) * (-1) * Real.smoothTransition (R + 1 + x))
    (Real.smoothTransition (R + 1 - x) * (deriv Real.smoothTransition (R + 1 + x) * 1))
  have h1 : |deriv Real.smoothTransition (R + 1 - x) * (-1) *
      Real.smoothTransition (R + 1 + x)| ≤ C := by
    rw [abs_mul, abs_mul, abs_neg, abs_one]
    have := hC (R + 1 - x)
    nlinarith [this, hρ1, abs_nonneg (deriv Real.smoothTransition (R + 1 - x)), _hC0]
  have h2 : |Real.smoothTransition (R + 1 - x) *
      (deriv Real.smoothTransition (R + 1 + x) * 1)| ≤ C := by
    rw [abs_mul, abs_mul, abs_one]
    have := hC (R + 1 + x)
    nlinarith [this, hρ2, abs_nonneg (deriv Real.smoothTransition (R + 1 + x)), _hC0]
  linarith

/-- Inside the flat region the cutoff does not change the derivative. -/
lemma deriv_mul_cutoff_of_abs_lt {φ : ℝ → ℝ} {R x : ℝ} (hφ : DifferentiableAt ℝ φ x)
    (hx : |x| < R) : deriv (fun y => φ y * oneDimCutoff R y) x = deriv φ x := by
  have hηdiff : DifferentiableAt ℝ (oneDimCutoff R) x :=
    (contDiff_infty_iff_deriv.mp (contDiff_oneDimCutoff R)).1 x
  have hEq : oneDimCutoff R =ᶠ[nhds x] fun _ => (1 : ℝ) := by
    filter_upwards [Ioo_mem_nhds (show -R < x by linarith [abs_lt.mp hx])
        (show x < R by linarith [abs_lt.mp hx])] with y hy
    rcases hy with ⟨hy1, hy2⟩
    exact oneDimCutoff_eq_one_of_abs_le (abs_le.mpr ⟨hy1.le, hy2.le⟩)
  have hderiv0 : deriv (oneDimCutoff R) x = 0 := by
    rw [hEq.deriv_eq]
    simp [deriv_const']
  rw [deriv_fun_mul hφ hηdiff, hderiv0, oneDimCutoff_eq_one_of_abs_le hx.le]
  ring

/-- Energy of a cutoff is dominated by the original energy and the square. -/
lemma sq_deriv_mul_cutoff_le {φ : ℝ → ℝ} {C R x : ℝ} (hφ : DifferentiableAt ℝ φ x)
    (hC0 : 0 ≤ C) (hC : ∀ y, |deriv Real.smoothTransition y| ≤ C) :
    (deriv (fun y => φ y * oneDimCutoff R y) x) ^ 2 ≤
      2 * (deriv φ x) ^ 2 + 8 * C ^ 2 * φ x ^ 2 := by
  have hηdiff : DifferentiableAt ℝ (oneDimCutoff R) x :=
    (contDiff_infty_iff_deriv.mp (contDiff_oneDimCutoff R)).1 x
  have hprod := deriv_fun_mul hφ hηdiff
  have hη1 : |oneDimCutoff R x| ≤ 1 := by
    have hmem := oneDimCutoff_mem_Icc R x
    rw [abs_of_nonneg hmem.1]
    exact hmem.2
  have hη' : |deriv (oneDimCutoff R) x| ≤ 2 * C := abs_deriv_oneDimCutoff_le hC0 hC
  have hle : |deriv (fun y => φ y * oneDimCutoff R y) x| ≤
      |deriv φ x| + 2 * C * |φ x| := by
    rw [hprod]
    have hsum := abs_add_le (deriv φ x * oneDimCutoff R x) (φ x * deriv (oneDimCutoff R) x)
    have hfirst : |deriv φ x * oneDimCutoff R x| ≤ |deriv φ x| := by
      rw [abs_mul]
      nlinarith [hη1, abs_nonneg (deriv φ x)]
    have hsecond : |φ x * deriv (oneDimCutoff R) x| ≤ 2 * C * |φ x| := by
      rw [abs_mul, mul_comm]
      nlinarith [hη', abs_nonneg (φ x), hC0]
    linarith
  have hsq : (|deriv φ x| + 2 * C * |φ x|) ^ 2 ≤
      2 * (deriv φ x) ^ 2 + 8 * C ^ 2 * φ x ^ 2 := by
    nlinarith [sq_nonneg (|deriv φ x| - 2 * C * |φ x|), sq_abs (deriv φ x), sq_abs (φ x), hC0]
  rw [← sq_abs]
  exact (pow_le_pow_left₀ (abs_nonneg _) hle 2).trans hsq

/-- Fatou lower semicontinuity of `entropyExpr` along a sequence of bounded approximants. -/
lemma entropyExpr_le_of_nat_approx {hApprox : ℕ → ℝ → ℝ} {hLim : ℝ → ℝ} {c : ℕ → ℝ} {c0 : ℝ}
    (hcont : ∀ n, Continuous (hApprox n)) (_hcontLim : Continuous hLim)
    (_hnn : ∀ n x, 0 ≤ hApprox n x) (hnnLim : ∀ x, 0 ≤ hLim x)
    (hpt : ∀ x, Tendsto (fun n => hApprox n x) atTop (𝓝 (hLim x)))
    (hmass : Tendsto (fun n => ∫ x, hApprox n x ∂gaussianReal 0 1) atTop
      (𝓝 (∫ x, hLim x ∂gaussianReal 0 1)))
    (hineq : ∀ n, entropyExpr (gaussianReal 0 1) (hApprox n) ≤ ENNReal.ofReal (c n))
    (_hcnn : ∀ n, 0 ≤ c n) (hc : Tendsto c atTop (𝓝 c0)) (hc0 : 0 ≤ c0) :
    entropyExpr (gaussianReal 0 1) hLim ≤ ENNReal.ofReal c0 := by
  let γ : Measure ℝ := gaussianReal 0 1
  let mass : ℕ → ℝ := fun n => ∫ x, hApprox n x ∂γ
  let m : ℝ := ∫ x, hLim x ∂γ
  let a : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ x, ENNReal.ofReal (klFun (hApprox n x / mass n)) ∂γ
  have hmass' : Tendsto mass atTop (𝓝 m) := by simpa [mass, m, γ] using hmass
  by_cases hm0 : m = 0
  · simp [entropyExpr, m, γ, hm0, ENNReal.ofReal_zero, zero_mul]
  · have hm : 0 < m := lt_of_le_of_ne (integral_nonneg fun x => hnnLim x) (Ne.symm hm0)
    have hineq' : ∀ n, ENNReal.ofReal (mass n) * a n ≤ ENNReal.ofReal (c n) := by
      intro n
      simpa [entropyExpr, mass, a, γ] using hineq n
    have hmeas : ∀ n, AEMeasurable
        (fun x => ENNReal.ofReal (klFun (hApprox n x / mass n))) γ := by
      intro n
      have hdiv : Continuous (fun x => hApprox n x / mass n) := by
        have hrewrite : (fun x => hApprox n x / mass n) =
            fun x => (mass n)⁻¹ * hApprox n x := by
          funext x
          rw [div_eq_mul_inv, mul_comm]
        rw [hrewrite]
        exact continuous_const.mul (hcont n)
      exact (ENNReal.continuous_ofReal.comp
        (continuous_klFun.comp hdiv)).measurable.aemeasurable
    have hpw : ∀ x, liminf (fun n => ENNReal.ofReal (klFun (hApprox n x / mass n))) atTop =
        ENNReal.ofReal (klFun (hLim x / m)) := by
      intro x
      refine Tendsto.liminf_eq ?_
      refine (ENNReal.continuous_ofReal.tendsto _).comp ((continuous_klFun.tendsto _).comp ?_)
      exact (hpt x).div hmass' hm.ne'
    have hfatou := lintegral_liminf_le' (μ := γ) (u := atTop)
      (f := fun n x => ENNReal.ofReal (klFun (hApprox n x / mass n))) hmeas
    have hlimle : liminf a atTop ≤ ENNReal.ofReal (c0 / m) := by
      have hεbound : ∀ ε : ℝ, 0 < ε → liminf a atTop ≤ ENNReal.ofReal (c0 / m + ε) := by
        intro ε hε
        have hratio : Tendsto (fun n => c n / mass n) atTop (𝓝 (c0 / m)) :=
          hc.div hmass' hm.ne'
        have hev : ∀ᶠ n in atTop, a n ≤ ENNReal.ofReal (c0 / m + ε) := by
          have hclose : ∀ᶠ n in atTop, c n / mass n < c0 / m + ε :=
            hratio (Iio_mem_nhds (by linarith))
          have hpos : ∀ᶠ n in atTop, m / 2 < mass n :=
            hmass' (Ioi_mem_nhds (by linarith : m / 2 < m))
          filter_upwards [hclose, hpos] with n hn hnpos
          have hnpos' : 0 < mass n := by linarith
          have hmass_ne : ENNReal.ofReal (mass n) ≠ 0 := by
            exact (ENNReal.ofReal_pos.mpr hnpos').ne'
          have ha : a n ≤ ENNReal.ofReal (c n) / ENNReal.ofReal (mass n) :=
            (ENNReal.le_div_iff_mul_le (b := ENNReal.ofReal (mass n))
              (c := ENNReal.ofReal (c n)) (Or.inl hmass_ne)
              (Or.inl ENNReal.ofReal_ne_top)).2 (by simpa [mul_comm] using hineq' n)
          rw [← ENNReal.ofReal_div_of_pos hnpos'] at ha
          exact ha.trans (ENNReal.ofReal_le_ofReal hn.le)
        exact (liminf_le_limsup (f := atTop) (u := a)).trans (limsup_le_of_le (h := hev))
      have hfin : liminf a atTop ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hεbound 1 one_pos)
      have hto : ENNReal.toReal (liminf a atTop) ≤ c0 / m := by
        refine le_of_forall_pos_le_add ?_
        intro ε hε
        have hnonneg : 0 ≤ c0 / m + ε := add_nonneg (div_nonneg hc0 hm.le) hε.le
        have htr := ENNReal.toReal_le_of_le_ofReal hnonneg (hεbound ε hε)
        linarith
      rw [← ENNReal.ofReal_toReal hfin]
      exact ENNReal.ofReal_le_ofReal hto
    have hfatou' : ∫⁻ x, ENNReal.ofReal (klFun (hLim x / m)) ∂γ ≤ liminf a atTop := by
      have hrew : (fun x => liminf (fun n => ENNReal.ofReal (klFun (hApprox n x / mass n)))
          atTop) = fun x => ENNReal.ofReal (klFun (hLim x / m)) := by
        funext x
        exact hpw x
      simpa [a, hrew] using hfatou
    calc
      entropyExpr γ hLim = ENNReal.ofReal m * ∫⁻ x, ENNReal.ofReal (klFun (hLim x / m)) ∂γ := by
        simp [entropyExpr, m, γ]
      _ ≤ ENNReal.ofReal m * liminf a atTop :=
          mul_le_mul_of_nonneg_left hfatou' bot_le
      _ ≤ ENNReal.ofReal m * ENNReal.ofReal (c0 / m) :=
          mul_le_mul_of_nonneg_left hlimle bot_le
      _ = ENNReal.ofReal c0 := by
          rw [← ENNReal.ofReal_mul hm.le]
          congr 1
          field_simp

/-- Entropy of `φ ^ 2 + δ` for smooth square-integrable `φ` with integrable derivative. -/
lemma gaussian_entropyExpr_sq_add_le {φ : ℝ → ℝ} {δ : ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (hφ2 : Integrable (fun x => φ x ^ 2) (gaussianReal 0 1))
    (hφ' : Integrable (fun x => (deriv φ x) ^ 2) (gaussianReal 0 1)) (hδ : 0 < δ) :
    entropyExpr (gaussianReal 0 1) (fun x => φ x ^ 2 + δ) ≤
      ENNReal.ofReal (2 * ∫ x, (deriv φ x) ^ 2 ∂gaussianReal 0 1) := by
  let γ : Measure ℝ := gaussianReal 0 1
  obtain ⟨C, hC0, hC⟩ := exists_smoothTransition_deriv_bound
  let η : ℕ → ℝ → ℝ := fun n => oneDimCutoff (n : ℝ)
  let φn : ℕ → ℝ → ℝ := fun n x => φ x * η n x
  have hφnC : ∀ n, ContDiff ℝ (↑(⊤ : ℕ∞)) (φn n) := by
    intro n
    simpa [φn, η] using hφ.mul (contDiff_oneDimCutoff (n : ℝ))
  have hφn0 : ∀ n : ℕ, ∀ x, (n : ℝ) + 1 ≤ |x| → φn n x = 0 := by
    intro n x hx
    dsimp [φn, η]
    rw [oneDimCutoff_eq_zero_of_le hx]
    simp
  have hdiff : Differentiable ℝ φ := (contDiff_infty_iff_deriv.mp hφ).1
  have hineq : ∀ n, entropyExpr γ (fun x => φn n x ^ 2 + δ) ≤
      ENNReal.ofReal (2 * ∫ x, (deriv (φn n) x) ^ 2 ∂γ) := by
    intro n
    simpa [γ] using entropyExpr_sq_add_support_le (R := (n : ℝ) + 1) (hφnC n) (hφn0 n) hδ
  have hdom : ∀ n x, (deriv (φn n) x) ^ 2 ≤
      2 * (deriv φ x) ^ 2 + 8 * C ^ 2 * φ x ^ 2 := by
    intro n x
    simpa [φn, η] using sq_deriv_mul_cutoff_le (hdiff x) hC0 hC
  have hbound_int : Integrable (fun x => 2 * (deriv φ x) ^ 2 + 8 * C ^ 2 * φ x ^ 2) γ :=
    (hφ'.const_mul _).add ((hφ2.const_mul _))
  have hpt_deriv : ∀ x, Tendsto (fun n => deriv (φn n) x) atTop (𝓝 (deriv φ x)) := by
    intro x
    have hev : ∀ᶠ n : ℕ in atTop, deriv (φn n) x = deriv φ x := by
      obtain ⟨N, hN⟩ := exists_nat_gt |x|
      filter_upwards [eventually_ge_atTop N] with n hn
      have hlt : |x| < (n : ℝ) := lt_of_lt_of_le hN (Nat.cast_le.mpr hn)
      simpa [φn, η] using deriv_mul_cutoff_of_abs_lt (hdiff x) hlt
    exact tendsto_const_nhds.congr' (EventuallyEq.symm hev)
  have htend_energy : Tendsto (fun n => ∫ x, (deriv (φn n) x) ^ 2 ∂γ) atTop
      (𝓝 (∫ x, (deriv φ x) ^ 2 ∂γ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (μ := γ) (l := atTop)
      (bound := fun x => 2 * (deriv φ x) ^ 2 + 8 * C ^ 2 * φ x ^ 2)
      (F := fun n x => (deriv (φn n) x) ^ 2)
      (f := fun x => (deriv φ x) ^ 2)
      (Filter.Eventually.of_forall fun n =>
        ((hφnC n).continuous_deriv (WithTop.coe_le_coe.mpr le_top)).fun_pow
            2 |>.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun n => ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hdom n x)
      hbound_int
      (ae_of_all _ fun x => (hpt_deriv x).pow 2)
  have hpt_sq : ∀ x, Tendsto (fun n => φn n x ^ 2 + δ) atTop (𝓝 (φ x ^ 2 + δ)) := by
    intro x
    have hev : ∀ᶠ n : ℕ in atTop, φn n x = φ x := by
      obtain ⟨N, hN⟩ := exists_nat_gt |x|
      filter_upwards [eventually_ge_atTop N] with n hn
      have hlt : |x| ≤ (n : ℝ) := le_of_lt (lt_of_lt_of_le hN (Nat.cast_le.mpr hn))
      dsimp [φn, η]
      rw [oneDimCutoff_eq_one_of_abs_le hlt]
      simp
    have hconst : Tendsto (fun _ : ℕ => φ x ^ 2 + δ) atTop (𝓝 (φ x ^ 2 + δ)) :=
      tendsto_const_nhds
    exact hconst.congr' (by filter_upwards [hev] with n hn; simp [hn])
  have hdom_sq : ∀ n x, (φn n x) ^ 2 ≤ φ x ^ 2 := by
    intro n x
    have hmem := oneDimCutoff_mem_Icc (n : ℝ) x
    have hsq : oneDimCutoff (n : ℝ) x ^ 2 ≤ 1 :=
      (pow_le_pow_left₀ hmem.1 hmem.2 2).trans_eq (one_pow 2)
    simpa [φn, η, mul_pow] using
      mul_le_mul_of_nonneg_left hsq (sq_nonneg (φ x))
  have htend_mass : Tendsto (fun n => ∫ x, (φn n x ^ 2 + δ) ∂γ) atTop
      (𝓝 (∫ x, (φ x ^ 2 + δ) ∂γ)) := by
    have hsq_tend : Tendsto (fun n => ∫ x, (φn n x) ^ 2 ∂γ) atTop
        (𝓝 (∫ x, φ x ^ 2 ∂γ)) := by
      refine tendsto_integral_filter_of_dominated_convergence (μ := γ) (l := atTop)
        (bound := fun x => φ x ^ 2) (F := fun n x => (φn n x) ^ 2)
        (f := fun x => φ x ^ 2)
        (Filter.Eventually.of_forall fun n =>
          ((hφnC n).continuous.fun_pow 2).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun n => ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact hdom_sq n x)
        (by simpa [γ] using hφ2)
        (ae_of_all _ fun x => by
          have hev : ∀ᶠ n : ℕ in atTop, φn n x = φ x := by
            obtain ⟨N, hN⟩ := exists_nat_gt |x|
            filter_upwards [eventually_ge_atTop N] with n hn
            have hlt : |x| ≤ (n : ℝ) := le_of_lt (lt_of_lt_of_le hN (Nat.cast_le.mpr hn))
            dsimp [φn, η]
            rw [oneDimCutoff_eq_one_of_abs_le hlt]
            simp
          exact tendsto_const_nhds.congr' (by filter_upwards [hev] with n hn; simp [hn]))
    have hadd : ∀ n, ∫ x, (φn n x ^ 2 + δ) ∂γ = ∫ x, (φn n x) ^ 2 ∂γ + δ := by
      intro n
      have hint : Integrable (fun x => (φn n x) ^ 2) γ := by
        have hzero : ∀ y, (n : ℝ) + 1 ≤ |y| → (φn n y) ^ 2 = 0 := by
          intro y hy
          rw [hφn0 n y hy]
          simp
        have hcont_sq : Continuous (fun y => (φn n y) ^ 2) :=
          (hφnC n).continuous.fun_pow 2
        obtain ⟨B, hB⟩ := exists_abs_bound_of_zero_outside hcont_sq hzero
        exact integrable_of_abs_le hcont_sq.aestronglyMeasurable hB
      rw [integral_add hint (integrable_const _), integral_const, probReal_univ]
      simp
    have hlim_add : ∫ x, (φ x ^ 2 + δ) ∂γ = ∫ x, φ x ^ 2 ∂γ + δ := by
      rw [integral_add (by simpa [γ] using hφ2) (integrable_const _), integral_const,
        probReal_univ]
      simp
    simpa [hadd, hlim_add] using hsq_tend.add tendsto_const_nhds
  have happ := entropyExpr_le_of_nat_approx
    (hApprox := fun n x => φn n x ^ 2 + δ) (hLim := fun x => φ x ^ 2 + δ)
    (c := fun n => 2 * ∫ x, (deriv (φn n) x) ^ 2 ∂γ)
    (c0 := 2 * ∫ x, (deriv φ x) ^ 2 ∂γ)
    (fun n => ((hφnC n).continuous.fun_pow 2).fun_add continuous_const)
    ((hφ.continuous.fun_pow 2).fun_add continuous_const)
    (fun _ _ => add_nonneg (sq_nonneg _) hδ.le)
    (fun _ => add_nonneg (sq_nonneg _) hδ.le)
    hpt_sq (by simpa [γ] using htend_mass)
    (fun n => by simpa [γ] using hineq n)
    (fun n => mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
    (by simpa using htend_energy.const_mul 2)
    (mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
  simpa [γ] using happ

/-- **One-dimensional Gaussian logarithmic Sobolev inequality** with constant `2`. -/
theorem gaussian_logSobolev_oneDim (φ : ℝ → ℝ) (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (hLp : MemLp φ 2 (gaussianReal 0 1)) :
    entropyExpr (gaussianReal 0 1) (fun x => φ x ^ 2) ≤
      2 * ∫⁻ x, ENNReal.ofReal ((deriv φ x) ^ 2) ∂gaussianReal 0 1 := by
  let γ : Measure ℝ := gaussianReal 0 1
  by_cases htop : ∫⁻ x, ENNReal.ofReal ((deriv φ x) ^ 2) ∂γ = ⊤
  · rw [htop, ENNReal.mul_top (by norm_num : (2 : ℝ≥0∞) ≠ 0)]
    exact le_top
  · have hcont' : Continuous (deriv φ) :=
      (contDiff_infty_iff_deriv.mp hφ).2.continuous
    have hfm : AEStronglyMeasurable (fun x => (deriv φ x) ^ 2) γ :=
      (hcont'.fun_pow 2).aestronglyMeasurable
    have hint' : Integrable (fun x => (deriv φ x) ^ 2) γ :=
      (lintegral_ofReal_ne_top_iff_integrable hfm
        (ae_of_all _ fun _ => sq_nonneg _)).1 htop
    have hint2 : Integrable (fun x => φ x ^ 2) γ := by simpa [γ] using hLp.integrable_sq
    have hδ : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
    have hineq_δ : ∀ n : ℕ, entropyExpr γ (fun x => φ x ^ 2 + 1 / ((n : ℝ) + 1)) ≤
        ENNReal.ofReal (2 * ∫ x, (deriv φ x) ^ 2 ∂γ) := fun n => by
      simpa [γ] using gaussian_entropyExpr_sq_add_le hφ (by simpa [γ] using hint2)
        (by simpa [γ] using hint') (hδ n)
    have htend_mass : Tendsto (fun n : ℕ =>
        ∫ x, (φ x ^ 2 + 1 / ((n : ℝ) + 1)) ∂γ) atTop (𝓝 (∫ x, φ x ^ 2 ∂γ)) := by
      have hadd : ∀ n : ℕ, ∫ x, (φ x ^ 2 + 1 / ((n : ℝ) + 1)) ∂γ =
          ∫ x, φ x ^ 2 ∂γ + 1 / ((n : ℝ) + 1) := by
        intro n
        rw [integral_add hint2 (integrable_const _), integral_const, probReal_univ]
        simp
      have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        Tendsto.congr (fun n => (one_div ((n : ℝ) + 1)).symm)
          (tendsto_inv_atTop_zero.comp
            (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop))
      have hsum := (tendsto_const_nhds (x := ∫ x, φ x ^ 2 ∂γ)).add hinv
      rw [add_zero] at hsum
      exact Tendsto.congr (fun n => (hadd n).symm) hsum
    have happ := entropyExpr_le_of_nat_approx
      (hApprox := fun n x => φ x ^ 2 + 1 / ((n : ℝ) + 1))
      (hLim := fun x => φ x ^ 2)
      (c := fun _ : ℕ => 2 * ∫ x, (deriv φ x) ^ 2 ∂γ)
      (c0 := 2 * ∫ x, (deriv φ x) ^ 2 ∂γ)
      (fun _ => (hφ.continuous.fun_pow 2).fun_add continuous_const)
      (hφ.continuous.fun_pow 2)
      (fun _ _ => add_nonneg (sq_nonneg _) (by positivity))
      (fun x => sq_nonneg _)
      (fun x => by
        have hlim := (tendsto_const_nhds (x := φ x ^ 2)).add
          (Tendsto.congr (fun n : ℕ => (one_div ((n : ℝ) + 1)).symm)
            (tendsto_inv_atTop_zero.comp
              (tendsto_atTop_add_const_right atTop (1 : ℝ)
                tendsto_natCast_atTop_atTop)))
        rw [add_zero] at hlim
        exact hlim)
      (by simpa [γ] using htend_mass)
      (fun n => hineq_δ n)
      (fun _ => mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
      tendsto_const_nhds
      (mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
    have hnn : 0 ≤ᵐ[γ] fun x => (deriv φ x) ^ 2 := ae_of_all _ fun _ => sq_nonneg _
    have hrew : ENNReal.ofReal (2 * ∫ x, (deriv φ x) ^ 2 ∂γ) =
        2 * ∫⁻ x, ENNReal.ofReal ((deriv φ x) ^ 2) ∂γ := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ofReal_integral_eq_lintegral_ofReal hint' hnn]
      simp
    exact happ.trans_eq (by simpa [γ] using hrew)

end CKMA
