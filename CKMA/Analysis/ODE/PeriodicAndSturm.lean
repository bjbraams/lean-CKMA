/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.ODE.PeriodicAndSturm.Floquet
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Floquet decompositions and Sturm zero theorems

Normalized fundamental operators of periodic finite-dimensional linear systems,
complex Floquet factorization and real factorization with possible period doubling.
Sturm–Liouville solutions use a positive leading coefficient; separation is certified
by a nonzero Wronskian, and comparison additionally uses a positive weight.
Operator exponentials and differentiability use Mathlib's normed-space calculus.
Sources: GAPS 31.17 and 31.20.

## Main definitions

* `CKMA.IsSturmLiouvilleSolutionOn`: Classical solution of `-(p u')' + q u = μ w u` on an interval.
* `CKMA.sturmWronskian`: The Wronskian `u x * deriv v x - v x * deriv u x`.

## Main results

* `CKMA.floquet_complex`: Complex Floquet factorization of a periodic linear system (**31.17**).
* `CKMA.floquet_real`: Real Floquet factorization with period `2 * T`.
* `CKMA.sturm_separation`: Sturm separation theorem for independent solutions (**31.20**).
* `CKMA.sturm_comparison`: Sturm comparison theorem for solutions at ordered spectral parameters.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology Set intervalIntegral

/-- **31.17**: complex Floquet factorization of a periodic linear system. -/
theorem floquet_complex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] (A U : ℝ → E →L[ℂ] E) {T : ℝ} (hT : 0 < T)
    (hA : Continuous A) (hperiod : Function.Periodic A T) (hU : IsFundamentalOperator A U) :
    ∃ (B : E →L[ℂ] E) (P : ℝ → E →L[ℂ] E), Function.Periodic P T ∧
      ContDiff ℝ 1 P ∧ (∀ t, (P t).IsInvertible) ∧
      ∀ t, U t = P t * NormedSpace.exp ((t : ℂ) • B) := by
  sorry

/-- A real Floquet decomposition may require period `2T`. -/
theorem floquet_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (A U : ℝ → E →L[ℝ] E) {T : ℝ} (hT : 0 < T)
    (hA : Continuous A) (hperiod : Function.Periodic A T) (hU : IsFundamentalOperator A U) :
    ∃ (B : E →L[ℝ] E) (P : ℝ → E →L[ℝ] E), Function.Periodic P (2 * T) ∧
      ContDiff ℝ 1 P ∧ (∀ t, (P t).IsInvertible) ∧
      ∀ t, U t = P t * NormedSpace.exp (t • B) := by
  sorry

/-- A classical solution of `-(p u')' + q u = λ w u` on an interval. -/
def IsSturmLiouvilleSolutionOn (p q w : ℝ → ℝ) (μ : ℝ) (u : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ContDiffOn ℝ 2 u I ∧ ∀ x ∈ I, -deriv (fun t ↦ p t * deriv u t) x + q x * u x = μ * w x * u x

/-- The ordinary Wronskian, used only at a finite point to certify independence. -/
def sturmWronskian (u v : ℝ → ℝ) (x : ℝ) : ℝ := u x * deriv v x - v x * deriv u x

/-- On the open interval, `ContDiffOn` supplies an ambient derivative. -/
private lemma contDiffAt_of_Icc {n : WithTop ℕ∞} {f : ℝ → ℝ} {a b x : ℝ}
    (hf : ContDiffOn ℝ n f (Icc a b)) (hx : x ∈ Ioo a b) : ContDiffAt ℝ n f x :=
  hf.contDiffAt (Icc_mem_nhds_iff.mpr hx)

/-- The differentiated leading term of a Sturm–Liouville solution, at an interior point. -/
private lemma hasDerivAt_sturmLeading {a b : ℝ} (p q w u : ℝ → ℝ) (μ : ℝ)
    (hp : ContDiffOn ℝ 1 p (Icc a b))
    (hu : IsSturmLiouvilleSolutionOn p q w μ u (Icc a b)) {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (fun t ↦ p t * deriv u t) ((q x - μ * w x) * u x) x := by
  have hux : ContDiffAt ℝ 2 u x := contDiffAt_of_Icc hu.1 hx
  have hpx : ContDiffAt ℝ 1 p x := contDiffAt_of_Icc hp hx
  have hdu : DifferentiableAt ℝ (deriv u) x :=
    (hux.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdiff : DifferentiableAt ℝ (fun t ↦ p t * deriv u t) x :=
    (hpx.differentiableAt (by norm_num)).mul hdu
  have hSL := hu.2 x (Ioo_subset_Icc_self hx)
  have hval : deriv (fun t ↦ p t * deriv u t) x = (q x - μ * w x) * u x := by
    have hD : deriv (fun t ↦ p t * deriv u t) x =
        q x * u x - μ * w x * u x := by linear_combination -hSL
    linarith [hD]
  simpa [hval] using hdiff.hasDerivAt

/-- Interior derivative of `p` times the Wronskian, equal to `(μ - ν) w u v`. -/
private lemma hasDerivAt_sturmCross {a b : ℝ} (p q w u v : ℝ → ℝ) (μ ν : ℝ)
    (hp : ContDiffOn ℝ 1 p (Icc a b))
    (hu : IsSturmLiouvilleSolutionOn p q w μ u (Icc a b))
    (hv : IsSturmLiouvilleSolutionOn p q w ν v (Icc a b)) {x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (fun t ↦ u t * (p t * deriv v t) - v t * (p t * deriv u t))
      ((μ - ν) * w x * u x * v x) x := by
  have hφu := hasDerivAt_sturmLeading p q w u μ hp hu hx
  have hφv := hasDerivAt_sturmLeading p q w v ν hp hv hx
  have hu' : DifferentiableAt ℝ u x :=
    (contDiffAt_of_Icc hu.1 hx).differentiableAt (by norm_num)
  have hv' : DifferentiableAt ℝ v x :=
    (contDiffAt_of_Icc hv.1 hx).differentiableAt (by norm_num)
  have hmul := (hu'.hasDerivAt.mul hφv).sub (hv'.hasDerivAt.mul hφu)
  exact hmul.congr_deriv (by ring)

/-- A continuous function with no zero on an open interval has constant strict sign. -/
private lemma sign_const_of_ne_zero {a b : ℝ} (hab : a < b) {u : ℝ → ℝ}
    (hu : ContinuousOn u (Icc a b)) (hno : ∀ x ∈ Ioo a b, u x ≠ 0) :
    (∀ x ∈ Ioo a b, 0 < u x) ∨ (∀ x ∈ Ioo a b, u x < 0) := by
  have hc : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  rcases lt_or_gt_of_ne (hno _ hc) with hneg | hpos
  · refine Or.inr fun x hx ↦ ?_
    by_contra hnot
    have hxpos : 0 < u x := lt_of_le_of_ne (not_lt.mp hnot) (hno x hx).symm
    rcases lt_trichotomy x ((a + b) / 2) with hlt | heq | hgt
    · have hsub : ContinuousOn u (Icc x ((a + b) / 2)) :=
        hu.mono fun y hy ↦ ⟨hx.1.le.trans hy.1, hy.2.trans hc.2.le⟩
      have h0 : (0 : ℝ) ∈ Ioo (u ((a + b) / 2)) (u x) := ⟨hneg, hxpos⟩
      have himg := intermediate_value_Ioo' (le_of_lt hlt) hsub h0
      rw [mem_image] at himg
      obtain ⟨z, hz, hz0⟩ := himg
      exact hno z ⟨hx.1.trans hz.1, hz.2.trans hc.2⟩ hz0
    · rw [heq] at hxpos
      exact lt_asymm hxpos hneg
    · have hsub : ContinuousOn u (Icc ((a + b) / 2) x) :=
        hu.mono fun y hy ↦ ⟨hc.1.le.trans hy.1, hy.2.trans hx.2.le⟩
      have h0 : (0 : ℝ) ∈ Ioo (u ((a + b) / 2)) (u x) := ⟨hneg, hxpos⟩
      have himg := intermediate_value_Ioo (le_of_lt hgt) hsub h0
      rw [mem_image] at himg
      obtain ⟨z, hz, hz0⟩ := himg
      exact hno z ⟨hc.1.trans hz.1, hz.2.trans hx.2⟩ hz0
  · refine Or.inl fun x hx ↦ ?_
    by_contra hnot
    have hxneg : u x < 0 := lt_of_le_of_ne (not_lt.mp hnot) (hno x hx)
    rcases lt_trichotomy x ((a + b) / 2) with hlt | heq | hgt
    · have hsub : ContinuousOn u (Icc x ((a + b) / 2)) :=
        hu.mono fun y hy ↦ ⟨hx.1.le.trans hy.1, hy.2.trans hc.2.le⟩
      have h0 : (0 : ℝ) ∈ Ioo (u x) (u ((a + b) / 2)) := ⟨hxneg, hpos⟩
      have himg := intermediate_value_Ioo (le_of_lt hlt) hsub h0
      rw [mem_image] at himg
      obtain ⟨z, hz, hz0⟩ := himg
      exact hno z ⟨hx.1.trans hz.1, hz.2.trans hc.2⟩ hz0
    · rw [heq] at hxneg
      exact lt_asymm hpos hxneg
    · have hsub : ContinuousOn u (Icc ((a + b) / 2) x) :=
        hu.mono fun y hy ↦ ⟨hc.1.le.trans hy.1, hy.2.trans hx.2.le⟩
      have h0 : (0 : ℝ) ∈ Ioo (u x) (u ((a + b) / 2)) := ⟨hxneg, hpos⟩
      have himg := intermediate_value_Ioo' (le_of_lt hgt) hsub h0
      rw [mem_image] at himg
      obtain ⟨z, hz, hz0⟩ := himg
      exact hno z ⟨hc.1.trans hz.1, hz.2.trans hx.2⟩ hz0

/-- A strictly increasing continuous function running from `-∞` to `+∞` has one root. -/
private lemma existsUnique_strictMono_zero {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo a b)) (hmono : StrictMonoOn f (Ioo a b))
    (ha : Tendsto f (𝓝[>] a) atBot) (hb : Tendsto f (𝓝[<] b) atTop) :
    ∃! x, x ∈ Ioo a b ∧ f x = 0 := by
  have hmem_a : Ioo a b ∈ 𝓝[>] a := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact self_mem_nhdsWithin
  have hmem_b : Ioo a b ∈ 𝓝[<] b := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hab]
    exact self_mem_nhdsWithin
  obtain ⟨c, hfc, hc⟩ :=
    ((ha.eventually (Iio_mem_atBot (0 : ℝ))).and
      (eventually_of_mem hmem_a fun _ hx ↦ hx)).exists
  obtain ⟨d, hfd, hd⟩ :=
    ((hb.eventually (Ioi_mem_atTop (0 : ℝ))).and
      (eventually_of_mem hmem_b fun _ hx ↦ hx)).exists
  have hcd : c < d := by
    by_contra hle
    have hle' : d ≤ c := le_of_not_gt hle
    have hfd_neg : f d < 0 := by
      rcases hle'.eq_or_lt with rfl | hlt
      · exact hfc
      · exact (hmono hd hc hlt).trans hfc
    exact lt_asymm hfd hfd_neg
  have hcont : ContinuousOn f (Icc c d) :=
    hf.mono fun x hx ↦ ⟨hc.1.trans_le hx.1, hx.2.trans_lt hd.2⟩
  have himg := intermediate_value_Ioo (le_of_lt hcd) hcont ⟨hfc, hfd⟩
  rw [mem_image] at himg
  obtain ⟨z, hz, hz0⟩ := himg
  have hzab : z ∈ Ioo a b := ⟨hc.1.trans hz.1, hz.2.trans hd.2⟩
  refine ⟨z, ⟨hzab, hz0⟩, ?_⟩
  rintro y ⟨hy, hy0⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (hmono hy hzab hlt).ne (hy0.trans hz0.symm)
  · exact (hmono hzab hy hgt).ne (hz0.trans hy0.symm)

/-- Quotient blowing up on the right of a simple root. -/
private lemma tendsto_div_nhdsGT {a : ℝ} {u v : ℝ → ℝ} {u' va : ℝ}
    (hua : u a = 0) (hu' : u' ≠ 0) (hva : va ≠ 0)
    (hslope : Tendsto (fun x ↦ (u x - u a) / (x - a)) (𝓝[>] a) (𝓝 u'))
    (hv : Tendsto v (𝓝[>] a) (𝓝 va)) :
    Tendsto (fun x ↦ v x / u x) (𝓝[>] a) (if 0 < va / u' then atTop else atBot) := by
  have hsub : Tendsto (fun x ↦ x - a) (𝓝[>] a) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hbase : Tendsto (fun x ↦ x - a) (𝓝[>] a) (𝓝 0) := by
        have hraw := ((continuous_id.sub (continuous_const (y := a))).tendsto a).mono_left
          (nhdsWithin_le_nhds (s := Ioi a))
        simp only [id_eq, Pi.sub_apply, sub_self] at hraw
        exact hraw
      exact hbase
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_pos.mpr hx
  have hinv : Tendsto (fun x ↦ (x - a)⁻¹) (𝓝[>] a) atTop := hsub.inv_tendsto_nhdsGT_zero
  have hquot : Tendsto (fun x ↦ v x / ((u x - u a) / (x - a))) (𝓝[>] a) (𝓝 (va / u')) :=
    hv.div hslope hu'
  have hne : ({(0 : ℝ)}ᶜ) ∈ 𝓝 u' := isOpen_compl_singleton.mem_nhds (by simpa using hu')
  have hident :
      (fun x ↦ v x / ((u x - u a) / (x - a)) * (x - a)⁻¹) =ᶠ[𝓝[>] a] fun x ↦ v x / u x := by
    filter_upwards [self_mem_nhdsWithin, hslope.eventually hne] with x hx hsx
    have hxa : x - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx)
    have hmul : ((u x - u a) / (x - a)) * (x - a) = u x := by
      rw [div_mul_cancel₀ _ hxa, hua, sub_zero]
    calc v x / ((u x - u a) / (x - a)) * (x - a)⁻¹
        = v x * (((u x - u a) / (x - a))⁻¹ * (x - a)⁻¹) := by rw [div_eq_mul_inv, mul_assoc]
      _ = v x * (((u x - u a) / (x - a)) * (x - a))⁻¹ := by
          rw [mul_comm (((u x - u a) / (x - a))⁻¹), ← mul_inv_rev]
      _ = v x * (u x)⁻¹ := by rw [hmul]
      _ = v x / u x := by rw [div_eq_mul_inv]
  split_ifs with hsign
  · exact (hquot.pos_mul_atTop hsign hinv).congr' hident
  · have hneg : va / u' < 0 := lt_of_le_of_ne (not_lt.mp hsign) (div_ne_zero hva hu')
    exact (hquot.neg_mul_atTop hneg hinv).congr' hident

/-- Quotient blowing up on the left of a simple root. -/
private lemma tendsto_div_nhdsLT {b : ℝ} {u v : ℝ → ℝ} {u' vb : ℝ}
    (hub : u b = 0) (hu' : u' ≠ 0) (hvb : vb ≠ 0)
    (hslope : Tendsto (fun x ↦ (u x - u b) / (x - b)) (𝓝[<] b) (𝓝 u'))
    (hv : Tendsto v (𝓝[<] b) (𝓝 vb)) :
    Tendsto (fun x ↦ v x / u x) (𝓝[<] b) (if 0 < vb / u' then atBot else atTop) := by
  have hsub : Tendsto (fun x ↦ x - b) (𝓝[<] b) (𝓝[<] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hbase : Tendsto (fun x ↦ x - b) (𝓝[<] b) (𝓝 0) := by
        have hraw := ((continuous_id.sub (continuous_const (y := b))).tendsto b).mono_left
          (nhdsWithin_le_nhds (s := Iio b))
        simp only [id_eq, Pi.sub_apply, sub_self] at hraw
        exact hraw
      exact hbase
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_neg.mpr hx
  have hinv : Tendsto (fun x ↦ (x - b)⁻¹) (𝓝[<] b) atBot := hsub.inv_tendsto_nhdsLT_zero
  have hquot : Tendsto (fun x ↦ v x / ((u x - u b) / (x - b))) (𝓝[<] b) (𝓝 (vb / u')) :=
    hv.div hslope hu'
  have hne : ({(0 : ℝ)}ᶜ) ∈ 𝓝 u' := isOpen_compl_singleton.mem_nhds (by simpa using hu')
  have hident :
      (fun x ↦ v x / ((u x - u b) / (x - b)) * (x - b)⁻¹) =ᶠ[𝓝[<] b] fun x ↦ v x / u x := by
    filter_upwards [self_mem_nhdsWithin, hslope.eventually hne] with x hx hsx
    have hxb : x - b ≠ 0 := sub_ne_zero.mpr (ne_of_lt hx)
    have hmul : ((u x - u b) / (x - b)) * (x - b) = u x := by
      rw [div_mul_cancel₀ _ hxb, hub, sub_zero]
    calc v x / ((u x - u b) / (x - b)) * (x - b)⁻¹
        = v x * (((u x - u b) / (x - b))⁻¹ * (x - b)⁻¹) := by rw [div_eq_mul_inv, mul_assoc]
      _ = v x * (((u x - u b) / (x - b)) * (x - b))⁻¹ := by
          rw [mul_comm (((u x - u b) / (x - b))⁻¹), ← mul_inv_rev]
      _ = v x * (u x)⁻¹ := by rw [hmul]
      _ = v x / u x := by rw [div_eq_mul_inv]
  split_ifs with hsign
  · exact (hquot.pos_mul_atBot hsign hinv).congr' hident
  · have hneg : vb / u' < 0 := lt_of_le_of_ne (not_lt.mp hsign) (div_ne_zero hvb hu')
    exact (hquot.neg_mul_atBot hneg hinv).congr' hident

/-- The difference quotient at the left endpoint tends to the one-sided derivative. -/
private lemma tendsto_slope_nhdsGT_derivWithin {a b : ℝ} (hab : a < b) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Icc a b)) :
    Tendsto (fun x ↦ (u x - u a) / (x - a)) (𝓝[>] a) (𝓝 (derivWithin u (Icc a b) a)) := by
  have hdw : HasDerivWithinAt u (derivWithin u (Icc a b) a) (Icc a b) a :=
    ((hu.differentiableOn (by norm_num)) a ⟨le_rfl, hab.le⟩).hasDerivWithinAt
  have htend := hasDerivWithinAt_iff_tendsto_slope.mp hdw
  simp_rw [slope_fun_def_field] at htend
  rwa [Icc_sdiff_left, nhdsWithin_Ioc_eq_nhdsGT hab] at htend

/-- The difference quotient at the right endpoint tends to the one-sided derivative. -/
private lemma tendsto_slope_nhdsLT_derivWithin {a b : ℝ} (hab : a < b) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Icc a b)) :
    Tendsto (fun x ↦ (u x - u b) / (x - b)) (𝓝[<] b) (𝓝 (derivWithin u (Icc a b) b)) := by
  have hdw : HasDerivWithinAt u (derivWithin u (Icc a b) b) (Icc a b) b :=
    ((hu.differentiableOn (by norm_num)) b ⟨hab.le, le_rfl⟩).hasDerivWithinAt
  have htend := hasDerivWithinAt_iff_tendsto_slope.mp hdw
  simp_rw [slope_fun_def_field] at htend
  rwa [Icc_sdiff_right, nhdsWithin_Ico_eq_nhdsLT hab] at htend

/-- Positive values on `(a, b)` force a nonnegative left derivative at `a`. -/
private lemma derivWithin_left_nonneg {a b : ℝ} (hab : a < b) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Icc a b)) (hua : u a = 0)
    (hpos : ∀ x ∈ Ioo a b, 0 < u x) : 0 ≤ derivWithin u (Icc a b) a := by
  refine ge_of_tendsto (tendsto_slope_nhdsGT_derivWithin hab hu) ?_
  have hmem : Ioo a b ∈ 𝓝[>] a := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact self_mem_nhdsWithin
  filter_upwards [hmem] with x hx
  exact (div_pos (by simpa [hua] using hpos x hx) (sub_pos.mpr hx.1)).le

/-- Positive values on `(a, b)` force a nonpositive right derivative at `b`. -/
private lemma derivWithin_right_nonpos {a b : ℝ} (hab : a < b) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Icc a b)) (hub : u b = 0)
    (hpos : ∀ x ∈ Ioo a b, 0 < u x) : derivWithin u (Icc a b) b ≤ 0 := by
  refine le_of_tendsto (tendsto_slope_nhdsLT_derivWithin hab hu) ?_
  have hmem : Ioo a b ∈ 𝓝[<] b := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hab]
    exact self_mem_nhdsWithin
  filter_upwards [hmem] with x hx
  have hden : x - b < 0 := sub_neg.mpr hx.2
  have hnum : 0 < u x - u b := by simpa [hub] using hpos x hx
  exact div_nonpos_of_nonneg_of_nonpos hnum.le hden.le

/-- A nonnegative continuous limit from the right. -/
private lemma left_endpoint_nonneg {a b : ℝ} (hab : a < b) {v : ℝ → ℝ}
    (hv : ContinuousOn v (Icc a b)) (hpos : ∀ x ∈ Ioo a b, 0 < v x) : 0 ≤ v a := by
  have hle : 𝓝[>] a ≤ 𝓝[Icc a b] a :=
    (nhdsWithin_Ioo_eq_nhdsGT hab).symm.le.trans (nhdsWithin_mono a Ioo_subset_Icc_self)
  refine ge_of_tendsto ((hv.continuousWithinAt ⟨le_rfl, hab.le⟩).tendsto.mono_left hle) ?_
  filter_upwards [by rw [← nhdsWithin_Ioo_eq_nhdsGT hab]; exact self_mem_nhdsWithin] with x hx
  exact (hpos x hx).le

/-- A nonnegative continuous limit from the left. -/
private lemma right_endpoint_nonneg {a b : ℝ} (hab : a < b) {v : ℝ → ℝ}
    (hv : ContinuousOn v (Icc a b)) (hpos : ∀ x ∈ Ioo a b, 0 < v x) : 0 ≤ v b := by
  have hle : 𝓝[<] b ≤ 𝓝[Icc a b] b :=
    (nhdsWithin_Ioo_eq_nhdsLT hab).symm.le.trans (nhdsWithin_mono b Ioo_subset_Icc_self)
  refine ge_of_tendsto ((hv.continuousWithinAt ⟨hab.le, le_rfl⟩).tendsto.mono_left hle) ?_
  filter_upwards [by rw [← nhdsWithin_Ioo_eq_nhdsLT hab]; exact self_mem_nhdsWithin] with x hx
  exact (hpos x hx).le

/-- The negative of a Sturm–Liouville solution is a solution with the same parameter. -/
private lemma IsSturmLiouvilleSolutionOn.neg {p q w u : ℝ → ℝ} {μ : ℝ} {I : Set ℝ}
    (hu : IsSturmLiouvilleSolutionOn p q w μ u I) :
    IsSturmLiouvilleSolutionOn p q w μ (fun t ↦ -u t) I := by
  refine ⟨hu.1.neg, fun x hx ↦ ?_⟩
  have hfun : (fun t ↦ p t * deriv (fun s ↦ -u s) t) = fun t ↦ -(p t * deriv u t) := by
    funext t
    rw [deriv.fun_neg, mul_neg]
  rw [hfun, deriv.fun_neg]
  beta_reduce
  linear_combination -hu.2 x hx

/-- **Abel's identity**: for two solutions with the same parameter, `p` times their Wronskian is
constant on `(a, b)`. -/
private lemma exists_mul_sturmWronskian_eq_const {a b μ : ℝ} {p q w u v : ℝ → ℝ}
    (hp : ContDiffOn ℝ 1 p (Icc a b))
    (hu : IsSturmLiouvilleSolutionOn p q w μ u (Icc a b))
    (hv : IsSturmLiouvilleSolutionOn p q w μ v (Icc a b)) :
    ∃ c, ∀ x ∈ Ioo a b, p x * sturmWronskian u v x = c := by
  have hHas : ∀ x ∈ Ioo a b, HasDerivAt (fun t ↦ p t * sturmWronskian u v t) 0 x := by
    intro x hx
    have hcross := hasDerivAt_sturmCross p q w u v μ μ hp hu hv hx
    have hfun : (fun t ↦ u t * (p t * deriv v t) - v t * (p t * deriv u t)) =
        fun t ↦ p t * sturmWronskian u v t := by
      funext t
      simp only [sturmWronskian]
      ring
    rw [hfun] at hcross
    exact hcross.congr_deriv (by ring)
  exact isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun x hx ↦ (hHas x hx).differentiableAt.differentiableWithinAt)
    (fun x hx ↦ (hHas x hx).deriv)

/-- At a point of `[a, b]`, the derivative of a `C²` function on `[a, b]` tends along `(a, b)`
to the derivative within `[a, b]`. -/
private lemma tendsto_deriv_nhdsWithin_Ioo {a b x : ℝ} (hab : a < b) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Icc a b)) (hx : x ∈ Icc a b) :
    Tendsto (deriv u) (𝓝[Ioo a b] x) (𝓝 (derivWithin u (Icc a b) x)) := by
  have hcont := hu.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)
  refine ((hcont x hx).tendsto.mono_left (nhdsWithin_mono x Ioo_subset_Icc_self)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact derivWithin_of_mem_nhds (Icc_mem_nhds_iff.mpr hy)

/-- If `p` times the Wronskian is constant on `(a, b)`, the same constant is obtained at a
point of `[a, b]` from the Wronskian formed with derivatives within `[a, b]`. -/
private lemma const_eq_mul_sturmWronskian_of_mem_Icc {a b x c : ℝ} (hab : a < b)
    {p u v : ℝ → ℝ} (hp : ContinuousOn p (Icc a b)) (hu : ContDiffOn ℝ 2 u (Icc a b))
    (hv : ContDiffOn ℝ 2 v (Icc a b)) (hc : ∀ y ∈ Ioo a b, p y * sturmWronskian u v y = c)
    (hx : x ∈ Icc a b) :
    c = p x * (u x * derivWithin v (Icc a b) x - v x * derivWithin u (Icc a b) x) := by
  have hne : (𝓝[Ioo a b] x).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo hab.ne]
    exact hx
  have hle : 𝓝[Ioo a b] x ≤ 𝓝[Icc a b] x := nhdsWithin_mono x Ioo_subset_Icc_self
  have hW : Tendsto (sturmWronskian u v) (𝓝[Ioo a b] x)
      (𝓝 (u x * derivWithin v (Icc a b) x - v x * derivWithin u (Icc a b) x)) :=
    (((hu.continuousOn x hx).tendsto.mono_left hle).mul
      (tendsto_deriv_nhdsWithin_Ioo hab hv hx)).sub
      (((hv.continuousOn x hx).tendsto.mono_left hle).mul
        (tendsto_deriv_nhdsWithin_Ioo hab hu hx))
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_)
    (((hp x hx).tendsto.mono_left hle).mul hW)
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (hc y hy).symm

/-- **31.20**, separation: independent solutions have exactly one intervening zero. -/
theorem sturm_separation {a b : ℝ} (hab : a < b) (p q w u v : ℝ → ℝ) (μ : ℝ)
    (hp : ContDiffOn ℝ 1 p (Set.Icc a b)) (hp_pos : ∀ x ∈ Set.Icc a b, 0 < p x)
    (hu : IsSturmLiouvilleSolutionOn p q w μ u (Set.Icc a b))
    (hv : IsSturmLiouvilleSolutionOn p q w μ v (Set.Icc a b))
    (hua : u a = 0) (hub : u b = 0) (hno : ∀ x ∈ Set.Ioo a b, u x ≠ 0)
    (hind : sturmWronskian u v a ≠ 0) : ∃! x, x ∈ Set.Ioo a b ∧ v x = 0 := by
  let W := sturmWronskian u v
  obtain ⟨c, hc⟩ := exists_mul_sturmWronskian_eq_const hp hu hv
  have hpa : 0 < p a := hp_pos a ⟨le_rfl, hab.le⟩
  have hpb : 0 < p b := hp_pos b ⟨hab.le, le_rfl⟩
  have hdu_a : DifferentiableAt ℝ u a := by
    by_contra hnot
    exact hind (by simp [sturmWronskian, hua, deriv_zero_of_not_differentiableAt hnot])
  have hu'a : derivWithin u (Icc a b) a = deriv u a :=
    hdu_a.hasDerivAt.hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc hab a ⟨le_rfl, hab.le⟩)
  -- The constant `c` at both endpoints.
  have hc_eq : c = p a * W a := by
    have h := const_eq_mul_sturmWronskian_of_mem_Icc hab hp.continuousOn hu.1 hv.1 hc
      ⟨le_rfl, hab.le⟩
    rw [h, hu'a]
    simp [W, sturmWronskian, hua]
  have hc_ne : c ≠ 0 := hc_eq ▸ mul_ne_zero hpa.ne' hind
  let ub : ℝ := derivWithin u (Icc a b) b
  have hWb : -(v b * ub) = c / p b := by
    have h := const_eq_mul_sturmWronskian_of_mem_Icc hab hp.continuousOn hu.1 hv.1 hc
      ⟨hab.le, le_rfl⟩
    rw [h, hub]
    field_simp [hpb.ne']
    ring
  have hv_a : v a ≠ 0 := by
    intro hv0
    exact hind (by simp [sturmWronskian, hua, hv0])
  have hu'a_ne : deriv u a ≠ 0 := by
    intro hu0
    exact hind (by simp [sturmWronskian, hua, hu0])
  have hv_b : v b ≠ 0 := by
    intro hv0
    have : c / p b = 0 := by simpa [hv0] using hWb.symm
    exact hc_ne (((div_eq_zero_iff.mp this).resolve_right hpb.ne'))
  have hu'b_ne : ub ≠ 0 := by
    intro hu0
    have : c / p b = 0 := by simpa [hu0] using hWb.symm
    exact hc_ne (((div_eq_zero_iff.mp this).resolve_right hpb.ne'))
  -- The quotient `v / u` is strictly monotone and blows up at both ends.
  have hle_a : 𝓝[>] a ≤ 𝓝[Icc a b] a :=
    (nhdsWithin_Ioo_eq_nhdsGT hab).symm.le.trans (nhdsWithin_mono a Ioo_subset_Icc_self)
  have hle_b : 𝓝[<] b ≤ 𝓝[Icc a b] b :=
    (nhdsWithin_Ioo_eq_nhdsLT hab).symm.le.trans (nhdsWithin_mono b Ioo_subset_Icc_self)
  have hlim_v := (hv.1.continuousOn.continuousWithinAt ⟨le_rfl, hab.le⟩).tendsto.mono_left hle_a
  have hlim_v_b := (hv.1.continuousOn.continuousWithinAt ⟨hab.le, le_rfl⟩).tendsto.mono_left hle_b
  have hslope_a : Tendsto (fun x ↦ (u x - u a) / (x - a)) (𝓝[>] a) (𝓝 (deriv u a)) := by
    simpa [hu'a] using tendsto_slope_nhdsGT_derivWithin hab hu.1
  have hslope_b := tendsto_slope_nhdsLT_derivWithin hab hu.1
  let ratio := fun t ↦ v t / u t
  have hratio_cont : ContinuousOn ratio (Ioo a b) :=
    (hv.1.continuousOn.mono Ioo_subset_Icc_self).div
      (hu.1.continuousOn.mono Ioo_subset_Icc_self) hno
  have hratio_deriv : ∀ x ∈ Ioo a b, deriv ratio x = W x / (u x) ^ 2 := by
    intro x hx
    have hu' := (contDiffAt_of_Icc hu.1 hx).differentiableAt (by norm_num)
    have hv' := (contDiffAt_of_Icc hv.1 hx).differentiableAt (by norm_num)
    have hd := deriv_div hv' hu' (hno x hx)
    have heq : (v / u) = fun t ↦ v t / u t := by
      ext t
      simp [Pi.div_apply]
    rw [heq] at hd
    rw [hd]
    simp only [W, sturmWronskian]
    ring
  have hW_eq : ∀ x ∈ Ioo a b, W x = c / p x := by
    intro x hx
    rw [eq_div_iff (hp_pos x (Ioo_subset_Icc_self hx)).ne', mul_comm]
    exact hc x hx
  have hWa : W a = c / p a := by rw [hc_eq]; field_simp [hpa.ne']
  have hdiv_a : v a / deriv u a = -(c / p a) / (deriv u a) ^ 2 := by
    have hW : W a = -(v a * deriv u a) := by simp [W, sturmWronskian, hua]
    rw [← hWa, hW]
    field_simp [hu'a_ne]
  have hdiv_b : v b / ub = -(c / p b) / ub ^ 2 := by
    have hmul : v b * ub = -(c / p b) := (neg_eq_iff_eq_neg).mp hWb
    rw [← hmul]
    exact (div_eq_div_iff hu'b_ne (pow_ne_zero 2 hu'b_ne)).mpr (by ring)
  have hratio_a := tendsto_div_nhdsGT hua hu'a_ne hv_a hslope_a hlim_v
  have hratio_b := tendsto_div_nhdsLT hub hu'b_ne hv_b hslope_b hlim_v_b
  rcases lt_or_gt_of_ne hc_ne with hc_neg | hc_pos
  · have hlt_a : 0 < v a / deriv u a := by
      rw [hdiv_a]
      exact div_pos (neg_pos.mpr (div_neg_of_neg_of_pos hc_neg hpa))
        (sq_pos_of_ne_zero hu'a_ne)
    have hlt_b : 0 < v b / ub := by
      rw [hdiv_b]
      exact div_pos (neg_pos.mpr (div_neg_of_neg_of_pos hc_neg hpb))
        (sq_pos_of_ne_zero hu'b_ne)
    rw [ite_eq_left hlt_a] at hratio_a
    rw [ite_eq_left hlt_b] at hratio_b
    have hmono : StrictMonoOn (fun x ↦ -ratio x) (Ioo a b) := by
      refine strictMonoOn_of_deriv_pos (convex_Ioo a b) hratio_cont.neg ?_
      intro x hx
      rw [isOpen_Ioo.interior_eq] at hx
      rw [deriv.fun_neg, hratio_deriv x hx, hW_eq x hx, neg_pos]
      exact div_neg_of_neg_of_pos (div_neg_of_neg_of_pos hc_neg
        (hp_pos x (Ioo_subset_Icc_self hx))) (sq_pos_of_ne_zero (hno x hx))
    obtain ⟨x, ⟨hx, hx0⟩, huniq⟩ := existsUnique_strictMono_zero hab hratio_cont.neg hmono
      (tendsto_neg_atTop_atBot.comp hratio_a) (tendsto_neg_atBot_atTop.comp hratio_b)
    refine ⟨x, ⟨hx, ?_⟩, ?_⟩
    · have hx0' : -(v x / u x) = 0 := by simpa [ratio] using hx0
      exact ((div_eq_zero_iff).mp (neg_eq_zero.mp hx0')).resolve_right (hno x hx)
    · intro y hy
      exact huniq y ⟨hy.1, by simp [ratio, hy.2]⟩
  · have hlt_a : v a / deriv u a < 0 := by
      rw [hdiv_a]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos (div_pos hc_pos hpa))
        (sq_pos_of_ne_zero hu'a_ne)
    have hlt_b : v b / ub < 0 := by
      rw [hdiv_b]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos (div_pos hc_pos hpb))
        (sq_pos_of_ne_zero hu'b_ne)
    rw [ite_eq_right (not_lt_of_gt hlt_a)] at hratio_a
    rw [ite_eq_right (not_lt_of_gt hlt_b)] at hratio_b
    have hmono : StrictMonoOn ratio (Ioo a b) := by
      refine strictMonoOn_of_deriv_pos (convex_Ioo a b) hratio_cont ?_
      intro x hx
      rw [isOpen_Ioo.interior_eq] at hx
      rw [hratio_deriv x hx, hW_eq x hx]
      exact div_pos (div_pos hc_pos (hp_pos x (Ioo_subset_Icc_self hx)))
        (sq_pos_of_ne_zero (hno x hx))
    obtain ⟨x, ⟨hx, hx0⟩, huniq⟩ := existsUnique_strictMono_zero (f := ratio) hab hratio_cont
      hmono hratio_a hratio_b
    refine ⟨x, ⟨hx, (div_eq_zero_iff.mp (by simpa [ratio] using hx0)).resolve_right (hno x hx)⟩, ?_⟩
    intro y hy
    exact huniq y ⟨hy.1, by simp [ratio, hy.2]⟩

/-- The positive case of `sturm_comparison`: if `μ < ν`, a solution `u` for `μ` that is positive
on `(a, b)` and vanishes at both ends rules out a solution for `ν` positive on `(a, b)`, since
the integral of `(ν - μ) w u v` would be both positive and nonpositive. -/
private lemma sturm_comparison_of_pos {a b μ ν : ℝ} (hab : a < b) (hμν : μ < ν)
    {p q w u v : ℝ → ℝ} (hp : ContDiffOn ℝ 1 p (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hp_pos : ∀ x ∈ Icc a b, 0 < p x) (hw_pos : ∀ x ∈ Icc a b, 0 < w x)
    (hu : IsSturmLiouvilleSolutionOn p q w μ u (Icc a b))
    (hv : IsSturmLiouvilleSolutionOn p q w ν v (Icc a b))
    (hua : u a = 0) (hub : u b = 0) (hu_pos : ∀ x ∈ Ioo a b, 0 < u x)
    (hv_pos : ∀ x ∈ Ioo a b, 0 < v x) : False := by
  let s : Set ℝ := Icc a b
  let du := derivWithin u s
  let dv := derivWithin v s
  let F : ℝ → ℝ := fun t ↦ v t * (p t * du t) - u t * (p t * dv t)
  let g : ℝ → ℝ := fun x ↦ (ν - μ) * w x * u x * v x
  have hdu_cont := hu.1.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)
  have hdv_cont := hv.1.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)
  have hF_cont : ContinuousOn F s :=
    (hv.1.continuousOn.mul (hp.continuousOn.mul hdu_cont)).sub
      (hu.1.continuousOn.mul (hp.continuousOn.mul hdv_cont))
  have hg_cont : ContinuousOn g s :=
    (((continuousOn_const.mul hw).mul hu.1.continuousOn).mul hv.1.continuousOn)
  have hF_deriv : ∀ x ∈ Ioo a b, HasDerivAt F (g x) x := by
    intro x hx
    have hcross := hasDerivAt_sturmCross p q w u v μ ν hp hu hv hx
    have hnear : F =ᶠ[𝓝 x]
        fun t ↦ -(u t * (p t * deriv v t) - v t * (p t * deriv u t)) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
      have hdu_eq := derivWithin_of_mem_nhds (f := u) (s := s) (x := t)
        (Icc_mem_nhds_iff.mpr ht)
      have hdv_eq := derivWithin_of_mem_nhds (f := v) (s := s) (x := t)
        (Icc_mem_nhds_iff.mpr ht)
      simp only [F, du, dv]
      rw [hdu_eq, hdv_eq]
      ring
    refine (hcross.neg.congr_of_eventuallyEq hnear).congr_deriv ?_
    simp only [g]
    ring
  have hFTC := integral_eq_sub_of_hasDerivAt_of_le hab.le hF_cont hF_deriv
    (hg_cont.intervalIntegrable_of_Icc hab.le)
  have hFa0 : 0 ≤ F a := by
    have hFa : F a = v a * (p a * du a) := by simp [F, hua]
    rw [hFa]
    exact mul_nonneg (left_endpoint_nonneg hab hv.1.continuousOn hv_pos)
      (mul_nonneg (hp_pos a ⟨le_rfl, hab.le⟩).le (derivWithin_left_nonneg hab hu.1 hua hu_pos))
  have hFb0 : F b ≤ 0 := by
    have hFb : F b = v b * (p b * du b) := by simp [F, hub]
    rw [hFb]
    exact mul_nonpos_of_nonneg_of_nonpos (right_endpoint_nonneg hab hv.1.continuousOn hv_pos)
      (mul_nonpos_of_nonneg_of_nonpos (hp_pos b ⟨hab.le, le_rfl⟩).le
        (derivWithin_right_nonpos hab hu.1 hub hu_pos))
  have hgt : ∀ x ∈ Ioo a b, 0 < g x := fun x hx ↦
    mul_pos (mul_pos (mul_pos (sub_pos.mpr hμν) (hw_pos x (Ioo_subset_Icc_self hx)))
      (hu_pos x hx)) (hv_pos x hx)
  have hnn : ∀ x ∈ Ioc a b, 0 ≤ g x := by
    intro x hx
    rcases eq_or_lt_of_le hx.2 with rfl | hxb
    · simp [g, hub]
    · exact (hgt x ⟨hx.1, hxb⟩).le
  have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hpos := integral_pos hab hg_cont hnn ⟨(a + b) / 2, Ioo_subset_Icc_self hmid, hgt _ hmid⟩
  linarith [hFTC, hpos]

/-- Increasing the spectral parameter forces a zero between successive zeros of a lower mode. -/
theorem sturm_comparison {a b μ ν : ℝ} (hab : a < b) (hμν : μ < ν)
    (p q w u v : ℝ → ℝ) (hp : ContDiffOn ℝ 1 p (Set.Icc a b))
    (hw : ContinuousOn w (Set.Icc a b))
    (hp_pos : ∀ x ∈ Set.Icc a b, 0 < p x) (hw_pos : ∀ x ∈ Set.Icc a b, 0 < w x)
    (hu : IsSturmLiouvilleSolutionOn p q w μ u (Set.Icc a b))
    (hv : IsSturmLiouvilleSolutionOn p q w ν v (Set.Icc a b))
    (hua : u a = 0) (hub : u b = 0) (hno : ∀ x ∈ Set.Ioo a b, u x ≠ 0) :
    ∃ x ∈ Set.Ioo a b, v x = 0 := by
  by_contra hnone
  have hv_ne : ∀ x ∈ Ioo a b, v x ≠ 0 := fun x hx hvx ↦ hnone ⟨x, hx, hvx⟩
  have hneg {f : ℝ → ℝ} (hf : ∀ x ∈ Ioo a b, f x < 0) : ∀ x ∈ Ioo a b, 0 < -f x :=
    fun x hx ↦ neg_pos.mpr (hf x hx)
  have hua' : -u a = 0 := by simp [hua]
  have hub' : -u b = 0 := by simp [hub]
  -- Replacing `u` or `v` by its negative reduces to the case of positive solutions.
  rcases sign_const_of_ne_zero hab hu.1.continuousOn hno with hu_pos | hu_neg <;>
    rcases sign_const_of_ne_zero hab hv.1.continuousOn hv_ne with hv_pos | hv_neg
  · exact sturm_comparison_of_pos hab hμν hp hw hp_pos hw_pos hu hv hua hub hu_pos hv_pos
  · exact sturm_comparison_of_pos hab hμν hp hw hp_pos hw_pos hu hv.neg hua hub hu_pos
      (hneg hv_neg)
  · exact sturm_comparison_of_pos hab hμν hp hw hp_pos hw_pos hu.neg hv hua' hub'
      (hneg hu_neg) hv_pos
  · exact sturm_comparison_of_pos hab hμν hp hw hp_pos hw_pos hu.neg hv.neg hua' hub'
      (hneg hu_neg) (hneg hv_neg)

end CKMA
