/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.ODE.PeriodicAndSturm.Floquet
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Calculus.ContDiff.Defs

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.Ring.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Floquet decompositions and Sturm zero theorems

Floquet factorization `U t = P t exp (t B)` of the normalized fundamental operator of a
`T`-periodic linear system on a finite-dimensional space, with `P` periodic of period `T` over `ℂ`
and of period `2 T` over `ℝ`. Sturm's separation and comparison theorems for real equations
`-(p u')' + q u = μ w u` with positive leading coefficient `p` on a compact interval `[a, b]`;
separation assumes a nonzero Wronskian at `a`, and comparison a positive weight `w`.
Sources: GAPS 31.17 and 31.20.

## Main definitions

* `CKMA.IsSturmLiouvilleSolutionOn`: `u` is `C²` on `I` and solves `-(p u')' + q u = μ w u` at
  the interior points of `I`.
* `CKMA.sturmWronskian`: The Wronskian `u v' - v u'`, with derivatives within a set.

## Main results

* `CKMA.floquet_complex`: Complex Floquet factorization of a periodic linear system (**31.17**).
* `CKMA.floquet_real`: Real Floquet factorization with period `2 * T`.
* `CKMA.sturm_separation`: Sturm separation theorem for independent solutions (**31.20**).
* `CKMA.sturm_comparison`: Sturm comparison theorem for solutions at ordered spectral parameters.
* `CKMA.forall_pos_or_forall_neg_of_ne_zero`, `CKMA.existsUnique_eq_zero_of_strictMonoOn`:
  sign and root lemmas for continuous real functions used in the proofs.

## Implementation notes

The equation is imposed only at interior points and the Wronskian at an endpoint uses
derivatives within the interval, so neither depends on how `u` is extended outside it.

## References

* [Coddington and Levinson, *Theory of Ordinary Differential Equations*][coddingtonlevinson1955]
-/

public section

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
  obtain ⟨L, hL⟩ :=
    exists_normedSpace_exp_eq_of_isInvertible (hU.isInvertible_of_finiteDimensional hA T)
  exact hU.floquet_of_exp_eq hA hperiod hT.ne' hL

/-- Real Floquet factorization: a `T`-periodic real linear system has a factorization
`U t = P t exp (t B)` with `P` periodic of period `2 T`. -/
theorem floquet_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (A U : ℝ → E →L[ℝ] E) {T : ℝ} (hT : 0 < T)
    (hA : Continuous A) (hperiod : Function.Periodic A T) (hU : IsFundamentalOperator A U) :
    ∃ (B : E →L[ℝ] E) (P : ℝ → E →L[ℝ] E), Function.Periodic P (2 * T) ∧
      ContDiff ℝ 1 P ∧ (∀ t, (P t).IsInvertible) ∧
      ∀ t, U t = P t * NormedSpace.exp (t • B) := by
  sorry

/-- A classical solution of `-(p u')' + q u = μ w u` on a set `I`: `u` is `C²` on `I`, and the
equation holds at every interior point of `I`. -/
@[expose]
def IsSturmLiouvilleSolutionOn (p q w : ℝ → ℝ) (μ : ℝ) (u : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ContDiffOn ℝ 2 u I ∧
    ∀ x ∈ interior I, -deriv (fun t ↦ p t * deriv u t) x + q x * u x = μ * w x * u x

/-- Unfolding `IsSturmLiouvilleSolutionOn`. -/
lemma isSturmLiouvilleSolutionOn_iff {p q w : ℝ → ℝ} {μ : ℝ} {u : ℝ → ℝ} {I : Set ℝ} :
    IsSturmLiouvilleSolutionOn p q w μ u I ↔ ContDiffOn ℝ 2 u I ∧
      ∀ x ∈ interior I, -deriv (fun t ↦ p t * deriv u t) x + q x * u x = μ * w x * u x :=
  Iff.rfl

/-- A Sturm–Liouville solution on `I` is `C²` on `I`. -/
lemma IsSturmLiouvilleSolutionOn.contDiffOn {p q w : ℝ → ℝ} {μ : ℝ} {u : ℝ → ℝ} {I : Set ℝ}
    (hu : IsSturmLiouvilleSolutionOn p q w μ u I) : ContDiffOn ℝ 2 u I :=
  hu.1

/-- A Sturm–Liouville solution on `I` satisfies the equation at each interior point of `I`. -/
lemma IsSturmLiouvilleSolutionOn.eq_of_mem_interior {p q w : ℝ → ℝ} {μ : ℝ} {u : ℝ → ℝ}
    {I : Set ℝ} (hu : IsSturmLiouvilleSolutionOn p q w μ u I) {x : ℝ} (hx : x ∈ interior I) :
    -deriv (fun t ↦ p t * deriv u t) x + q x * u x = μ * w x * u x :=
  hu.2 x hx

/-- The Wronskian `u v' - v u'` of `u` and `v` at `x`, with derivatives taken within `s`. -/
@[expose]
def sturmWronskian (u v : ℝ → ℝ) (s : Set ℝ) (x : ℝ) : ℝ :=
  u x * derivWithin v s x - v x * derivWithin u s x

/-- Unfolding `sturmWronskian`. -/
lemma sturmWronskian_def (u v : ℝ → ℝ) (s : Set ℝ) (x : ℝ) :
    sturmWronskian u v s x = u x * derivWithin v s x - v x * derivWithin u s x :=
  rfl

/-- The Wronskian within the whole line uses the ordinary derivatives. -/
lemma sturmWronskian_univ (u v : ℝ → ℝ) (x : ℝ) :
    sturmWronskian u v univ x = u x * deriv v x - v x * deriv u x := by
  simp only [sturmWronskian_def, derivWithin_univ]

/-- At a point of which `s` is a neighbourhood, the Wronskian within `s` is the ordinary one. -/
lemma sturmWronskian_of_mem_nhds {u v : ℝ → ℝ} {s : Set ℝ} {x : ℝ} (hs : s ∈ 𝓝 x) :
    sturmWronskian u v s x = sturmWronskian u v univ x := by
  simp only [sturmWronskian_def, derivWithin_univ, derivWithin_of_mem_nhds hs]

/-- Negating the second function negates the Wronskian. -/
lemma sturmWronskian_neg_right (u v : ℝ → ℝ) (s : Set ℝ) (x : ℝ) :
    sturmWronskian u (fun t ↦ -v t) s x = -sturmWronskian u v s x := by
  simp only [sturmWronskian_def, derivWithin.fun_neg]
  ring

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
  have hSL := hu.eq_of_mem_interior (by rwa [interior_Icc])
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

/-- A real function continuous and without zeros on a preconnected set has constant strict sign
there. -/
theorem forall_pos_or_forall_neg_of_ne_zero {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsPreconnected s) {u : X → ℝ} (hu : ContinuousOn u s) (hno : ∀ x ∈ s, u x ≠ 0) :
    (∀ x ∈ s, 0 < u x) ∨ (∀ x ∈ s, u x < 0) := by
  by_contra! h
  obtain ⟨⟨x, hx, hux⟩, y, hy, huy⟩ := h
  obtain ⟨z, hz, hz0⟩ := hs.intermediate_value hx hy hu ⟨hux, huy⟩
  exact hno z hz hz0

/-- A continuous function strictly increasing on `(a, b)`, tending to `-∞` at `a` and to `+∞` at
`b`, has exactly one zero in `(a, b)`. -/
theorem existsUnique_eq_zero_of_strictMonoOn {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
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
    filter_upwards [self_mem_nhdsWithin, hslope.eventually hne] with x hx _hsx
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
    filter_upwards [self_mem_nhdsWithin, hslope.eventually hne] with x hx _hsx
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
lemma IsSturmLiouvilleSolutionOn.neg {p q w u : ℝ → ℝ} {μ : ℝ} {I : Set ℝ}
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
    ∃ c, ∀ x ∈ Ioo a b, p x * sturmWronskian u v univ x = c := by
  have hHas : ∀ x ∈ Ioo a b, HasDerivAt (fun t ↦ p t * sturmWronskian u v univ t) 0 x := by
    intro x hx
    have hcross := hasDerivAt_sturmCross p q w u v μ μ hp hu hv hx
    have hfun : (fun t ↦ u t * (p t * deriv v t) - v t * (p t * deriv u t)) =
        fun t ↦ p t * sturmWronskian u v univ t := by
      funext t
      rw [sturmWronskian_univ]
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
    (hv : ContDiffOn ℝ 2 v (Icc a b)) (hc : ∀ y ∈ Ioo a b, p y * sturmWronskian u v univ y = c)
    (hx : x ∈ Icc a b) : c = p x * sturmWronskian u v (Icc a b) x := by
  have hne : (𝓝[Ioo a b] x).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo hab.ne]
    exact hx
  have hle : 𝓝[Ioo a b] x ≤ 𝓝[Icc a b] x := nhdsWithin_mono x Ioo_subset_Icc_self
  have hW : Tendsto (sturmWronskian u v univ) (𝓝[Ioo a b] x)
      (𝓝 (sturmWronskian u v (Icc a b) x)) := by
    rw [funext (sturmWronskian_univ u v), sturmWronskian_def]
    exact (((hu.continuousOn x hx).tendsto.mono_left hle).mul
      (tendsto_deriv_nhdsWithin_Ioo hab hv hx)).sub
      (((hv.continuousOn x hx).tendsto.mono_left hle).mul
        (tendsto_deriv_nhdsWithin_Ioo hab hu hx))
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_)
    (((hp x hx).tendsto.mono_left hle).mul hW)
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (hc y hy).symm

/-- The case of `sturm_separation` with a positive Wronskian at `a`: then `p W = c > 0` on
`[a, b]`, the quotient `v / u` is strictly increasing on `(a, b)` and runs from `-∞` to `+∞`. -/
private lemma existsUnique_zero_of_sturmWronskian_pos {a b μ : ℝ} (hab : a < b)
    {p q w u v : ℝ → ℝ} (hp : ContDiffOn ℝ 1 p (Icc a b)) (hp_pos : ∀ x ∈ Icc a b, 0 < p x)
    (hu : IsSturmLiouvilleSolutionOn p q w μ u (Icc a b))
    (hv : IsSturmLiouvilleSolutionOn p q w μ v (Icc a b))
    (hua : u a = 0) (hub : u b = 0) (hno : ∀ x ∈ Ioo a b, u x ≠ 0)
    (hW : 0 < sturmWronskian u v (Icc a b) a) : ∃! x, x ∈ Ioo a b ∧ v x = 0 := by
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  obtain ⟨c, hc⟩ := exists_mul_sturmWronskian_eq_const hp hu hv
  have hcW {x : ℝ} (hx : x ∈ Icc a b) :=
    const_eq_mul_sturmWronskian_of_mem_Icc hab hp.continuousOn hu.1 hv.1 hc hx
  have hc_pos : 0 < c := hcW ha ▸ mul_pos (hp_pos a ha) hW
  have hWb : 0 < sturmWronskian u v (Icc a b) b :=
    pos_of_mul_pos_right (hcW hb ▸ hc_pos) (hp_pos b hb).le
  -- At a zero `z` of `u`, the Wronskian is `-(v z * u'(z))`.
  have hend {z : ℝ} (hz : u z = 0) (h : 0 < sturmWronskian u v (Icc a b) z) :
      v z / derivWithin u (Icc a b) z < 0 := by
    rw [sturmWronskian_def, hz, zero_mul, zero_sub, neg_pos] at h
    exact div_neg_iff.mpr (mul_neg_iff.mp h)
  have hne {z : ℝ} (h : v z / derivWithin u (Icc a b) z < 0) :
      v z ≠ 0 ∧ derivWithin u (Icc a b) z ≠ 0 :=
    div_ne_zero_iff.mp h.ne
  have hsa := hend hua hW
  have hsb := hend hub hWb
  have hlim_a := tendsto_div_nhdsGT hua (hne hsa).2 (hne hsa).1
    (tendsto_slope_nhdsGT_derivWithin hab hu.1)
    ((hv.1.continuousOn.continuousWithinAt ha).tendsto.mono_left
      ((nhdsWithin_Ioo_eq_nhdsGT hab).symm.le.trans (nhdsWithin_mono a Ioo_subset_Icc_self)))
  have hlim_b := tendsto_div_nhdsLT hub (hne hsb).2 (hne hsb).1
    (tendsto_slope_nhdsLT_derivWithin hab hu.1)
    ((hv.1.continuousOn.continuousWithinAt hb).tendsto.mono_left
      ((nhdsWithin_Ioo_eq_nhdsLT hab).symm.le.trans (nhdsWithin_mono b Ioo_subset_Icc_self)))
  rw [ite_eq_right hsa.not_gt] at hlim_a
  rw [ite_eq_right hsb.not_gt] at hlim_b
  have hratio_cont : ContinuousOn (fun t ↦ v t / u t) (Ioo a b) :=
    (hv.1.continuousOn.mono Ioo_subset_Icc_self).div
      (hu.1.continuousOn.mono Ioo_subset_Icc_self) hno
  have hmono : StrictMonoOn (fun t ↦ v t / u t) (Ioo a b) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo a b) hratio_cont fun x hx ↦ ?_
    rw [isOpen_Ioo.interior_eq] at hx
    have hu' := (contDiffAt_of_Icc hu.1 hx).differentiableAt (by norm_num)
    have hv' := (contDiffAt_of_Icc hv.1 hx).differentiableAt (by norm_num)
    have hpx := hp_pos x (Ioo_subset_Icc_self hx)
    have hcx := hc x hx
    rw [sturmWronskian_univ] at hcx
    rw [deriv_fun_div hv' hu' (hno x hx)]
    refine div_pos ?_ (sq_pos_of_ne_zero (hno x hx))
    linarith [pos_of_mul_pos_right (hcx ▸ hc_pos) hpx.le]
  obtain ⟨x, ⟨hx, hx0⟩, huniq⟩ :=
    existsUnique_eq_zero_of_strictMonoOn hab hratio_cont hmono hlim_a hlim_b
  refine ⟨x, ⟨hx, (div_eq_zero_iff.mp hx0).resolve_right (hno x hx)⟩, fun y hy ↦ ?_⟩
  exact huniq y ⟨hy.1, by simp only [hy.2, zero_div]⟩

/-- **31.20**, separation: if `u` vanishes at `a` and `b` and not in between, and the Wronskian
of `u` and `v` at `a` (with derivatives within `[a, b]`) is nonzero, then `v` has exactly one
zero in `(a, b)`. -/
theorem sturm_separation {a b : ℝ} (hab : a < b) (p q w u v : ℝ → ℝ) (μ : ℝ)
    (hp : ContDiffOn ℝ 1 p (Set.Icc a b)) (hp_pos : ∀ x ∈ Set.Icc a b, 0 < p x)
    (hu : IsSturmLiouvilleSolutionOn p q w μ u (Set.Icc a b))
    (hv : IsSturmLiouvilleSolutionOn p q w μ v (Set.Icc a b))
    (hua : u a = 0) (hub : u b = 0) (hno : ∀ x ∈ Set.Ioo a b, u x ≠ 0)
    (hind : sturmWronskian u v (Set.Icc a b) a ≠ 0) : ∃! x, x ∈ Set.Ioo a b ∧ v x = 0 := by
  rcases hind.lt_or_gt with hneg | hpos
  · simpa only [neg_eq_zero] using existsUnique_zero_of_sturmWronskian_pos hab hp hp_pos hu
      hv.neg hua hub hno (by rwa [sturmWronskian_neg_right, neg_pos])
  · exact existsUnique_zero_of_sturmWronskian_pos hab hp hp_pos hu hv hua hub hno hpos

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

/-- **31.20**, comparison: if `μ < ν`, `u` solves the equation for `μ`, vanishes at `a` and `b`
and not in between, and `v` solves it for `ν`, then `v` has a zero in `(a, b)`. -/
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
  rcases forall_pos_or_forall_neg_of_ne_zero isPreconnected_Ioo
      (hu.1.continuousOn.mono Ioo_subset_Icc_self) hno with hu_pos | hu_neg <;>
    rcases forall_pos_or_forall_neg_of_ne_zero isPreconnected_Ioo
      (hv.1.continuousOn.mono Ioo_subset_Icc_self) hv_ne with hv_pos | hv_neg
  · exact sturm_comparison_of_pos hab hμν hp hw hp_pos hw_pos hu hv hua hub hu_pos hv_pos
  · exact sturm_comparison_of_pos hab hμν hp hw hp_pos hw_pos hu hv.neg hua hub hu_pos
      (hneg hv_neg)
  · exact sturm_comparison_of_pos hab hμν hp hw hp_pos hw_pos hu.neg hv hua' hub'
      (hneg hu_neg) hv_pos
  · exact sturm_comparison_of_pos hab hμν hp hw hp_pos hw_pos hu.neg hv.neg hua' hub'
      (hneg hu_neg) (hneg hv_neg)

end CKMA
