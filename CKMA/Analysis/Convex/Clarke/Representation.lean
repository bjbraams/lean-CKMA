/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Sequences

/-!
# Line integrals of Lipschitz derivatives

A real function that is Lipschitz on a ball in a finite-dimensional space is differentiable
almost everywhere. Along almost every line the fundamental theorem recovers the increment as
the integral of the derivative, so a uniform bound on directional derivatives controls nearby
difference quotients.

In finite dimensions the canonical embedding into the double dual is surjective, and the
support function of a set is unchanged by passing to the closed convex hull.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology Set Metric MeasureTheory intervalIntegral Module
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A Lipschitz function on a ball is differentiable at almost every point of the ball. -/
private lemma ae_differentiableAt_of_lipschitzOn_ball
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]
    {f : E → ℝ} {x : E} {r : ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (ball x r)) :
    ∀ᵐ y ∂μ, y ∈ ball x r → DifferentiableAt ℝ f y := by
  filter_upwards [hf.ae_differentiableWithinAt_of_mem (μ := μ)] with y hy hyball
  exact (hy hyball).differentiableAt (isOpen_ball.mem_nhds hyball)

/-- In finite dimensions the strong dual is finite-dimensional. -/
lemma finiteDimensional_strongDual [FiniteDimensional ℝ E] :
    FiniteDimensional ℝ (StrongDual ℝ E) :=
  (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).finiteDimensional

/-- In finite dimensions the strong dual has the same dimension as the original space. -/
lemma finrank_strongDual [FiniteDimensional ℝ E] :
    finrank ℝ (StrongDual ℝ E) = finrank ℝ E := by
  rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).finrank_eq]
  exact Subspace.dual_finrank_eq (K := ℝ) (V := E)

/-- In finite dimensions every continuous linear functional on the strong dual is evaluation
at a vector. -/
lemma exists_strongDual_eq_apply [FiniteDimensional ℝ E]
    (φ : StrongDual ℝ (StrongDual ℝ E)) :
    ∃ d : E, ∀ u : StrongDual ℝ E, φ u = u d := by
  have : FiniteDimensional ℝ (StrongDual ℝ E) := finiteDimensional_strongDual
  have : FiniteDimensional ℝ (StrongDual ℝ (StrongDual ℝ E)) :=
    finiteDimensional_strongDual (E := StrongDual ℝ E)
  have hdim : finrank ℝ E = finrank ℝ (StrongDual ℝ (StrongDual ℝ E)) := by
    rw [finrank_strongDual (E := StrongDual ℝ E), finrank_strongDual]
  have hinj : Function.Injective (NormedSpace.inclusionInDoubleDual ℝ E).toLinearMap :=
    (NormedSpace.inclusionInDoubleDualLi ℝ).injective
  have hsurj :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (NormedSpace.inclusionInDoubleDual ℝ E).toLinearMap) hdim).mp hinj
  obtain ⟨d, hd⟩ := hsurj φ
  refine ⟨d, fun u => ?_⟩
  have hud : (NormedSpace.inclusionInDoubleDual ℝ E) d u = φ u :=
    DFunLike.congr_fun hd u
  rw [← hud, NormedSpace.dual_def]

/-- Closing and taking the convex hull does not change the support function of a nonempty
set of scalars that is bounded above. -/
lemma sSup_image_closure_convexHull_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : StrongDual ℝ F} {s : Set F} (hne : s.Nonempty) (hbdd : BddAbove (φ '' s)) :
    sSup (φ '' closure (convexHull ℝ s)) = sSup (φ '' s) := by
  set σ : ℝ := sSup (φ '' s)
  have hσ : ∀ z ∈ s, φ z ≤ σ := fun z hz => le_csSup hbdd (mem_image_of_mem φ hz)
  set half : Set F := {z | φ z ≤ σ}
  have hconv : Convex ℝ half := by
    intro a ha b hb p q hp hq hpq
    rw [mem_ofPred_eq] at ha hb
    rw [mem_ofPred_eq, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have hpa : p * φ a ≤ p * σ := mul_le_mul_of_nonneg_left ha hp
    have hqb : q * φ b ≤ q * σ := mul_le_mul_of_nonneg_left hb hq
    calc
      p * φ a + q * φ b ≤ p * σ + q * σ := add_le_add hpa hqb
      _ = σ := by rw [← add_mul, hpq, one_mul]
  have hclosed : IsClosed half := isClosed_Iic.preimage φ.continuous
  have hhull : convexHull ℝ s ⊆ half := convexHull_min hσ hconv
  have hcl : closure (convexHull ℝ s) ⊆ half := closure_minimal hhull hclosed
  have hbd : BddAbove (φ '' closure (convexHull ℝ s)) := by
    refine ⟨σ, ?_⟩
    intro a ha
    obtain ⟨z, hz, rfl⟩ := ha
    exact hcl hz
  have hne' : (φ '' closure (convexHull ℝ s)).Nonempty := by
    obtain ⟨z, hz⟩ := hne
    exact ⟨φ z, z, subset_closure ((subset_convexHull ℝ s) hz), rfl⟩
  have hsub : φ '' s ⊆ φ '' closure (convexHull ℝ s) :=
    image_mono ((subset_convexHull ℝ s).trans subset_closure)
  refine le_antisymm ?_ (csSup_le_csSup hbd (hne.image φ) hsub)
  exact csSup_le hne' fun a ha => by
    obtain ⟨z, hz, rfl⟩ := ha
    exact hcl hz

/-- Derivatives at differentiability points tending to `x` admit a norm-convergent subsequence.
Finite dimensionality supplies the compact ball of candidate derivatives. -/
theorem exists_tendsto_fderiv_of_lipschitzOn [FiniteDimensional ℝ E]
    {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hf : LipschitzOnWith L f (ball x r)) :
    ∃ u : StrongDual ℝ E, ∃ y : ℕ → E, Tendsto y atTop (𝓝 x) ∧
      (∀ n, DifferentiableAt ℝ f (y n)) ∧
      Tendsto (fun n ↦ fderiv ℝ f (y n)) atTop (𝓝 u) ∧ ‖u‖ ≤ (L : ℝ) := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  have _ : LocallyCompactSpace E :=
    LocallyCompactSpace.of_finiteDimensional_of_complete ℝ E
  let μ : Measure E := Measure.addHaar
  have hae : ∀ᵐ y ∂μ, y ∈ ball x r → DifferentiableAt ℝ f y :=
    ae_differentiableAt_of_lipschitzOn_ball hf
  have hdense : Dense {y | y ∈ ball x r → DifferentiableAt ℝ f y} :=
    Measure.dense_of_ae hae
  have hne : ∀ n : ℕ,
      (ball x (min (r / 2) (1 / ((n : ℝ) + 1))) ∩
        {y | y ∈ ball x r → DifferentiableAt ℝ f y}).Nonempty := by
    intro n
    have hpos : 0 < min (r / 2) (1 / ((n : ℝ) + 1)) :=
      lt_min (div_pos hr zero_lt_two) (div_pos one_pos (by linarith))
    exact hdense.inter_open_nonempty _ isOpen_ball (nonempty_ball.2 hpos)
  let y : ℕ → E := fun n => (hne n).choose
  have hy : ∀ n : ℕ, y n ∈ ball x (min (r / 2) (1 / ((n : ℝ) + 1))) ∩
      {z | z ∈ ball x r → DifferentiableAt ℝ f z} := fun n => (hne n).choose_spec
  have hdist : ∀ n : ℕ, dist (y n) x < 1 / ((n : ℝ) + 1) := by
    intro n
    exact lt_of_lt_of_le (mem_ball.mp (hy n).1) (min_le_right _ _)
  have hytend : Tendsto y atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hdist n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hball : ∀ n, y n ∈ ball x r := by
    intro n
    exact ball_subset_ball ((min_le_left _ _).trans (half_le_self hr.le)) (hy n).1
  have hdiff : ∀ n, DifferentiableAt ℝ f (y n) := fun n => (hy n).2 (hball n)
  have hfy : ∀ n, ‖fderiv ℝ f (y n)‖ ≤ (L : ℝ) := fun n =>
    norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds (hball n)) hf
  have : FiniteDimensional ℝ (StrongDual ℝ E) := finiteDimensional_strongDual
  obtain ⟨u, hu, φ, hφ, hφtend⟩ :=
    (isCompact_closedBall (0 : StrongDual ℝ E) (L : ℝ)).tendsto_subseq fun n => by
      simpa [mem_closedBall, dist_zero_right] using hfy n
  refine ⟨u, y ∘ φ, hytend.comp hφ.tendsto_atTop, fun n => hdiff (φ n), hφtend, ?_⟩
  rw [mem_closedBall, dist_zero_right] at hu
  exact hu

/-- If directional derivatives on a smaller ball are at most `α`, then nearby positive
difference quotients are at most `α`. Almost every line meets the nondifferentiability set
in a null set, and continuity removes the remaining null set of base points. -/
theorem differenceQuotient_eventually_le_of_fderiv_le [FiniteDimensional ℝ E]
    {f : E → ℝ} {x : E} {r : ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (ball x r))
    {v : E} {α ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r)
    (hgrad : ∀ y ∈ ball x ρ, DifferentiableAt ℝ f y → (fderiv ℝ f y) v ≤ α) :
    ∀ᶠ p in 𝓝[univ ×ˢ Ioi 0] (x, 0),
      (f (p.1 + p.2 • v) - f p.1) / p.2 ≤ α := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  have _ : LocallyCompactSpace E :=
    LocallyCompactSpace.of_finiteDimensional_of_complete ℝ E
  let μ : Measure E := Measure.addHaar
  have hae : ∀ᵐ y ∂μ, y ∈ ball x r → DifferentiableAt ℝ f y :=
    ae_differentiableAt_of_lipschitzOn_ball hf
  have hbad : μ {y | y ∈ ball x ρ ∧ ¬ DifferentiableAt ℝ f y} = 0 := by
    refine measure_mono_null ?_ (ae_iff.mp hae)
    intro y hy himp
    exact hy.2 (himp (ball_subset_ball hρr hy.1))
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null hbad
  have hspan (t : ℝ) : (LinearMap.toSpanSingleton ℝ E v) t = t • v := by
    rw [LinearMap.toSpanSingleton, LinearMap.smulRight_apply, LinearMap.id_apply]
  have hlines : ∀ᵐ y ∂μ, ∀ᵐ t : ℝ ∂volume, y + t • v ∉ N := by
    have hcompl : ∀ᵐ y ∂μ, y ∈ Nᶜ := measure_eq_zero_iff_ae_notMem.mp hN0
    filter_upwards [(ae_ae_add_linearMap_mem_iff (LinearMap.toSpanSingleton ℝ E v)
      (volume : Measure ℝ) μ hNm.compl).2 hcompl] with y hy
    filter_upwards [hy] with t ht
    rw [hspan, mem_compl_iff] at ht
    exact ht
  set δ : ℝ := ρ / (2 * (1 + ‖v‖))
  have h1 : 0 < 1 + ‖v‖ := by linarith [norm_nonneg v]
  have hδ : 0 < δ := div_pos hρ (mul_pos zero_lt_two h1)
  have hδmul : δ * (1 + ‖v‖) = ρ / 2 := by
    have hc : 1 + ‖v‖ ≠ 0 := h1.ne'
    simp only [δ]
    rw [div_mul_eq_mul_div]
    exact mul_div_mul_right _ _ hc
  have hδρ : δ * (1 + ‖v‖) < ρ := by
    rw [hδmul]
    linarith
  have hseg : ∀ {y : E} {s t : ℝ}, dist y x < δ → 0 ≤ s → s ≤ t → t < δ →
      y + s • v ∈ ball x ρ := by
    intro y s t hy hs hst ht
    rw [mem_ball, dist_eq_norm]
    have hyx : ‖y - x‖ < δ := by rwa [dist_eq_norm] at hy
    calc
      ‖y + s • v - x‖ = ‖(y - x) + s • v‖ := by rw [add_sub_right_comm]
      _ ≤ ‖y - x‖ + ‖s • v‖ := norm_add_le _ _
      _ = ‖y - x‖ + s * ‖v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
      _ < δ + s * ‖v‖ := by linarith
      _ ≤ δ + δ * ‖v‖ := by nlinarith [hst, ht.le, norm_nonneg v]
      _ = δ * (1 + ‖v‖) := by ring
      _ < ρ := hδρ
  have hae_quot : ∀ᵐ y ∂μ, ∀ t, 0 < t → t < δ → dist y x < δ →
      (f (y + t • v) - f y) / t ≤ α := by
    filter_upwards [hlines] with y hy
    intro t ht0 htδ hyδ
    let path : ℝ → E := fun s => y + s • v
    let g : ℝ → ℝ := f ∘ path
    have hmaps : MapsTo path (uIcc 0 t) (ball x r) := by
      intro s hs
      have hsI : s ∈ Icc 0 t := by rwa [uIcc_of_le ht0.le] at hs
      exact ball_subset_ball hρr (hseg hyδ hsI.1 hsI.2 htδ)
    have hpathL : LipschitzOnWith ‖v‖₊ path (uIcc 0 t) := by
      refine LipschitzOnWith.of_dist_le_mul fun s _ u _ => ?_
      dsimp [path]
      rw [dist_eq_norm, dist_eq_norm]
      apply le_of_eq
      calc
        ‖y + s • v - (y + u • v)‖ = ‖(s - u) • v‖ := by
          rw [add_sub_add_left_eq_sub, sub_smul]
        _ = |s - u| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ = (‖v‖₊ : ℝ) * ‖s - u‖ := by
          rw [mul_comm, ← Real.norm_eq_abs, coe_nnnorm]
    have hgac : AbsolutelyContinuousOnInterval g 0 t :=
      (hf.comp hpathL hmaps).absolutelyContinuousOnInterval
    have hderiv_le : ∀ᵐ s ∂volume, s ∈ Icc 0 t → deriv g s ≤ α := by
      filter_upwards [hy] with s hs
      intro hsI
      have hpoint : path s ∈ ball x ρ := hseg hyδ hsI.1 hsI.2 htδ
      have hdiff : DifferentiableAt ℝ f (path s) := by
        by_contra hnd
        exact hs (hNsub ⟨hpoint, hnd⟩)
      have hpair : (fderiv ℝ f (path s)) v ≤ α := hgrad _ hpoint hdiff
      have hpathd : HasDerivAt path v s := by
        dsimp [path]
        simpa [one_smul] using ((hasDerivAt_id s).smul_const v).const_add y
      have hhas : HasDerivAt g ((fderiv ℝ f (path s)) v) s := by
        dsimp [g]
        exact hdiff.hasFDerivAt.comp_hasDerivAt s hpathd
      rw [hhas.deriv]
      exact hpair
    have hint_le : ∫ s in (0 : ℝ)..t, deriv g s ≤ α * t := by
      have hintα : ∫ s in (0 : ℝ)..t, α = α * t := by
        rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm]
      rw [← hintα]
      apply integral_mono_ae_restrict ht0.le hgac.intervalIntegrable_deriv
        intervalIntegrable_const
      exact (ae_restrict_iff' measurableSet_Icc).2 hderiv_le
    have hinc : g t - g 0 ≤ α * t := by
      rw [← hgac.integral_deriv_eq_sub]
      exact hint_le
    have hquot : (g t - g 0) / t ≤ α := (div_le_iff₀ ht0).2 hinc
    dsimp [g, path] at hquot
    rw [zero_smul, add_zero] at hquot
    exact hquot
  have hall : ∀ y, dist y x < δ → ∀ t, 0 < t → t < δ →
      (f (y + t • v) - f y) / t ≤ α := by
    intro y hy t ht0 htδ
    set hfun : E → ℝ := fun z => (f (z + t • v) - f z) / t
    have hshift : ∀ z, dist z x < δ → z + t • v ∈ ball x r := by
      intro z hz
      exact ball_subset_ball hρr (hseg hz ht0.le le_rfl htδ)
    have hδlt : δ < ρ := by
      have hle : δ ≤ δ * (1 + ‖v‖) := by nlinarith [norm_nonneg v, hδ.le]
      exact hle.trans_lt hδρ
    have hbase : ∀ z, dist z x < δ → z ∈ ball x r := by
      intro z hz
      exact ball_subset_ball hρr (mem_ball.mpr (hz.trans hδlt))
    have hcont : ∀ z, dist z x < δ → ContinuousAt hfun z := by
      intro z hz
      have hcf : ContinuousAt f z :=
        hf.continuousOn.continuousAt (isOpen_ball.mem_nhds (hbase z hz))
      have hcs : ContinuousAt f (z + t • v) :=
        hf.continuousOn.continuousAt (isOpen_ball.mem_nhds (hshift z hz))
      have hadd : ContinuousAt (fun w => w + t • v) z :=
        (continuous_add_const (t • v)).continuousAt
      exact ((ContinuousAt.comp (f := fun w => w + t • v) hcs hadd).sub hcf).div_const t
    set bad : Set E := ball x δ ∩ hfun ⁻¹' Ioi α
    have hcontOn : ContinuousOn hfun (ball x δ) := by
      intro z hz
      exact (hcont z (mem_ball.mp hz)).continuousWithinAt
    have hopen : IsOpen bad :=
      hcontOn.isOpen_inter_preimage isOpen_ball isOpen_Ioi
    have hnull : μ bad = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hae_quot] with z hz
      intro hzmem
      rcases hzmem with ⟨hzball, hgt⟩
      rw [mem_preimage, mem_Ioi] at hgt
      exact (not_lt_of_ge (hz t ht0 htδ (mem_ball.mp hzball))) hgt
    have hempty : bad = ∅ := hopen.eq_empty_of_measure_zero hnull
    have hnot : ¬ α < hfun y := by
      intro hlt
      have : y ∈ bad := by
        rw [mem_inter_iff, mem_preimage, mem_Ioi, mem_ball]
        exact ⟨hy, hlt⟩
      simp [hempty] at this
    exact le_of_not_gt hnot
  rw [eventually_nhdsWithin_iff]
  have hU : ball x δ ×ˢ ball (0 : ℝ) δ ∈ 𝓝 (x, (0 : ℝ)) := by
    rw [nhds_prod_eq]
    exact prod_mem_prod (ball_mem_nhds x hδ) (ball_mem_nhds 0 hδ)
  filter_upwards [hU] with p hp hs
  obtain ⟨hpE, hpR⟩ := mem_prod.mp hp
  have ht0 : 0 < p.2 := (mem_prod.mp hs).2
  have htδ : p.2 < δ := by
    rw [mem_ball, dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_pos ht0] at hpR
    exact hpR
  have hyδ : dist p.1 x < δ := by
    rw [mem_ball] at hpE
    exact hpE
  exact hall p.1 hyδ p.2 ht0 htδ

end CKMA
