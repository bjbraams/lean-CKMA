/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.Compact

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite-dimensional norming in the bidual

Whitley's lemma, in the form used for the Eberlein–Šmulian theorem: a finite-dimensional subspace
of the bidual is normed up to the factor two by finitely many functionals from the dual unit ball.
The subspace is realized as the image of a Lipschitz linear combination on a finite product of
scalars, and the estimate is made on the quotient by the kernel, whose norm agrees with the metric
used by the sphere.
-/

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false

namespace CKMA.EberleinSmulian

open ContinuousLinearMap Filter Metric Set
open scoped BigOperators NNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Whitley's norming lemma: a finite-dimensional subspace of the bidual is normed, up to the
factor two, by a finite list in the dual unit ball. The list is read off a finite subcover of the
classes in the coefficient quotient whose image has norm one. -/
theorem exists_list_norming {ι : Type*} [Finite ι]
    (v : ι → StrongDual 𝕜 (StrongDual 𝕜 E)) :
    ∃ F : List (StrongDual 𝕜 E), (∀ f ∈ F, ‖f‖ ≤ 1) ∧
      ∀ z ∈ Submodule.span 𝕜 (range v), ‖z‖ ≠ 0 → ∃ f ∈ F, ‖z‖ ≤ 2 * ‖z f‖ := by
  haveI : Fintype ι := Fintype.ofFinite ι
  let Tlin := Fintype.linearCombination 𝕜 v
  let C : ℝ := ∑ i, ‖v i‖
  have hCnonneg : 0 ≤ C := Finset.sum_nonneg fun i _ ↦ opNorm_nonneg (v i)
  have hlip : LipschitzWith (Real.toNNReal C) Tlin := by
    refine LipschitzWith.of_dist_le' (K := C) fun c d ↦ ?_
    have hcd : dist (Tlin c) (Tlin d) = ‖Tlin c - Tlin d‖ := by
      convert dist_eq_norm (Tlin c) (Tlin d)
    have hdom : dist c d = ‖c - d‖ := dist_eq_norm _ _
    rw [hcd, hdom]
    have hsplit : (∑ i, c i • v i) - (∑ i, d i • v i) =
        ∑ i, (c i • v i - d i • v i) :=
      (Finset.sum_sub_distrib (s := Finset.univ) (f := fun i ↦ c i • v i)
        (g := fun i ↦ d i • v i)).symm
    have hsub : ∑ i, (c i • v i - d i • v i) = ∑ i, (c i - d i) • v i := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ext φ
      rw [sub_apply, smul_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul,
        smul_eq_mul, sub_mul]
    have hdiff : Tlin c - Tlin d = ∑ i, (c i - d i) • v i := by
      change (∑ i, c i • v i) - (∑ i, d i • v i) = _
      exact hsplit.trans hsub
    rw [hdiff]
    refine opNorm_le_bound (∑ i, (c i - d i) • v i) (M := C * ‖c - d‖)
      (mul_nonneg hCnonneg (norm_nonneg _)) ?_
    intro φ
    have happ : (∑ i, (c i - d i) • v i) φ = ∑ i, (c i - d i) * (v i) φ := by
      simp only [sum_apply, smul_apply, smul_eq_mul]
    rw [happ]
    calc
      ‖∑ i, (c i - d i) * (v i) φ‖ ≤ ∑ i, ‖(c i - d i) * (v i) φ‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖c i - d i‖ * ‖(v i) φ‖ := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [norm_mul]
      _ ≤ ∑ i, ‖c i - d i‖ * (‖v i‖ * ‖φ‖) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        exact mul_le_mul_of_nonneg_left (le_opNorm (v i) φ) (norm_nonneg _)
      _ = (∑ i, ‖c i - d i‖ * ‖v i‖) * ‖φ‖ := by
        simp_rw [← mul_assoc]
        rw [← Finset.sum_mul]
      _ ≤ (C * ‖c - d‖) * ‖φ‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        calc
          ∑ i, ‖c i - d i‖ * ‖v i‖ ≤ ∑ i, ‖c - d‖ * ‖v i‖ := by
            refine Finset.sum_le_sum fun i _ ↦
              mul_le_mul_of_nonneg_right (norm_le_pi_norm (c - d) i) (opNorm_nonneg _)
          _ = ‖c - d‖ * C := by rw [← Finset.mul_sum]
          _ = C * ‖c - d‖ := mul_comm _ _
  have hTlin_le (c : ι → 𝕜) : ‖Tlin c‖ ≤ C * ‖c‖ := by
    refine opNorm_le_bound (Tlin c) (M := C * ‖c‖)
      (mul_nonneg hCnonneg (norm_nonneg _)) ?_
    intro φ
    have happ : Tlin c φ = ∑ i, c i * (v i) φ := by
      change (∑ i, c i • v i) φ = _
      simp only [sum_apply, smul_apply, smul_eq_mul]
    rw [happ]
    calc
      ‖∑ i, c i * (v i) φ‖ ≤ ∑ i, ‖c i * (v i) φ‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖c i‖ * ‖(v i) φ‖ := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [norm_mul]
      _ ≤ ∑ i, ‖c i‖ * (‖v i‖ * ‖φ‖) := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        exact mul_le_mul_of_nonneg_left (le_opNorm (v i) φ) (norm_nonneg _)
      _ = (∑ i, ‖c i‖ * ‖v i‖) * ‖φ‖ := by
        simp_rw [← mul_assoc]
        rw [← Finset.sum_mul]
      _ ≤ (C * ‖c‖) * ‖φ‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        calc
          ∑ i, ‖c i‖ * ‖v i‖ ≤ ∑ i, ‖c‖ * ‖v i‖ := by
            refine Finset.sum_le_sum fun i _ ↦
              mul_le_mul_of_nonneg_right (norm_le_pi_norm c i) (opNorm_nonneg _)
          _ = ‖c‖ * C := by rw [← Finset.mul_sum]
          _ = C * ‖c‖ := mul_comm _ _
  let T : (ι → 𝕜) →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
    { toLinearMap := Tlin
      cont := by exact hlip.continuous }
  have hrange : LinearMap.range Tlin = Submodule.span 𝕜 (range v) :=
    Fintype.range_linearCombination _ _
  let K : Submodule 𝕜 (ι → 𝕜) := LinearMap.ker Tlin
  haveI : IsClosed (K : Set (ι → 𝕜)) := by simpa [K] using T.isClosed_ker
  let Q := (ι → 𝕜) ⧸ K
  haveI : FiniteDimensional 𝕜 Q := inferInstance
  haveI : ProperSpace Q := FiniteDimensional.proper_rclike 𝕜 Q
  let Tbar : Q → StrongDual 𝕜 (StrongDual 𝕜 E) :=
    Quotient.lift (s := K.quotientRel) (fun c ↦ Tlin c) fun a b hab ↦ by
      have hsub : a - b ∈ K := (K.quotientRel_def).mp hab
      have hker : Tlin (a - b) = 0 := by
        simpa [K, LinearMap.mem_ker] using hsub
      simpa [map_sub, sub_eq_zero] using hker
  have hTbar (c : ι → 𝕜) : Tbar (Submodule.Quotient.mk c) = Tlin c := by
    simp [Tbar, Submodule.Quotient.mk]
  have hadd (q p : Q) : Tbar (q + p) = Tbar q + Tbar p := by
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective K q
    obtain ⟨d, rfl⟩ := Submodule.Quotient.mk_surjective K p
    rw [← Submodule.Quotient.mk_add, hTbar, hTbar, hTbar, map_add]
  have hsmul (a : 𝕜) (q : Q) : Tbar (a • q) = a • Tbar q := by
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective K q
    rw [← Submodule.Quotient.mk_smul, hTbar, hTbar, map_smul]
  have hneg (q : Q) : Tbar (-q) = -Tbar q := by
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective K q
    rw [← Submodule.Quotient.mk_neg, hTbar, hTbar, map_neg]
  have hsub (q p : Q) : Tbar (q - p) = Tbar q - Tbar p := by
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective K q
    obtain ⟨d, rfl⟩ := Submodule.Quotient.mk_surjective K p
    rw [← Submodule.Quotient.mk_sub, hTbar, map_sub, hTbar, hTbar]
  have hT0 : Tbar 0 = 0 := by
    rw [← Submodule.Quotient.mk_zero K, hTbar, map_zero]
  have hinj : Function.Injective Tbar := by
    intro q p hqp
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective K q
    obtain ⟨d, rfl⟩ := Submodule.Quotient.mk_surjective K p
    rw [Submodule.Quotient.eq]
    have hcd : Tlin c = Tlin d := by simpa [hTbar] using hqp
    have hzero : Tlin (c - d) = 0 := by rw [map_sub, hcd, sub_self]
    simpa [K, LinearMap.mem_ker] using hzero
  have hnorm_smul (c : 𝕜) (f : StrongDual 𝕜 (StrongDual 𝕜 E)) :
      ‖c • f‖ = ‖c‖ * ‖f‖ := by
    refine le_antisymm (opNorm_smul_le c f) ?_
    rcases eq_or_ne c 0 with rfl | hc
    · rw [norm_zero, zero_mul]
      exact opNorm_nonneg _
    · have hf : f = c⁻¹ • c • f := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      have hle : ‖f‖ ≤ ‖c⁻¹‖ * ‖c • f‖ := by
        calc
          ‖f‖ = ‖c⁻¹ • c • f‖ := congrArg norm hf
          _ ≤ ‖c⁻¹‖ * ‖c • f‖ := opNorm_smul_le _ _
      rw [norm_inv] at hle
      have hc0 : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
      calc
        ‖c‖ * ‖f‖ ≤ ‖c‖ * (‖c‖⁻¹ * ‖c • f‖) :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg c)
        _ = ‖c • f‖ := by rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  have hTbar_le (q : Q) : ‖Tbar q‖ ≤ C * ‖q‖ := by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    by_cases hC : C = 0
    · obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective K q
      have hzero : Tlin c = 0 := by
        have hle := hTlin_le c
        rw [hC, zero_mul] at hle
        exact (opNorm_zero_iff (f := Tlin c)).mp
          (le_antisymm hle (opNorm_nonneg _))
      rw [hTbar, hzero, opNorm_zero]
      positivity
    · have hCpos : 0 < C := lt_of_le_of_ne hCnonneg (Ne.symm hC)
      obtain ⟨c, hc, hlt⟩ :=
        Submodule.Quotient.norm_mk_lt q (div_pos hε hCpos)
      calc
        ‖Tbar q‖ = ‖Tlin c‖ := by rw [← hc, hTbar]
        _ ≤ C * ‖c‖ := hTlin_le c
        _ ≤ C * (‖q‖ + ε / C) := mul_le_mul_of_nonneg_left hlt.le hCnonneg
        _ = C * ‖q‖ + ε := by rw [mul_add, mul_div_cancel₀ _ hCpos.ne']
  have habs (a b : StrongDual 𝕜 (StrongDual 𝕜 E)) : |‖a‖ - ‖b‖| ≤ ‖a - b‖ := by
    rw [abs_sub_le_iff]
    constructor
    · have hle : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
        simpa [sub_add_cancel] using opNorm_add_le (a - b) b
      linarith
    · have hle : ‖b‖ ≤ ‖a - b‖ + ‖a‖ := by
        have hba : ‖b‖ ≤ ‖b - a‖ + ‖a‖ := by
          simpa [sub_add_cancel] using opNorm_add_le (b - a) a
        rw [← neg_sub a b, opNorm_neg] at hba
        exact hba
      linarith
  have hcont : Continuous (fun q : Q ↦ ‖Tbar q‖) := by
    refine (LipschitzWith.of_dist_le' (K := C) fun q p ↦ ?_).continuous
    rw [dist_eq_norm, Real.norm_eq_abs, dist_eq_norm]
    exact (habs (Tbar q) (Tbar p)).trans (by
      rw [← hsub q p]
      exact hTbar_le (q - p))
  let sphereSpan : Set Q := {q | ‖Tbar q‖ = 1}
  by_cases hempty : sphereSpan.Nonempty
  · obtain ⟨q1, hq1⟩ := hempty
    have hCpos : 0 < C := by
      refine lt_of_le_of_ne hCnonneg ?_
      intro hC
      have hzero : Tbar q1 = 0 := by
        obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective K q1
        have hle := hTlin_le c
        rw [← hC, zero_mul] at hle
        rw [hTbar]
        exact (opNorm_zero_iff (f := Tlin c)).mp
          (le_antisymm hle (opNorm_nonneg _))
      have hq1eq : ‖Tbar q1‖ = 1 := by simpa [sphereSpan] using hq1
      rw [hzero, opNorm_zero] at hq1eq
      norm_num at hq1eq
    have hq1eq : ‖Tbar q1‖ = 1 := by simpa [sphereSpan] using hq1
    have hq1ne : q1 ≠ 0 := by
      intro hq
      rw [hq, hT0, opNorm_zero] at hq1eq
      norm_num at hq1eq
    have hSne : (sphere (0 : Q) 1).Nonempty :=
      ⟨(‖q1‖ : 𝕜)⁻¹ • q1, by
        rw [mem_sphere_iff_norm, sub_zero]
        exact norm_smul_inv_norm hq1ne⟩
    obtain ⟨q0, hq0, hmin⟩ :=
      (isCompact_sphere (0 : Q) 1).exists_isMinOn hSne hcont.continuousOn
    let m : ℝ := ‖Tbar q0‖
    have hmpos : 0 < m := by
      have hq0ne : q0 ≠ 0 := by
        intro hq
        rw [mem_sphere_iff_norm, sub_zero, hq, norm_zero] at hq0
        norm_num at hq0
      have hne : Tbar q0 ≠ 0 := fun h ↦ hq0ne (hinj (h.trans hT0.symm))
      have hnz : m ≠ 0 := (opNorm_zero_iff (f := Tbar q0)).not.mpr hne
      exact lt_of_le_of_ne (opNorm_nonneg _) (Ne.symm hnz)
    have hbelow (q : Q) : m * ‖q‖ ≤ ‖Tbar q‖ := by
      rcases eq_or_ne q 0 with rfl | hq
      · rw [norm_zero, mul_zero, hT0, opNorm_zero]
      · have hpos : 0 < ‖q‖ := norm_pos_iff.mpr hq
        let u : Q := (‖q‖ : 𝕜)⁻¹ • q
        have hu : u ∈ sphere (0 : Q) 1 := by
          rw [mem_sphere_iff_norm, sub_zero]
          exact norm_smul_inv_norm hq
        have hmu : m ≤ ‖Tbar u‖ := hmin hu
        have hmu' : m ≤ ‖(‖q‖ : 𝕜)⁻¹ • Tbar q‖ := by
          simpa [u, hsmul] using hmu
        rw [hnorm_smul, norm_inv, RCLike.norm_ofReal,
          abs_of_nonneg (norm_nonneg q)] at hmu'
        have hmul : ‖q‖ * m ≤ ‖q‖ * (‖q‖⁻¹ * ‖Tbar q‖) :=
          mul_le_mul_of_nonneg_left hmu' hpos.le
        have hcancel : ‖q‖ * (‖q‖⁻¹ * ‖Tbar q‖) = ‖Tbar q‖ := by
          rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
        rw [mul_comm]
        exact hmul.trans_eq hcancel
    let rad : ℝ := (1 / 4) / C
    have hradpos : 0 < rad := by positivity
    have hradmul : C * rad = 1 / 4 := by simp [rad, mul_div_cancel₀ _ hCpos.ne']
    have hcov : sphereSpan ⊆ ⋃ q : ↥sphereSpan, ball (q : Q) rad := by
      intro q hq
      exact mem_iUnion.2 ⟨⟨q, hq⟩, mem_ball_self hradpos⟩
    have hclosed : IsClosed sphereSpan := isClosed_eq hcont continuous_const
    have hsubball : sphereSpan ⊆ closedBall (0 : Q) (1 / m) := by
      intro q hq
      rw [mem_closedBall_iff_norm, sub_zero]
      have hmq : m * ‖q‖ ≤ 1 := by
        have hqeq : ‖Tbar q‖ = 1 := by simpa [sphereSpan] using hq
        simpa [hqeq] using hbelow q
      rwa [le_div_iff₀ hmpos, mul_comm]
    have hcompact : IsCompact sphereSpan :=
      (isCompact_closedBall (0 : Q) (1 / m)).of_isClosed_subset hclosed hsubball
    obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover
      (fun q : ↥sphereSpan ↦ ball (q : Q) rad) (fun _ ↦ isOpen_ball) hcov
    have vec (i : ↥sphereSpan) : ∃ x : StrongDual 𝕜 E, ‖x‖ ≤ 1 ∧
        (3 / 4 : ℝ) < ‖Tbar (i : Q) x‖ := by
      have hr : (3 / 4 : ℝ) < ‖Tbar (i : Q)‖ := by
        have h1 : ‖Tbar (i : Q)‖ = 1 := i.2
        rw [h1]
        norm_num
      obtain ⟨x, hx, hxz⟩ := exists_lt_apply_of_lt_opNorm (Tbar (i : Q)) hr
      exact ⟨x, hx.le, hxz⟩
    refine ⟨t.toList.map fun i ↦ Classical.choose (vec i), ?_, ?_⟩
    · intro f hf
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hf
      exact (Classical.choose_spec (vec i)).1
    · intro w hw hwnz
      have hr0 : 0 < ‖w‖ := lt_of_le_of_ne (opNorm_nonneg w) (Ne.symm hwnz)
      let z : StrongDual 𝕜 (StrongDual 𝕜 E) := (‖w‖ : 𝕜)⁻¹ • w
      have hzmem : z ∈ Submodule.span 𝕜 (range v) := Submodule.smul_mem _ _ hw
      have hznorm : ‖z‖ = 1 := by
        rw [hnorm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg w),
          inv_mul_cancel₀ hr0.ne']
      have hzrange : z ∈ LinearMap.range Tlin := by rwa [hrange]
      obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hzrange
      let q : Q := Submodule.Quotient.mk c
      have hqz : Tbar q = z := by simpa [q, hTbar] using hc
      have hqS : q ∈ sphereSpan := by simpa [sphereSpan, hqz] using hznorm
      obtain ⟨i, hi, hball⟩ := mem_iUnion₂.mp (ht hqS)
      have hdist : ‖q - (i : Q)‖ < rad := by
        rw [mem_ball_iff_norm] at hball
        exact hball
      let x : StrongDual 𝕜 E := Classical.choose (vec i)
      have hx := Classical.choose_spec (vec i)
      have hxmem : x ∈ t.toList.map fun j ↦ Classical.choose (vec j) :=
        List.mem_map.mpr ⟨i, Finset.mem_toList.mpr hi, rfl⟩
      let zi : StrongDual 𝕜 (StrongDual 𝕜 E) := Tbar (i : Q)
      have hzi : ‖z - zi‖ < 1 / 4 := by
        have hdiff : z - zi = Tbar (q - (i : Q)) := by
          rw [← hqz]
          exact (hsub q (i : Q)).symm
        rw [hdiff]
        calc
          ‖Tbar (q - (i : Q))‖ ≤ C * ‖q - (i : Q)‖ := hTbar_le _
          _ < C * rad := mul_lt_mul_of_pos_left hdist hCpos
          _ = 1 / 4 := hradmul
      have hhalf : (1 / 2 : ℝ) < ‖z x‖ := by
        have hix : (3 / 4 : ℝ) < ‖zi x‖ := hx.2
        have hdu : ‖(zi - z) x‖ < 1 / 4 := by
          have happ : (zi - z) x = -((z - zi) x) := by
            rw [sub_apply, sub_apply, neg_sub]
          calc
            ‖(zi - z) x‖ = ‖(z - zi) x‖ := by rw [happ, norm_neg]
            _ ≤ ‖z - zi‖ * ‖x‖ := le_opNorm (z - zi) x
            _ ≤ ‖z - zi‖ * 1 :=
              mul_le_mul_of_nonneg_left hx.1 (opNorm_nonneg _)
            _ = ‖z - zi‖ := mul_one _
            _ < 1 / 4 := hzi
        have hadd : ‖zi x‖ ≤ ‖z x‖ + ‖(zi - z) x‖ := by
          have h := norm_add_le (z x) ((zi - z) x)
          have hsum : z x + (zi - z) x = zi x := by
            rw [sub_apply, add_sub_cancel]
          simpa [hsum] using h
        linarith
      have hone : 1 ≤ 2 * ‖z x‖ := by linarith
      have hscale : ‖z x‖ = ‖w‖⁻¹ * ‖w x‖ := by
        have hzapply : z x = (‖w‖ : 𝕜)⁻¹ * w x := by
          rw [show z = (‖w‖ : 𝕜)⁻¹ • w from rfl, smul_apply, smul_eq_mul]
        rw [hzapply, norm_mul, norm_inv, RCLike.norm_ofReal,
          abs_of_nonneg (norm_nonneg w)]
      have hrle : ‖w‖ ≤ 2 * ‖w x‖ := by
        have h1 : 1 ≤ 2 * (‖w‖⁻¹ * ‖w x‖) := by rw [← hscale]; exact hone
        calc
          ‖w‖ = ‖w‖ * 1 := (mul_one _).symm
          _ ≤ ‖w‖ * (2 * (‖w‖⁻¹ * ‖w x‖)) :=
            mul_le_mul_of_nonneg_left h1 hr0.le
          _ = 2 * ‖w x‖ := by
            have hinner : ‖w‖ * (‖w‖⁻¹ * ‖w x‖) = ‖w x‖ := by
              rw [← mul_assoc, mul_inv_cancel₀ hr0.ne', one_mul]
            rw [mul_left_comm, hinner]
      exact ⟨x, hxmem, hrle⟩
  · refine ⟨[], by simp, ?_⟩
    intro w hw hwnz
    have hr0 : 0 < ‖w‖ := lt_of_le_of_ne (opNorm_nonneg w) (Ne.symm hwnz)
    let z : StrongDual 𝕜 (StrongDual 𝕜 E) := (‖w‖ : 𝕜)⁻¹ • w
    have hzmem : z ∈ Submodule.span 𝕜 (range v) := Submodule.smul_mem _ _ hw
    have hznorm : ‖z‖ = 1 := by
      rw [hnorm_smul, norm_inv, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg w),
        inv_mul_cancel₀ hr0.ne']
    have hzrange : z ∈ LinearMap.range Tlin := by rwa [hrange]
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hzrange
    let q : Q := Submodule.Quotient.mk c
    have hqz : Tbar q = z := by simpa [q, hTbar] using hc
    have hqS : q ∈ sphereSpan := by simpa [sphereSpan, hqz] using hznorm
    exact False.elim (hempty ⟨q, hqS⟩)
