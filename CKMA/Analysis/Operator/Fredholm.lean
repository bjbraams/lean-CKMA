/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Fredholm.CompactPerturbation

import Mathlib.Topology.Algebra.Module.Equiv.Submodule
import Mathlib.Analysis.CStarAlgebra.Classes
import TauCeti.Analysis.Fredholm.Adjoint
import TauCeti.Analysis.Normed.Operator.Compact.Finite.Rank
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Atkinson's theorem and the Fredholm essential spectrum

For real or complex Banach spaces, a Fredholm operator has a bounded inverse modulo compact
remainders, and conversely; this is TauCeti's Atkinson theorem in
`TauCeti.Analysis.Fredholm.CompactPerturbation`.

For endomorphisms the Fredholm essential spectrum is invariant under compact perturbations.
For self-adjoint Hilbert-space operators, its spectral complement is the set of isolated
finite-multiplicity eigenvalues. The identification uses the closed-range adjoint theorem in
`TauCeti.Analysis.Fredholm.Adjoint` and Mathlib's continuous functional calculus.
Sources: GAPS 21.11 and 21.16.

## Main definitions

* `CKMA.essentialSpectrum`: the Fredholm essential spectrum of a bounded endomorphism.
* `CKMA.IsIsolatedIn`: isolated point of a subset of a topological space.

## Main results

* Atkinson's characterization of Fredholm operators (**21.11**) is TauCeti's
  `TauCeti.isFredholm_iff_exists_isCompactOperator_comp_sub_one`, over any complete nontrivially
  normed field.
* `CKMA.essentialSpectrum_add_compact`: stability of the Fredholm essential spectrum under
  compact perturbations.
* `CKMA.mem_spectrum_sdiff_essentialSpectrum_iff`: discrete spectrum of a self-adjoint operator.
-/

public section

noncomputable section

namespace CKMA

open ContinuousLinearMap Filter Topology

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- The Fredholm essential spectrum. Other notions of essential spectrum need not agree
for non-self-adjoint operators. -/
@[expose]
def essentialSpectrum (T : E →L[𝕜] E) : Set 𝕜 :=
  {z | ¬ IsFredholm (T - z • (1 : E →L[𝕜] E))}

omit [CompleteSpace E] in
/-- Membership in the Fredholm essential spectrum. -/
theorem mem_essentialSpectrum_iff (T : E →L[𝕜] E) (z : 𝕜) :
    z ∈ essentialSpectrum T ↔ ¬ IsFredholm (T - z • (1 : E →L[𝕜] E)) :=
  Iff.rfl

omit [CompleteSpace E] in
/-- A point lies outside the Fredholm essential spectrum iff `T - z • 1` is Fredholm. -/
theorem notMem_essentialSpectrum_iff (T : E →L[𝕜] E) (z : 𝕜) :
    z ∉ essentialSpectrum T ↔ IsFredholm (T - z • (1 : E →L[𝕜] E)) :=
  not_not

/-- Compact perturbations preserve the Fredholm essential spectrum, without self-adjointness. -/
theorem essentialSpectrum_add_compact (T K : E →L[𝕜] E) (hK : IsCompactOperator K) :
    essentialSpectrum (T + K) = essentialSpectrum T := by
  ext z
  have hf : IsFredholm (T + K - z • (1 : E →L[𝕜] E)) ↔
      IsFredholm (T - z • (1 : E →L[𝕜] E)) := by
    constructor
    · intro h
      have h' := h.add_of_isCompactOperator (show IsCompactOperator (-K) from by
        simpa only [FunLike.coe_neg] using hK.neg)
      convert h' using 1
      abel
    · intro h
      have h' := h.add_of_isCompactOperator hK
      convert h' using 1
      abel
  exact not_congr hf

/-- An isolated point of a subset of a topological space. -/
@[expose]
def IsIsolatedIn {X : Type*} [TopologicalSpace X] (x : X) (s : Set X) : Prop :=
  x ∈ s ∧ ∀ᶠ y in 𝓝 x, y ∈ s → y = x

/-- The defining property of an isolated point. -/
theorem isIsolatedIn_iff {X : Type*} [TopologicalSpace X] (x : X) (s : Set X) :
    IsIsolatedIn x s ↔ x ∈ s ∧ ∀ᶠ y in 𝓝 x, y ∈ s → y = x :=
  Iff.rfl

/-- The indicator of an isolated point is continuous along the ambient set. -/
private lemma continuousOn_indicator_isolated {z : ℂ} {s : Set ℂ} (h : IsIsolatedIn z s) :
    ContinuousOn (fun w : ℂ => if w = z then (1 : ℂ) else 0) s := by
  intro x _hx
  rw [Metric.continuousWithinAt_iff]
  intro eps heps
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp h.2
  by_cases hxz : x = z
  · refine ⟨δ, hδ, fun y hy hyd => ?_⟩
    rw [hxz] at hyd
    have hyz : y = z := hball hyd hy
    simp only [hxz, hyz, ↓reduceIte, dist_self]
    exact heps
  · refine ⟨dist x z, dist_pos.mpr hxz, fun y hy hyd => ?_⟩
    have hyz : y ≠ z := by
      intro hyeq
      rw [hyeq, dist_comm] at hyd
      exact lt_irrefl _ hyd
    rw [ite_eq_right hxz, ite_eq_right hyz, dist_self]
    exact heps

/-- Off an isolated point the reciprocal `w ↦ (w - z)⁻¹`, with value `0` at the point, is
continuous along the ambient set. -/
private lemma continuousOn_resolvent_isolated {z : ℂ} {s : Set ℂ} (h : IsIsolatedIn z s) :
    ContinuousOn (fun w : ℂ => if w = z then 0 else (w - z)⁻¹) s := by
  intro x _hx
  rw [Metric.continuousWithinAt_iff]
  intro eps heps
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp h.2
  by_cases hxz : x = z
  · refine ⟨δ, hδ, fun y hy hyd => ?_⟩
    rw [hxz] at hyd
    have hyz : y = z := hball hyd hy
    simp only [hxz, hyz, ↓reduceIte, dist_self]
    exact heps
  · have hinv : ContinuousAt (fun w : ℂ => (w - z)⁻¹) x :=
      (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hxz)
    rw [Metric.continuousAt_iff] at hinv
    obtain ⟨δ', hδ', hnear⟩ := hinv eps heps
    refine ⟨min δ' (dist x z), lt_min hδ' (dist_pos.mpr hxz), fun y hy hyd => ?_⟩
    have hydδ : dist y x < δ' := lt_of_lt_of_le hyd (min_le_left _ _)
    have hyz : y ≠ z := by
      intro hyeq
      rw [hyeq, dist_comm] at hyd
      exact lt_irrefl _ (lt_of_lt_of_le hyd (min_le_right _ _))
    rw [ite_eq_right hyz, ite_eq_right hxz]
    exact hnear hydδ

/-- An endomorphism preserving a complete subspace and its orthogonal complement is invertible
when both restrictions are invertible. -/
private lemma isUnit_of_isUnit_restrict_orthogonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : H →L[ℂ] H) (K : Submodule ℂ H) [CompleteSpace K]
    (hK : ∀ x : H, x ∈ K → S x ∈ K) (hKo : ∀ x : H, x ∈ Kᗮ → S x ∈ Kᗮ)
    (h1 : IsUnit (S.restrict hK)) (h2 : IsUnit (S.restrict hKo)) : IsUnit S := by
  rw [ContinuousLinearMap.isUnit_iff_bijective (f := S)]
  have hbij1 : Function.Bijective (S.restrict hK) :=
    (ContinuousLinearMap.isUnit_iff_bijective (f := S.restrict hK)).mp h1
  have hbij2 : Function.Bijective (S.restrict hKo) :=
    (ContinuousLinearMap.isUnit_iff_bijective (f := S.restrict hKo)).mp h2
  constructor
  · intro x y hSxy
    have hdiff : S (x - y) = 0 := by rw [map_sub, hSxy, sub_self]
    let u := K.starProjection (x - y)
    let v := Kᗮ.starProjection (x - y)
    have hsum : u + v = x - y := K.starProjection_add_starProjection_orthogonal (x - y)
    have hSu_mem : S u ∈ K := hK u (K.starProjection_apply_mem _)
    have hSv_mem : S v ∈ Kᗮ := hKo v (Kᗮ.starProjection_apply_mem _)
    have hsumS : S u + S v = 0 := by rw [← map_add, hsum, hdiff]
    have hSv_eq : S v = -S u := by
      have : S u + S v = S u + -S u := by rw [hsumS, add_neg_cancel]
      exact add_left_cancel this
    have hSv0 : S v = 0 := by
      have hboth : S v ∈ K ⊓ Kᗮ := ⟨by rw [hSv_eq]; exact K.neg_mem hSu_mem, hSv_mem⟩
      rw [K.inf_orthogonal_eq_bot] at hboth
      simpa using hboth
    have hSu0 : S u = 0 := by
      rw [hSv0, add_zero] at hsumS
      exact hsumS
    have hu : u = 0 := by
      have hsub : (⟨u, K.starProjection_apply_mem (x - y)⟩ : K) = 0 := by
        apply hbij1.1
        rw [map_zero]
        apply Subtype.ext
        simp only [coe_restrict_apply, hSu0, ZeroMemClass.coe_zero]
      exact congrArg Subtype.val hsub
    have hv : v = 0 := by
      have hsub : (⟨v, Kᗮ.starProjection_apply_mem (x - y)⟩ : Kᗮ) = 0 := by
        apply hbij2.1
        rw [map_zero]
        apply Subtype.ext
        simp only [coe_restrict_apply, hSv0, ZeroMemClass.coe_zero]
      exact congrArg Subtype.val hsub
    have : x - y = 0 := by rw [← hsum, hu, hv, zero_add]
    exact sub_eq_zero.mp this
  · intro y
    let a := K.starProjection y
    let b := Kᗮ.starProjection y
    obtain ⟨x1, hx1⟩ := hbij1.2 ⟨a, K.starProjection_apply_mem y⟩
    obtain ⟨x2, hx2⟩ := hbij2.2 ⟨b, Kᗮ.starProjection_apply_mem y⟩
    refine ⟨(x1 : H) + x2, ?_⟩
    rw [map_add]
    have hSx1 : S (x1 : H) = a := by
      simpa only [coe_restrict_apply] using congrArg Subtype.val hx1
    have hSx2 : S (x2 : H) = b := by
      simpa only [coe_restrict_apply] using congrArg Subtype.val hx2
    rw [hSx1, hSx2, K.starProjection_add_starProjection_orthogonal]

/-- If `w` lies in the spectrum of `a`, then `a - w • 1` is not invertible. -/
theorem not_isUnit_sub_smul_one_of_mem_spectrum {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] {a : A} {w : R} (hw : w ∈ spectrum R a) : ¬ IsUnit (a - w • (1 : A)) := by
  intro hunit
  apply spectrum.mem_iff.mp hw
  rw [Algebra.algebraMap_eq_smul_one, ← neg_sub]
  exact hunit.neg

/-- For a self-adjoint `T` and a point `z` of its spectrum, `T - z • 1` is self-adjoint. -/
private lemma isSelfAdjoint_sub_smul_one_of_mem_spectrum {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) {z : ℂ}
    (hz : z ∈ spectrum ℂ T) : IsSelfAdjoint (T - z • (1 : H →L[ℂ] H)) :=
  hT.sub ((RCLike.im_eq_zero_iff_isSelfAdjoint.mp (hT.im_eq_zero_of_mem_spectrum hz)).smul
    (IsSelfAdjoint.one (H →L[ℂ] H)))

/-- The range of a self-adjoint Fredholm operator is the orthogonal complement of its kernel. -/
private lemma range_eq_orthogonal_ker_of_isFredholm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {S : H →L[ℂ] H} (hS : IsSelfAdjoint S)
    (hfred : IsFredholm S) :
    LinearMap.range (S : H →ₗ[ℂ] H) = (LinearMap.ker (S : H →ₗ[ℂ] H))ᗮ := by
  have h := S.range_adjoint_eq_orthogonal_ker_of_isClosed_range hfred.isClosed_range
  rwa [hS.adjoint_eq] at h

/-- If `S` vanishes on `K`, then `S - c • 1` acts on `K` as multiplication by `-c`, which is
invertible for `c ≠ 0`. -/
private lemma isUnit_restrict_sub_smul_of_forall_eq_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (S : H →L[ℂ] H) (K : Submodule ℂ H) (hS : ∀ x ∈ K, S x = 0)
    {c : ℂ} (hc : c ≠ 0) (hRK : ∀ x : H, x ∈ K → (S - c • (1 : H →L[ℂ] H)) x ∈ K) :
    IsUnit ((S - c • (1 : H →L[ℂ] H)).restrict hRK) := by
  have heq : (S - c • (1 : H →L[ℂ] H)).restrict hRK = algebraMap ℂ (K →L[ℂ] K) (-c) := by
    ext x
    rw [coe_restrict_apply, sub_apply, smul_apply, one_apply_eq_self, hS x x.2,
      zero_sub, ← neg_smul, Algebra.algebraMap_eq_smul_one, ← Submodule.coe_smul]
    exact congrArg Subtype.val <| by rw [smul_apply, one_apply_eq_self]
  rw [heq]
  exact (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hc)).map (algebraMap ℂ (K →L[ℂ] K))

/-- A self-adjoint Fredholm operator `S` has `S - c • 1` invertible for all small nonzero `c`:
it acts as `-c` on the finite-dimensional kernel, and on the orthogonal complement of the
kernel it is a small perturbation of the isomorphism onto the range. -/
private lemma exists_isUnit_sub_smul_of_isFredholm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {S : H →L[ℂ] H} (hS : IsSelfAdjoint S)
    (hfred : IsFredholm S) :
    ∃ eps > 0, ∀ c : ℂ, c ≠ 0 → ‖c‖ < eps → IsUnit (S - c • (1 : H →L[ℂ] H)) := by
  let K : Submodule ℂ H := LinearMap.ker (S : H →ₗ[ℂ] H)
  have : FiniteDimensional ℂ K := hfred.finite_ker
  have : CompleteSpace K := FiniteDimensional.completeSpace ℂ K
  have hclosed : IsClosed (LinearMap.range (S : H →ₗ[ℂ] H) : Set H) := hfred.isClosed_range
  have hrange : LinearMap.range (S : H →ₗ[ℂ] H) = Kᗮ :=
    range_eq_orthogonal_ker_of_isFredholm hS hfred
  have hK0 : ∀ x ∈ K, S x = 0 := fun x hx => by
    simpa only [ContinuousLinearMap.coe_coe] using (LinearMap.mem_ker).mp hx
  have hKmem : ∀ x : H, x ∈ K → S x ∈ K := fun x hx => by
    rw [hK0 x hx]
    exact K.zero_mem
  have hKo : ∀ x : H, x ∈ Kᗮ → S x ∈ Kᗮ := by
    have hmem : K ∈ Module.End.invtSubmodule S.adjoint.toLinearMap := by
      rw [hS.adjoint_eq]
      exact hKmem
    exact ContinuousLinearMap.orthogonal_mem_invtSubmodule hmem
  -- On `Kᗮ`, `S` is an isomorphism `e`; `e - c • 1 = e (1 - c e⁻¹)` is invertible for small `c`.
  let e : Kᗮ ≃L[ℂ] Kᗮ :=
    (S.orthogonalKerEquivRange hclosed).trans (ContinuousLinearEquiv.ofEq _ _ hrange)
  have he_apply (x : Kᗮ) : (e x : H) = S (x : H) := by
    simp only [e, ContinuousLinearEquiv.trans_apply]
    exact S.orthogonalKerEquivRange_apply hclosed x
  have hmul : (e : Kᗮ →L[ℂ] Kᗮ) * (e.symm : Kᗮ →L[ℂ] Kᗮ) = 1 := by
    rw [mul_def, ContinuousLinearEquiv.coe_comp_coe_symm, one_def]
  let n : ℝ := ‖(e.symm : Kᗮ →L[ℂ] Kᗮ)‖
  have hn1 : 0 < n + 1 := by linarith [norm_nonneg (e.symm : Kᗮ →L[ℂ] Kᗮ)]
  refine ⟨1 / (n + 1), div_pos one_pos hn1, fun c hc hnormc => ?_⟩
  have hsmall : ‖c • (e.symm : Kᗮ →L[ℂ] Kᗮ)‖ < 1 := by
    calc
      ‖c • (e.symm : Kᗮ →L[ℂ] Kᗮ)‖ ≤ ‖c‖ * n := by
        simpa only [n] using opNorm_smul_le c (e.symm : Kᗮ →L[ℂ] Kᗮ)
      _ ≤ ‖c‖ * (n + 1) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (norm_nonneg c)
      _ < 1 / (n + 1) * (n + 1) := mul_lt_mul_of_pos_right hnormc hn1
      _ = 1 := div_mul_cancel₀ (1 : ℝ) (ne_of_gt hn1)
  have hfac : (e : Kᗮ →L[ℂ] Kᗮ) - c • 1 =
      (e : Kᗮ →L[ℂ] Kᗮ) * (1 - c • (e.symm : Kᗮ →L[ℂ] Kᗮ)) := by
    rw [mul_sub, mul_one,
      Algebra.mul_smul_comm c (e : Kᗮ →L[ℂ] Kᗮ) (e.symm : Kᗮ →L[ℂ] Kᗮ), hmul]
  have hRK : ∀ x : H, x ∈ K → (S - c • (1 : H →L[ℂ] H)) x ∈ K := by
    intro x hx
    rw [sub_apply, smul_apply, one_apply_eq_self, hK0 x hx, zero_sub, ← neg_smul]
    exact K.smul_mem (-c) hx
  have hRKo : ∀ x : H, x ∈ Kᗮ → (S - c • (1 : H →L[ℂ] H)) x ∈ Kᗮ := by
    intro x hx
    rw [sub_apply, smul_apply, one_apply_eq_self]
    exact Kᗮ.sub_mem (hKo x hx) (Kᗮ.smul_mem c hx)
  have hunitKo : IsUnit ((S - c • (1 : H →L[ℂ] H)).restrict hRKo) := by
    have heq : (S - c • (1 : H →L[ℂ] H)).restrict hRKo =
        (e : Kᗮ →L[ℂ] Kᗮ) - c • 1 := by
      ext x
      rw [coe_restrict_apply, sub_apply, smul_apply, one_apply_eq_self, ← he_apply x,
        ← Submodule.coe_smul, ← Submodule.coe_sub]
      exact congrArg Subtype.val <| by
        rw [sub_apply, smul_apply, one_apply_eq_self, ContinuousLinearEquiv.coe_apply]
    rw [heq, hfac]
    exact IsUnit.mul (ContinuousLinearEquiv.toUnit e).isUnit
      (IsUnit.one_sub_of_norm_lt_one (x := c • (e.symm : Kᗮ →L[ℂ] Kᗮ)) hsmall)
  exact isUnit_of_isUnit_restrict_orthogonal _ K hRK hRKo
    (isUnit_restrict_sub_smul_of_forall_eq_zero S K hK0 hc hRK) hunitKo

/-- A self-adjoint Fredholm operator that is not invertible has a nontrivial kernel: a trivial
kernel would make it bijective. -/
private lemma ker_ne_bot_of_isFredholm_of_not_isUnit {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {S : H →L[ℂ] H} (hS : IsSelfAdjoint S)
    (hfred : IsFredholm S) (hunit : ¬ IsUnit S) :
    LinearMap.ker (S : H →ₗ[ℂ] H) ≠ ⊥ := by
  intro hbot
  have htop : LinearMap.range (S : H →ₗ[ℂ] H) = ⊤ := by
    rw [range_eq_orthogonal_ker_of_isFredholm hS hfred, hbot, Submodule.bot_orthogonal_eq_top]
  exact hunit ((ContinuousLinearMap.isUnit_iff_bijective (f := S)).mpr
    ⟨LinearMap.ker_eq_bot.mp hbot, LinearMap.range_eq_top.mp htop⟩)

/-- If `z` is in the spectrum of a self-adjoint `T` and `T - z • 1` is Fredholm, then `z` is an
isolated point of the spectrum. -/
private lemma isIsolatedIn_spectrum_of_isFredholm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) {z : ℂ}
    (hz : z ∈ spectrum ℂ T) (hfred : IsFredholm (T - z • (1 : H →L[ℂ] H))) :
    IsIsolatedIn z (spectrum ℂ T) := by
  obtain ⟨eps, heps, hunit⟩ := exists_isUnit_sub_smul_of_isFredholm
    (isSelfAdjoint_sub_smul_one_of_mem_spectrum hT hz) hfred
  refine ⟨hz, Metric.eventually_nhds_iff.mpr ⟨eps, heps, fun w hdist hw => ?_⟩⟩
  by_contra hwz
  have hshift : T - z • (1 : H →L[ℂ] H) - (w - z) • (1 : H →L[ℂ] H) =
      T - w • (1 : H →L[ℂ] H) := by
    rw [sub_smul]
    abel
  refine not_isUnit_sub_smul_one_of_mem_spectrum hw ?_
  rw [← hshift]
  rw [dist_eq_norm] at hdist
  exact hunit (w - z) (sub_ne_zero.mpr hwz) hdist

/-- At an isolated point `z` of the spectrum of a self-adjoint `T` with finite-dimensional
eigenspace, `T - z • 1` is Fredholm: the continuous functional calculus gives a finite-rank
spectral projection `P` and an operator `Q` with `(T - z • 1) Q = Q (T - z • 1) = 1 - P`. -/
private lemma isFredholm_sub_smul_of_isIsolatedIn {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) {z : ℂ}
    (hiso : IsIsolatedIn z (spectrum ℂ T))
    (hfin : FiniteDimensional ℂ (LinearMap.ker ((T - z • (1 : H →L[ℂ] H)) : H →ₗ[ℂ] H))) :
    IsFredholm (T - z • (1 : H →L[ℂ] H)) := by
  let Sz : H →L[ℂ] H := T - z • (1 : H →L[ℂ] H)
  have : IsStarNormal T := hT.isStarNormal
  let f : ℂ → ℂ := fun w => if w = z then 1 else 0
  let q : ℂ → ℂ := fun w => if w = z then 0 else (w - z)⁻¹
  have hf : ContinuousOn f (spectrum ℂ T) := continuousOn_indicator_isolated hiso
  have hq : ContinuousOn q (spectrum ℂ T) := continuousOn_resolvent_isolated hiso
  have hmul0 : ∀ w : ℂ, (w - z) * f w = 0 := by
    intro w
    by_cases hw : w = z <;> simp [f, hw]
  have hmulq : ∀ w : ℂ, (w - z) * q w = 1 - f w := by
    intro w
    by_cases hw : w = z
    · simp [f, q, hw]
    · simp [f, q, hw, mul_inv_cancel₀ (sub_ne_zero.mpr hw)]
  let P : H →L[ℂ] H := cfc f T
  let Q : H →L[ℂ] H := cfc q T
  have hcont : ContinuousOn (fun w : ℂ => w - z) (spectrum ℂ T) :=
    (continuous_id.sub continuous_const).continuousOn
  have hcontId : ContinuousOn (fun w : ℂ => w) (spectrum ℂ T) := continuous_id.continuousOn
  have hcontZ : ContinuousOn (fun _ : ℂ => z) (spectrum ℂ T) := continuousOn_const
  have hSz_cfc : cfc (fun w : ℂ => w - z) T = Sz := by
    rw [cfc_sub (fun w : ℂ => w) (fun _ : ℂ => z) T hcontId hcontZ, cfc_id' ℂ T,
      cfc_const z T, Algebra.algebraMap_eq_smul_one]
  have hSzP : Sz * P = 0 := by
    rw [← hSz_cfc, ← cfc_mul (fun w : ℂ => w - z) f T hcont hf]
    have hzero : (spectrum ℂ T).EqOn (fun w => (w - z) * f w) (fun _ => 0) :=
      fun w _ => hmul0 w
    rw [cfc_congr hzero, cfc_const_zero]
  have hkerP : LinearMap.range (P : H →ₗ[ℂ] H) ≤ LinearMap.ker (Sz : H →ₗ[ℂ] H) := by
    rw [LinearMap.range_le_ker_iff]
    simpa only [mul_def, toLinearMap_comp, toLinearMap_zero] using
      congrArg toLinearMap hSzP
  have : FiniteDimensional ℂ (LinearMap.ker (Sz : H →ₗ[ℂ] H)) := hfin
  have hfg : (P : H →ₗ[ℂ] H).HasFiniteRange := by
    rw [LinearMap.hasFiniteRange_iff_range, Submodule.fg_iff_finiteDimensional]
    exact Submodule.finiteDimensional_of_le hkerP
  have hcompact : IsCompactOperator P := hfg.isCompactOperator
  have hneg : IsCompactOperator (-P) := by simpa only [FunLike.coe_neg] using hcompact.neg
  have hSzQ : Sz * Q = 1 - P := by
    rw [← hSz_cfc, ← cfc_mul (fun w : ℂ => w - z) q T hcont hq]
    have hEq : (spectrum ℂ T).EqOn (fun w => (w - z) * q w) (fun w => 1 - f w) :=
      fun w _ => hmulq w
    rw [cfc_congr hEq, cfc_sub (fun _ : ℂ => (1 : ℂ)) f T continuousOn_const hf,
      cfc_const_one ℂ T]
  have hQSz : Q * Sz = 1 - P := by
    rw [← hSz_cfc, ← cfc_mul q (fun w : ℂ => w - z) T hq hcont]
    have hEq : (spectrum ℂ T).EqOn (fun w => q w * (w - z)) (fun w => 1 - f w) :=
      fun w _ => by
        show q w * (w - z) = 1 - f w
        rw [mul_comm, hmulq]
    rw [cfc_congr hEq, cfc_sub (fun _ : ℂ => (1 : ℂ)) f T continuousOn_const hf,
      cfc_const_one ℂ T]
  have hleft : Q.comp Sz - 1 = -P := by rw [← mul_def, hQSz]; abel
  have hright : Sz.comp Q - 1 = -P := by rw [← mul_def, hSzQ]; abel
  refine (TauCeti.isFredholm_iff_exists_isCompactOperator_comp_sub_one (T := Sz)).2 ⟨Q, ?_, ?_⟩
  · rw [hleft]; exact hneg
  · rw [hright]; exact hneg

/-- **21.16**: the discrete spectrum of a bounded self-adjoint operator is exactly its
isolated eigenvalues of finite multiplicity. -/
theorem mem_spectrum_sdiff_essentialSpectrum_iff {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (z : ℂ) :
    z ∈ spectrum ℂ T \ essentialSpectrum T ↔
      IsIsolatedIn z (spectrum ℂ T) ∧
      (LinearMap.ker ((T - z • (1 : H →L[ℂ] H)) : H →ₗ[ℂ] H)) ≠ ⊥ ∧
      FiniteDimensional ℂ (LinearMap.ker
        ((T - z • (1 : H →L[ℂ] H)) : H →ₗ[ℂ] H)) := by
  constructor
  · rintro ⟨hzspec, hnot⟩
    have hfred : IsFredholm (T - z • (1 : H →L[ℂ] H)) := by
      by_contra h
      exact hnot ((mem_essentialSpectrum_iff _ _).2 h)
    exact ⟨isIsolatedIn_spectrum_of_isFredholm hT hzspec hfred,
      ker_ne_bot_of_isFredholm_of_not_isUnit
        (isSelfAdjoint_sub_smul_one_of_mem_spectrum hT hzspec) hfred
        (not_isUnit_sub_smul_one_of_mem_spectrum hzspec), hfred.finite_ker⟩
  · rintro ⟨hiso, _, hfin⟩
    refine ⟨hiso.1, fun hmem => hmem ?_⟩
    exact isFredholm_sub_smul_of_isIsolatedIn hT hiso hfin

end CKMA
