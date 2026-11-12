/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.Fredholm.Adjoint
public import TauCeti.Analysis.Fredholm.CompactPerturbation
public import TauCeti.Analysis.Normed.Operator.Compact.FiniteRank
public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-!
# Atkinson's theorem and the Fredholm essential spectrum

For real or complex Banach spaces, a Fredholm operator has a bounded inverse modulo compact
remainders, and conversely. The proof uses TauCeti's compact-perturbation theorem and the
kernel/cokernel squeezing argument of the Tau Ceti contributors in
`TauCeti.Analysis.Fredholm.CompactPerturbation`.

For complex endomorphisms the Fredholm essential spectrum is invariant under compact
perturbations. For self-adjoint Hilbert-space operators, its spectral complement is the set of
isolated finite-multiplicity eigenvalues. The identification uses the closed-range adjoint
theorem in `TauCeti.Analysis.Fredholm.Adjoint` and Mathlib's continuous functional calculus.
Sources: GAPS 21.11 and 21.16.
-/

@[expose] public section

noncomputable section

namespace CKMA

open ContinuousLinearMap

section Atkinson

variable {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- **21.11**, Atkinson's theorem for operators between real or complex Banach spaces.
The proof adapts the kernel/cokernel squeezing argument of the Tau Ceti contributors in
`TauCeti.Analysis.Fredholm.CompactPerturbation`, using its proved compact-perturbation theorem. -/
theorem isFredholm_iff_exists_compact_remainders (T : E →L[𝕜] F) :
    IsFredholm T ↔ ∃ S : F →L[𝕜] E,
      IsCompactOperator (S.comp T - 1 : E →L[𝕜] E) ∧
      IsCompactOperator (T.comp S - 1 : F →L[𝕜] F) := by
  constructor
  · intro hT
    obtain ⟨S, hS⟩ := hT.exists_isQuasiInverse
    refine ⟨S, ?_, ?_⟩
    · apply LinearMap.HasFiniteRange.isCompactOperator
      simpa only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_comp,
        ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id] using
        LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mp hS.1
    · apply LinearMap.HasFiniteRange.isCompactOperator
      simpa only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_comp,
        ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id] using
        LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mp hS.2
  · rintro ⟨S, hleft, hright⟩
    have hST : IsFredholm (S.comp T) := by
      have h := TauCeti.isFredholm_one_add hleft
      convert h using 1
      abel
    have hTS : IsFredholm (T.comp S) := by
      have h := TauCeti.isFredholm_one_add hright
      convert h using 1
      abel
    apply IsFredholm.of_finite_ker_coker T
    · have hker : LinearMap.ker (T : E →ₗ[𝕜] F) ≤
          LinearMap.ker ((S.comp T) : E →ₗ[𝕜] E) := by
        intro x hx
        rw [LinearMap.mem_ker] at hx ⊢
        simpa only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, map_zero] using
          congrArg S hx
      have := hST.finite_ker
      exact Submodule.finiteDimensional_of_le hker
    · have hrange : LinearMap.range ((T.comp S) : F →ₗ[𝕜] F) ≤
          LinearMap.range (T : E →ₗ[𝕜] F) := by
        rintro y ⟨z, rfl⟩
        exact ⟨S z, rfl⟩
      have := hTS.finite_coker
      exact FiniteDimensional.of_surjective (Submodule.factor hrange)
        (Submodule.factor_surjective hrange)

end Atkinson

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The Fredholm essential spectrum. Other notions of essential spectrum need not agree
for non-self-adjoint operators. -/
def essentialSpectrum (T : E →L[ℂ] E) : Set ℂ :=
  {z | ¬ IsFredholm (T - z • (1 : E →L[ℂ] E))}

/-- Compact perturbations preserve the Fredholm essential spectrum, without self-adjointness. -/
theorem essentialSpectrum_add_compact (T K : E →L[ℂ] E) (hK : IsCompactOperator K) :
    essentialSpectrum (T + K) = essentialSpectrum T := by
  ext z
  have hf : IsFredholm (T + K - z • (1 : E →L[ℂ] E)) ↔
      IsFredholm (T - z • (1 : E →L[ℂ] E)) := by
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

/-- An isolated point of a set, using a punctured neighbourhood. -/
def IsIsolatedIn (z : ℂ) (s : Set ℂ) : Prop :=
  z ∈ s ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ s, dist w z < ε → w = z

/-- The indicator of an isolated point is continuous along the ambient set. -/
private lemma continuousOn_indicator_isolated {z : ℂ} {s : Set ℂ} (h : IsIsolatedIn z s) :
    ContinuousOn (fun w : ℂ => if w = z then (1 : ℂ) else 0) s := by
  intro x _hx
  rw [Metric.continuousWithinAt_iff]
  intro eps heps
  have h' := h
  simp only [IsIsolatedIn] at h'
  obtain ⟨_, δ, hδ, hball⟩ := h'
  by_cases hxz : x = z
  · refine ⟨δ, hδ, fun y hy hyd => ?_⟩
    rw [hxz] at hyd
    have hyz : y = z := hball y hy hyd
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
  have h' := h
  simp only [IsIsolatedIn] at h'
  obtain ⟨_, δ, hδ, hball⟩ := h'
  by_cases hxz : x = z
  · refine ⟨δ, hδ, fun y hy hyd => ?_⟩
    rw [hxz] at hyd
    have hyz : y = z := hball y hy hyd
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
  · intro hz
    let Sz : H →L[ℂ] H := T - z • (1 : H →L[ℂ] H)
    have hzspec : z ∈ spectrum ℂ T := hz.1
    have hnot : z ∉ essentialSpectrum T := hz.2
    have hfred : IsFredholm Sz := by
      by_contra h
      exact hnot (by simpa [essentialSpectrum, Sz] using h)
    have hzsa : IsSelfAdjoint z :=
      RCLike.im_eq_zero_iff_isSelfAdjoint.mp (hT.im_eq_zero_of_mem_spectrum hzspec)
    have hSz : IsSelfAdjoint Sz :=
      hT.sub (hzsa.smul (IsSelfAdjoint.one (H →L[ℂ] H)))
    let K : Submodule ℂ H := LinearMap.ker (Sz : H →ₗ[ℂ] H)
    have : FiniteDimensional ℂ K := hfred.finite_ker
    have : CompleteSpace K := FiniteDimensional.complete ℂ K
    have hclosed : IsClosed (LinearMap.range (Sz : H →ₗ[ℂ] H) : Set H) :=
      hfred.isClosed_range
    have hrange : LinearMap.range (Sz : H →ₗ[ℂ] H) = Kᗮ := by
      rw [← hSz.adjoint_eq]
      exact Sz.range_adjoint_eq_orthogonal_ker_of_isClosed_range hclosed
    have hker_ne : K ≠ ⊥ := by
      intro hbot
      have htop : LinearMap.range (Sz : H →ₗ[ℂ] H) = ⊤ := by
        rw [hrange, hbot, Submodule.bot_orthogonal_eq_top]
      have hbij : Function.Bijective Sz :=
        ⟨LinearMap.ker_eq_bot.mp hbot, LinearMap.range_eq_top.mp htop⟩
      have hunit : IsUnit Sz :=
        (ContinuousLinearMap.isUnit_iff_bijective (f := Sz)).mpr hbij
      apply spectrum.mem_iff.mp hzspec
      rw [Algebra.algebraMap_eq_smul_one]
      have : z • (1 : H →L[ℂ] H) - T = -Sz := by
        simp only [Sz]
        abel
      rw [this]
      exact hunit.neg
    have hKmem : ∀ x : H, x ∈ K → Sz x ∈ K := by
      intro x hx
      have hx0 : Sz x = 0 := by
        simpa only [ContinuousLinearMap.coe_coe] using (LinearMap.mem_ker).mp hx
      rw [hx0]
      exact K.zero_mem
    have hKo : ∀ x : H, x ∈ Kᗮ → Sz x ∈ Kᗮ := by
      have hmem : K ∈ Module.End.invtSubmodule Sz.adjoint.toLinearMap := by
        rw [hSz.adjoint_eq]
        exact hKmem
      exact ContinuousLinearMap.orthogonal_mem_invtSubmodule hmem
    let e : Kᗮ ≃L[ℂ] Kᗮ :=
      (Sz.orthogonalKerEquivRange hclosed).trans (ContinuousLinearEquiv.ofEq _ _ hrange)
    have he_apply (x : Kᗮ) : (e x : H) = Sz (x : H) := by
      simp only [e, ContinuousLinearEquiv.trans_apply]
      exact Sz.orthogonalKerEquivRange_apply hclosed x
    have hmul : (e : Kᗮ →L[ℂ] Kᗮ) * (e.symm : Kᗮ →L[ℂ] Kᗮ) = 1 := by
      rw [mul_def, ContinuousLinearEquiv.coe_comp_coe_symm, one_def]
    let n : ℝ := ‖(e.symm : Kᗮ →L[ℂ] Kᗮ)‖
    let eps : ℝ := 1 / (n + 1)
    have hn1 : 0 < n + 1 := by linarith [norm_nonneg (e.symm : Kᗮ →L[ℂ] Kᗮ)]
    have heps : 0 < eps := div_pos one_pos hn1
    have hiso : ∀ w ∈ spectrum ℂ T, dist w z < eps → w = z := by
      intro w hw hdist
      by_contra hwz
      let c : ℂ := w - z
      have hnormc : ‖c‖ < eps := by simpa [c, dist_eq_norm] using hdist
      have hsmall : ‖c • (e.symm : Kᗮ →L[ℂ] Kᗮ)‖ < 1 := by
        calc
          ‖c • (e.symm : Kᗮ →L[ℂ] Kᗮ)‖ ≤ ‖c‖ * n := by
            simpa only [n] using opNorm_smul_le c (e.symm : Kᗮ →L[ℂ] Kᗮ)
          _ ≤ ‖c‖ * (n + 1) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (norm_nonneg c)
          _ < eps * (n + 1) := mul_lt_mul_of_pos_right hnormc hn1
          _ = 1 := by
            simp only [eps]
            exact div_mul_cancel₀ (1 : ℝ) (ne_of_gt hn1)
      have hfac : (e : Kᗮ →L[ℂ] Kᗮ) - c • 1 =
          (e : Kᗮ →L[ℂ] Kᗮ) * (1 - c • (e.symm : Kᗮ →L[ℂ] Kᗮ)) := by
        rw [mul_sub, mul_one,
          Algebra.mul_smul_comm c (e : Kᗮ →L[ℂ] Kᗮ) (e.symm : Kᗮ →L[ℂ] Kᗮ), hmul]
      have hRK : ∀ x : H, x ∈ K → (Sz - c • (1 : H →L[ℂ] H)) x ∈ K := by
        intro x hx
        have hx0 : Sz x = 0 := by
          simpa only [ContinuousLinearMap.coe_coe] using (LinearMap.mem_ker).mp hx
        rw [sub_apply, smul_apply, one_apply_eq_self, hx0, zero_sub, ← neg_smul]
        exact K.smul_mem (-c) hx
      have hRKo : ∀ x : H, x ∈ Kᗮ → (Sz - c • (1 : H →L[ℂ] H)) x ∈ Kᗮ := by
        intro x hx
        rw [sub_apply, smul_apply, one_apply_eq_self]
        exact Kᗮ.sub_mem (hKo x hx) (Kᗮ.smul_mem c hx)
      have hunitK : IsUnit ((Sz - c • (1 : H →L[ℂ] H)).restrict hRK) := by
        have heq : (Sz - c • (1 : H →L[ℂ] H)).restrict hRK =
            algebraMap ℂ (K →L[ℂ] K) (-c) := by
          ext x
          have hx0 : Sz (x : H) = 0 := by
            simpa only [ContinuousLinearMap.coe_coe] using (LinearMap.mem_ker).mp x.2
          rw [coe_restrict_apply, sub_apply, smul_apply, one_apply_eq_self, hx0,
            zero_sub, ← neg_smul, Algebra.algebraMap_eq_smul_one, ← Submodule.coe_smul]
          exact congrArg Subtype.val <| by rw [smul_apply, one_apply_eq_self]
        rw [heq]
        exact (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (sub_ne_zero.mpr hwz))).map
          (algebraMap ℂ (K →L[ℂ] K))
      have hunitKo : IsUnit ((Sz - c • (1 : H →L[ℂ] H)).restrict hRKo) := by
        have heq : (Sz - c • (1 : H →L[ℂ] H)).restrict hRKo =
            (e : Kᗮ →L[ℂ] Kᗮ) - c • 1 := by
          ext x
          rw [coe_restrict_apply, sub_apply, smul_apply, one_apply_eq_self, ← he_apply x,
            ← Submodule.coe_smul, ← Submodule.coe_sub]
          exact congrArg Subtype.val <| by
            rw [sub_apply, smul_apply, one_apply_eq_self, ContinuousLinearEquiv.coe_apply]
        rw [heq, hfac]
        exact IsUnit.mul (ContinuousLinearEquiv.toUnit e).isUnit
          (IsUnit.one_sub_of_norm_lt_one (x := c • (e.symm : Kᗮ →L[ℂ] Kᗮ)) hsmall)
      have hunitSc : IsUnit (Sz - c • (1 : H →L[ℂ] H)) :=
        isUnit_of_isUnit_restrict_orthogonal _ K hRK hRKo hunitK hunitKo
      apply spectrum.mem_iff.mp hw
      rw [Algebra.algebraMap_eq_smul_one]
      have hshift : w • (1 : H →L[ℂ] H) - T = -(Sz - c • (1 : H →L[ℂ] H)) := by
        have hwc : w = z + c := by
          simp only [c]
          abel
        simp only [hwc, add_smul, Sz]
        abel
      rw [hshift]
      exact hunitSc.neg
    refine ⟨?_, hker_ne, hfred.finite_ker⟩
    simp only [IsIsolatedIn]
    exact ⟨hzspec, ⟨eps, heps, hiso⟩⟩
  · rintro ⟨hiso, _, hfin⟩
    let Sz : H →L[ℂ] H := T - z • (1 : H →L[ℂ] H)
    have hzspec : z ∈ spectrum ℂ T := by
      have h := hiso
      simp only [IsIsolatedIn] at h
      exact h.1
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
    have hfred : IsFredholm Sz := by
      refine (isFredholm_iff_exists_compact_remainders Sz).2 ⟨Q, ?_, ?_⟩
      · rw [hleft]; exact hneg
      · rw [hright]; exact hneg
    refine ⟨hzspec, ?_⟩
    intro hmem
    exact hmem (by simpa [essentialSpectrum, Sz] using hfred)

end CKMA
