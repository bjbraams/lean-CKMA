/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.Fredholm.CompactPerturbation
public import TauCeti.Analysis.Normed.Operator.Compact.FiniteRank
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Atkinson's theorem and the Fredholm essential spectrum

For real or complex Banach spaces, a Fredholm operator has a bounded inverse modulo compact
remainders, and conversely. The proof uses TauCeti's compact-perturbation theorem and the
kernel/cokernel squeezing argument of the Tau Ceti contributors in
`TauCeti.Analysis.Fredholm.CompactPerturbation`.

For complex endomorphisms the Fredholm essential spectrum is invariant under compact
perturbations. For self-adjoint Hilbert-space operators, its spectral complement is the set of
isolated finite-multiplicity eigenvalues. Sources: GAPS 21.11 and 21.16.
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
  sorry

end CKMA
