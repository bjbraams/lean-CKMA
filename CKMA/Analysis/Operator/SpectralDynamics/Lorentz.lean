/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.DiagonalMeasure

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith

/-!
# Lorentz CFC approximants, Cesàro phase kernels, and spectral measure atoms

This file constructs the Lorentz continuous functional calculus approximants
`ε² ((A - λ)² + ε²)⁻¹` for a bounded self-adjoint operator `A`, proves their strong convergence
to the orthogonal projection onto `ker (A - λ)`, and uses them to show that the diagonal spectral
measure `A.diagMeasure ξ` of a vector `ξ` orthogonal to `purePointOperatorSubspace A` has no atoms.
It also develops the Cesàro-averaged phase kernel `cesaroPhase` used in Wiener's criterion for RAGE.

## Main definitions

* `CKMA.purePointOperatorSubspace`: Closed subspace spanned by the real eigenvectors of `A`.
* `CKMA.eigenLorentzFun`: Lorentz symbol `z ↦ ε² / (‖z - λ‖² + ε²)`.
* `CKMA.eigenLorentz`: Lorentz CFC approximant `cfc (eigenLorentzFun lam eps) A`.
* `CKMA.evolutionPhase`: Unitary evolution phase `exp(-i t z)`.
* `CKMA.cesaroPhase`: Cesàro average `T⁻¹ * ∫ t in 0..T, evolutionPhase t w`.

## Main results

* `CKMA.tendsto_eigenLorentz_apply`: Strong convergence of Lorentz approximants to the eigenspace
  orthogonal projection as `ε → 0`.
* `CKMA.tendsto_cesaroPhase_of_ne_zero`: The Cesàro phase kernel vanishes as `T → ∞` at nonzero
  real frequencies.
* `CKMA.diagMeasure_real_singleton_eq_zero`: Diagonal spectral measures of vectors orthogonal to
  `purePointOperatorSubspace A` have no point masses.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology MeasureTheory
open scoped InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The closed subspace spanned by the real eigenvectors of `A`. -/
def purePointOperatorSubspace (A : H →L[ℂ] H) : Submodule ℂ H :=
  (Submodule.span ℂ {x : H | ∃ a : ℝ, A x = (a : ℂ) • x}).topologicalClosure

/-- A real scalar is a self-adjoint complex number. -/
lemma isSelfAdjoint_of_im_eq_zero {lam : ℂ} (hlam : lam.im = 0) : IsSelfAdjoint lam := by
  rw [isSelfAdjoint_iff, Complex.star_def]
  exact Complex.conj_eq_iff_im.mpr hlam

/-- The real translate `A - λ` of a self-adjoint operator is self-adjoint. -/
lemma eigenShift_isSelfAdjoint (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {lam : ℂ}
    (hlam : lam.im = 0) : IsSelfAdjoint (A - lam • (1 : H →L[ℂ] H)) :=
  hA.sub ((isSelfAdjoint_of_im_eq_zero hlam).smul
    (IsSelfAdjoint.one (H →L[ℂ] H)))

/-- `A - λ` is the continuous functional calculus of `z ↦ z - λ`. -/
lemma eigenShift_eq_cfc (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (lam : ℂ) :
    A - lam • (1 : H →L[ℂ] H) = cfc (fun z : ℂ => z - lam) A := by
  have : IsStarNormal A := hA.isStarNormal
  rw [cfc_sub (fun z : ℂ => z) (fun _ : ℂ => lam) A, cfc_id' ℂ A, cfc_const lam A]
  simp [Algebra.algebraMap_eq_smul_one]

/-- On a real scalar, the square agrees with the squared modulus. -/
private lemma sq_sub_eq_ofReal_norm_sq {z lam : ℂ} (hz : z.im = 0) (hlam : lam.im = 0) :
    (z - lam) ^ 2 = ↑(‖z - lam‖ ^ 2) := by
  have hz' : z = ↑z.re := Complex.ext rfl hz
  have hl' : lam = ↑lam.re := Complex.ext rfl hlam
  rw [hz', hl', ← Complex.ofReal_sub, ← Complex.ofReal_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- Lorentz symbol `ε² / (‖z - λ‖² + ε²)`. Division by zero is the Lean totalization. -/
def eigenLorentzFun (lam : ℂ) (eps : ℝ) : ℂ → ℂ :=
  fun z => ↑(eps ^ 2 / (‖z - lam‖ ^ 2 + eps ^ 2))

/-- The Lorentz symbol is continuous for positive width. -/
lemma continuous_eigenLorentzFun {lam : ℂ} {eps : ℝ} (heps : 0 < eps) :
    Continuous (eigenLorentzFun lam eps) := by
  unfold eigenLorentzFun
  refine Complex.continuous_ofReal.comp ?_
  refine Continuous.div continuous_const
      (((continuous_norm.comp (continuous_id.sub continuous_const)).pow 2).add
        continuous_const) ?_
  intro z
  exact ne_of_gt <| lt_of_lt_of_le (by positivity : 0 < eps ^ 2)
    (le_add_of_nonneg_left (sq_nonneg _))

/-- On real points the Lorentz symbol is the rational function of `(z - λ)²`. -/
lemma eigenLorentzFun_eq_div {lam z : ℂ} (hlam : lam.im = 0) (hz : z.im = 0) (eps : ℝ) :
    eigenLorentzFun lam eps z = (eps : ℂ) ^ 2 / ((z - lam) ^ 2 + (eps : ℂ) ^ 2) := by
  rw [sq_sub_eq_ofReal_norm_sq hz hlam, eigenLorentzFun, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_add, ← Complex.ofReal_pow]

/-- Algebraic identity of the Lorentz symbol on real points. -/
private lemma eigenLorentz_symbol_id {lam z : ℂ} (hlam : lam.im = 0) (hz : z.im = 0)
    {eps : ℝ} (heps : 0 < eps) :
    (z - lam) ^ 2 * eigenLorentzFun lam eps z =
      (eps : ℂ) ^ 2 * (1 - eigenLorentzFun lam eps z) := by
  rw [eigenLorentzFun_eq_div hlam hz eps]
  have hd : (z - lam) ^ 2 + (eps : ℂ) ^ 2 ≠ 0 := by
    rw [sq_sub_eq_ofReal_norm_sq hz hlam, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Complex.ofReal_ne_zero]
    positivity
  field_simp
  ring

/-- Lorentz approximant, as a continuous functional calculus. -/
def eigenLorentz (A : H →L[ℂ] H) (lam : ℂ) (eps : ℝ) : H →L[ℂ] H :=
  cfc (eigenLorentzFun lam eps) A

/-- The Lorentz approximant is self-adjoint. -/
lemma eigenLorentz_isSelfAdjoint (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (lam : ℂ)
    (eps : ℝ) : IsSelfAdjoint (eigenLorentz A lam eps) := by
  have : IsStarNormal A := hA.isStarNormal
  rw [eigenLorentz, IsSelfAdjoint, ← cfc_star]
  exact cfc_congr fun _ _ => by simp [eigenLorentzFun, Complex.conj_ofReal]

/-- `B² φ = ε² (1 - φ)` for the Lorentz approximant `φ` of `B = A - λ`. -/
private lemma eigenLorentz_mul_shift_sq (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {lam : ℂ}
    (hlam : lam.im = 0) {eps : ℝ} (heps : 0 < eps) :
    (A - lam • (1 : H →L[ℂ] H)) ^ 2 * eigenLorentz A lam eps =
      (eps : ℂ) ^ 2 • (1 - eigenLorentz A lam eps) := by
  have : IsStarNormal A := hA.isStarNormal
  let shift : ℂ → ℂ := fun z => z - lam
  have hshift : ContinuousOn shift (spectrum ℂ A) :=
    (continuous_id.sub continuous_const).continuousOn
  have hφ : ContinuousOn (eigenLorentzFun lam eps) (spectrum ℂ A) :=
    (continuous_eigenLorentzFun heps).continuousOn
  have hsq : ContinuousOn (fun z : ℂ => shift z ^ 2) (spectrum ℂ A) := hshift.pow 2
  have hone : ContinuousOn (fun _ : ℂ => (1 : ℂ)) (spectrum ℂ A) := continuousOn_const
  rw [eigenShift_eq_cfc A hA lam, eigenLorentz, pow_two,
    ← cfc_mul shift shift A hshift hshift]
  have hpow : cfc (fun z : ℂ => shift z * shift z) A = cfc (fun z : ℂ => shift z ^ 2) A :=
    cfc_congr fun z _ => by simp [shift, pow_two]
  rw [hpow, ← cfc_mul (fun z : ℂ => shift z ^ 2) (eigenLorentzFun lam eps) A hsq hφ]
  have hdiff : cfc (fun z : ℂ => (1 : ℂ) - eigenLorentzFun lam eps z) A =
      1 - cfc (eigenLorentzFun lam eps) A := by
    rw [cfc_sub (fun _ : ℂ => (1 : ℂ)) (eigenLorentzFun lam eps) A hone hφ, cfc_const_one ℂ A]
  rw [← hdiff, ← cfc_const_mul ((eps : ℂ) ^ 2)
      (fun z : ℂ => (1 : ℂ) - eigenLorentzFun lam eps z) A
      ((continuous_const.sub (continuous_eigenLorentzFun heps)).continuousOn)]
  refine cfc_congr fun z hz => ?_
  simpa [shift] using eigenLorentz_symbol_id hlam (hA.im_eq_zero_of_mem_spectrum hz) heps

/-- The Lorentz approximant commutes with `A - λ`. -/
lemma eigenLorentz_commute_shift (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (lam : ℂ) (eps : ℝ) :
    Commute (A - lam • (1 : H →L[ℂ] H)) (eigenLorentz A lam eps) := by
  have : IsStarNormal A := hA.isStarNormal
  rw [eigenShift_eq_cfc A hA lam, eigenLorentz]
  exact cfc_commute_cfc (fun z : ℂ => z - lam) (eigenLorentzFun lam eps) A

/-- Squared norm of the shifted Lorentz approximant. -/
private lemma eigenLorentz_shift_norm_sq (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {lam : ℂ}
    (hlam : lam.im = 0) {eps : ℝ} (heps : 0 < eps) (x : H) :
    let B := A - lam • (1 : H →L[ℂ] H)
    let φ := eigenLorentz A lam eps
    ‖B (φ x)‖ ^ 2 = eps ^ 2 * ((⟪x, φ x⟫_ℂ).re - ‖φ x‖ ^ 2) := by
  intro B φ
  have hBsa : IsSelfAdjoint B := eigenShift_isSelfAdjoint A hA hlam
  have hmul := eigenLorentz_mul_shift_sq A hA hlam heps
  have happ : B (B (φ x)) = (eps : ℂ) ^ 2 • (x - φ x) := by
    have hmulx : (B ^ 2 * φ) x = ((eps : ℂ) ^ 2 • (1 - φ)) x := congr_arg (· x) hmul
    rw [mul_apply_eq_comp, pow_two, mul_apply_eq_comp, smul_apply] at hmulx
    conv_rhs at hmulx => rw [sub_apply, one_apply_eq_self]
    exact hmulx
  have hswap : ⟪B (B (φ x)), φ x⟫_ℂ = ⟪B (φ x), B (φ x)⟫_ℂ := by
    calc
      ⟪B (B (φ x)), φ x⟫_ℂ = ⟪B (φ x), B.adjoint (φ x)⟫_ℂ :=
        (B.adjoint_inner_right (B (φ x)) (φ x)).symm
      _ = ⟪B (φ x), B (φ x)⟫_ℂ := by
        rw [← ContinuousLinearMap.star_eq_adjoint, hBsa.star_eq]
  have hcoe : (eps : ℂ) ^ 2 = ↑(eps ^ 2) := (Complex.ofReal_pow eps 2).symm
  have hstar : (starRingEnd ℂ) ((eps : ℂ) ^ 2) = (eps : ℂ) ^ 2 := by
    rw [hcoe, starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
  calc
    ‖B (φ x)‖ ^ 2 = RCLike.re ⟪B (φ x), B (φ x)⟫_ℂ := norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = RCLike.re ⟪B (B (φ x)), φ x⟫_ℂ := by rw [hswap]
    _ = RCLike.re ⟪(eps : ℂ) ^ 2 • (x - φ x), φ x⟫_ℂ := by rw [happ]
    _ = RCLike.re (((eps : ℂ) ^ 2) * (⟪x, φ x⟫_ℂ - ⟪φ x, φ x⟫_ℂ)) := by
      rw [inner_smul_left, hstar, inner_sub_left]
    _ = eps ^ 2 * ((⟪x, φ x⟫_ℂ).re - ‖φ x‖ ^ 2) := by
      have hsq : (((‖φ x‖ : ℂ) ^ 2).re) = ‖φ x‖ ^ 2 := by
        rw [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        ring
      rw [hcoe, inner_self_eq_norm_sq_to_K, RCLike.mul_re, RCLike.re_eq_complex_re,
        RCLike.im_eq_complex_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.sub_re]
      congr 1
      refine congrArg (fun t : ℝ => (⟪x, φ x⟫_ℂ).re - t) ?_
      exact hsq

/-- The Lorentz approximant is a contraction. -/
private lemma eigenLorentz_norm_apply_le (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {lam : ℂ}
    (hlam : lam.im = 0) {eps : ℝ} (heps : 0 < eps) (x : H) :
    ‖eigenLorentz A lam eps x‖ ≤ ‖x‖ := by
  set φx := eigenLorentz A lam eps x
  have hsq := eigenLorentz_shift_norm_sq A hA hlam heps x
  have hnn : 0 ≤ eps ^ 2 * ((⟪x, φx⟫_ℂ).re - ‖φx‖ ^ 2) := by
    rw [← hsq]
    exact sq_nonneg _
  have hre : ‖φx‖ ^ 2 ≤ (⟪x, φx⟫_ℂ).re := by
    have hpos : 0 < eps ^ 2 := by positivity
    have : 0 ≤ (⟪x, φx⟫_ℂ).re - ‖φx‖ ^ 2 :=
      (mul_nonneg_iff_of_pos_left hpos).mp hnn
    linarith
  have hcs : (⟪x, φx⟫_ℂ).re ≤ ‖x‖ * ‖φx‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  rcases eq_or_ne φx 0 with h0 | h0
  · simp [h0]
  · have hmul : ‖φx‖ * ‖φx‖ ≤ ‖x‖ * ‖φx‖ := by
      simpa [pow_two] using hre.trans hcs
    exact le_of_mul_le_mul_of_pos_right hmul (norm_pos_iff.mpr h0)

/-- The Lorentz approximant kills approximate range vectors up to the width. -/
private lemma eigenLorentz_apply_shift_le (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {lam : ℂ}
    (hlam : lam.im = 0) {eps : ℝ} (heps : 0 < eps) (y : H) :
    ‖eigenLorentz A lam eps ((A - lam • (1 : H →L[ℂ] H)) y)‖ ≤ eps * ‖y‖ := by
  have hcomm := eigenLorentz_commute_shift A hA lam eps
  have hswap : eigenLorentz A lam eps ((A - lam • (1 : H →L[ℂ] H)) y) =
      (A - lam • (1 : H →L[ℂ] H)) (eigenLorentz A lam eps y) := by
    simpa only [mul_apply_eq_comp] using congrArg
      (fun T : H →L[ℂ] H => T y) hcomm.symm
  rw [hswap]
  have hsq := eigenLorentz_shift_norm_sq A hA hlam heps y
  have hre : (⟪y, eigenLorentz A lam eps y⟫_ℂ).re ≤ ‖y‖ * ‖eigenLorentz A lam eps y‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hle : ‖(A - lam • (1 : H →L[ℂ] H)) (eigenLorentz A lam eps y)‖ ^ 2 ≤
      eps ^ 2 * ‖y‖ ^ 2 := by
    rw [hsq]
    have hdiff : (⟪y, eigenLorentz A lam eps y⟫_ℂ).re - ‖eigenLorentz A lam eps y‖ ^ 2 ≤
        ‖y‖ * ‖eigenLorentz A lam eps y‖ := by
      have : 0 ≤ ‖eigenLorentz A lam eps y‖ ^ 2 := sq_nonneg _
      linarith
    have hnorm : ‖eigenLorentz A lam eps y‖ ≤ ‖y‖ :=
      eigenLorentz_norm_apply_le A hA hlam heps y
    have : (⟪y, eigenLorentz A lam eps y⟫_ℂ).re - ‖eigenLorentz A lam eps y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      have hmul : ‖y‖ * ‖eigenLorentz A lam eps y‖ ≤ ‖y‖ * ‖y‖ :=
        mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      linarith
    have heps0 : 0 ≤ eps ^ 2 := sq_nonneg _
    nlinarith
  have hnn : 0 ≤ eps := heps.le
  exact (le_of_sq_le_sq (by simpa [mul_pow] using hle) (mul_nonneg hnn (norm_nonneg _)))

/-- The Lorentz approximant fixes the eigenspace of `A - λ`. -/
private lemma eigenLorentz_apply_ker (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {lam : ℂ}
    (hlam : lam.im = 0) {eps : ℝ} (heps : 0 < eps) {v : H}
    (hv : (A - lam • (1 : H →L[ℂ] H)) v = 0) : eigenLorentz A lam eps v = v := by
  have hcomm := eigenLorentz_commute_shift A hA lam eps
  have hBv : (A - lam • (1 : H →L[ℂ] H)) (eigenLorentz A lam eps v) = 0 := by
    have hswap := congrArg (fun T : H →L[ℂ] H => T v) hcomm
    simpa only [mul_apply_eq_comp, hv, map_zero] using hswap
  have happ : (A - lam • (1 : H →L[ℂ] H))
      ((A - lam • (1 : H →L[ℂ] H)) (eigenLorentz A lam eps v)) =
      (eps : ℂ) ^ 2 • (v - eigenLorentz A lam eps v) := by
    have hmul := congrArg (fun T : H →L[ℂ] H => T v)
      (eigenLorentz_mul_shift_sq A hA hlam heps)
    simpa only [mul_apply_eq_comp, pow_two, smul_apply, sub_apply, one_apply_eq_self,
      map_sub] using hmul
  have hzero : (eps : ℂ) ^ 2 • (v - eigenLorentz A lam eps v) = 0 := by
    rw [hBv, map_zero] at happ
    exact happ.symm
  have heps0 : (eps : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (pow_ne_zero 2 heps.ne')
  exact (sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left heps0)).symm

/-- Lorentz approximants converge strongly to the eigenspace projection. -/
theorem tendsto_eigenLorentz_apply (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {lam : ℂ}
    (hlam : lam.im = 0) (x : H) :
    Tendsto (fun n : ℕ => eigenLorentz A lam (1 / (n + 1 : ℝ)) x) atTop
      (𝓝 ((A - lam • (1 : H →L[ℂ] H)).ker.starProjection x)) := by
  let B := A - lam • (1 : H →L[ℂ] H)
  let P := B.ker.starProjection
  have hBsa := eigenShift_isSelfAdjoint A hA hlam
  have hnorm : IsStarNormal B := hBsa.isStarNormal
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hfix (n : ℕ) : eigenLorentz A lam (1 / (n + 1 : ℝ)) (P x) = P x :=
    eigenLorentz_apply_ker A hA hlam (by positivity : 0 < 1 / (n + 1 : ℝ))
      (by simpa [B, P] using LinearMap.mem_ker.mp (B.ker.starProjection_apply_mem x))
  have hdiff (n : ℕ) :
      eigenLorentz A lam (1 / (n + 1 : ℝ)) x - P x =
        eigenLorentz A lam (1 / (n + 1 : ℝ)) (x - P x) := by
    rw [map_sub, hfix n]
  have hnorm_eq : (fun n : ℕ => ‖eigenLorentz A lam (1 / (n + 1 : ℝ)) x - P x‖) =
      fun n : ℕ => ‖eigenLorentz A lam (1 / (n + 1 : ℝ)) (x - P x)‖ := by
    funext n
    rw [hdiff n]
  rw [hnorm_eq]
  let z := x - P x
  have hz : z ∈ B.range.topologicalClosure := by
    have horth : B.kerᗮ = B.range.topologicalClosure := by
      rw [← ContinuousLinearMap.IsStarNormal.orthogonal_range hnorm,
        Submodule.orthogonal_orthogonal_eq_closure]
    rw [← horth]
    simp [z, P]
  refine Metric.tendsto_atTop.2 fun eps heps => ?_
  obtain ⟨b, hb, hdist⟩ :=
    (Metric.mem_closure_iff.mp hz (eps / 2) (half_pos heps))
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hb
  rw [← hy] at hdist
  have htail : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ)) * ‖y‖) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa [div_eq_mul_inv, mul_comm] using
      (tendsto_inv_atTop_zero.comp hinv).const_mul ‖y‖
  rw [Metric.tendsto_atTop] at htail
  obtain ⟨N, hN⟩ := htail (eps / 2) (half_pos heps)
  refine ⟨N, fun n hn => ?_⟩
  have hepsn : 0 < 1 / (n + 1 : ℝ) := by positivity
  have htail_lt : (1 / (n + 1 : ℝ)) * ‖y‖ < eps / 2 := by
    have hlt := hN n hn
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hlt
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  calc
    ‖eigenLorentz A lam (1 / (n + 1 : ℝ)) z‖ =
        ‖eigenLorentz A lam (1 / (n + 1 : ℝ)) ((z - B y) + B y)‖ := by
      conv_lhs => rw [← sub_add_cancel z (B y)]
    _ = ‖eigenLorentz A lam (1 / (n + 1 : ℝ)) (z - B y) +
          eigenLorentz A lam (1 / (n + 1 : ℝ)) (B y)‖ := by
      rw [map_add]
    _ ≤ ‖eigenLorentz A lam (1 / (n + 1 : ℝ)) (z - B y)‖ +
        ‖eigenLorentz A lam (1 / (n + 1 : ℝ)) (B y)‖ := norm_add_le _ _
    _ ≤ ‖z - B y‖ + (1 / (n + 1 : ℝ)) * ‖y‖ := by
      gcongr
      · exact eigenLorentz_norm_apply_le A hA hlam hepsn _
      · simpa [B] using eigenLorentz_apply_shift_le A hA hlam hepsn y
    _ < eps / 2 + eps / 2 :=
      add_lt_add (by simpa [dist_eq_norm] using hdist) htail_lt
    _ = eps := add_halves eps

/-- The phase `exp(-i t z)` in the bounded evolution. -/
def evolutionPhase (t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((-(t : ℂ) * Complex.I) * z)

/-- At a real frequency the phase lies on the unit circle. -/
lemma norm_evolutionPhase_of_im_eq_zero (t : ℝ) {w : ℂ} (hw : w.im = 0) :
    ‖evolutionPhase t w‖ = 1 := by
  have hw' : w = ↑w.re := Complex.ext rfl hw
  rw [evolutionPhase, Complex.norm_exp, hw']
  have hre : ((-(t : ℂ) * Complex.I) * ↑w.re).re = 0 := by
    have hcomm : (-(t : ℂ) * Complex.I) * ↑w.re = (↑(-(t * w.re))) * Complex.I := by
      simp only [Complex.ofReal_neg, Complex.ofReal_mul]
      ring
    rw [hcomm, Complex.mul_I_re, Complex.ofReal_im, neg_zero]
  rw [hre, Real.exp_zero]

/-- Cesàro kernel of the phase, `(1/T) ∫_0^T exp(-i t w) dt`. -/
def cesaroPhase (T : ℝ) (w : ℂ) : ℂ :=
  T⁻¹ * ∫ t in (0 : ℝ)..T, evolutionPhase t w

/-- The Cesàro kernel is a contraction at real frequencies. -/
lemma norm_cesaroPhase_le {T : ℝ} (hT : 0 < T) {w : ℂ} (hw : w.im = 0) :
    ‖cesaroPhase T w‖ ≤ 1 := by
  have hle : ‖∫ t in (0 : ℝ)..T, evolutionPhase t w‖ ≤ T := by
    refine (intervalIntegral.norm_integral_le_integral_norm hT.le).trans ?_
    simp_rw [norm_evolutionPhase_of_im_eq_zero _ hw, intervalIntegral.integral_const,
      sub_zero, smul_eq_mul, mul_one]
    exact le_rfl
  rw [cesaroPhase, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hT.le)]
  calc
    T⁻¹ * ‖∫ t in (0 : ℝ)..T, evolutionPhase t w‖ ≤ T⁻¹ * T :=
      mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hT.le)
    _ = 1 := inv_mul_cancel₀ hT.ne'

/-- At frequency zero the Cesàro kernel equals one. -/
lemma cesaroPhase_zero {T : ℝ} (hT : 0 < T) : cesaroPhase T 0 = 1 := by
  unfold cesaroPhase evolutionPhase
  simp only [mul_zero, Complex.exp_zero, intervalIntegral.integral_const, sub_zero]
  rw [Complex.real_smul, mul_one, Complex.ofReal_inv]
  exact inv_mul_cancel₀ (mod_cast hT.ne')

/-- The phase is differentiable, with derivative `(-i w) exp(-i t w)`. -/
private lemma hasDerivAt_evolutionPhase (w : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => evolutionPhase s w)
      (((-Complex.I) * w) * evolutionPhase t w) t := by
  unfold evolutionPhase
  simp_rw [show ∀ s : ℝ, (-(s : ℂ) * Complex.I) * w = (s : ℂ) * ((-Complex.I) * w) by
    intro s; ring]
  let c : ℂ := (-Complex.I) * w
  change HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * c))
    (c * Complex.exp ((t : ℂ) * c)) t
  rw [Complex.exp_eq_exp_ℂ, mul_comm c (NormedSpace.exp _)]
  exact ((hasDerivAt_exp (x := (t : ℂ) * c)).comp (t : ℂ)
    (hasDerivAt_mul_const c)).comp_ofReal

/-- Off zero, the Cesàro kernel of a real frequency tends to zero. -/
lemma tendsto_cesaroPhase_of_ne_zero {w : ℂ} (hw : w.im = 0) (hw0 : w ≠ 0) :
    Tendsto (fun T : ℝ => cesaroPhase T w) atTop (𝓝 0) := by
  let c : ℂ := (-Complex.I) * w
  have hc0 : c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hw0
  have hder (T : ℝ) : ∀ x ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun s => evolutionPhase s w) (c * evolutionPhase x w) x := by
    intro x _
    simpa [c] using hasDerivAt_evolutionPhase w x
  have hint (T : ℝ) : IntervalIntegrable (fun s => c * evolutionPhase s w) volume 0 T :=
    (continuous_const.mul (by
      unfold evolutionPhase
      fun_prop)).intervalIntegrable _ _
  refine Metric.tendsto_atTop.2 fun eps heps => ?_
  let M : ℝ := 2 * ‖c‖⁻¹
  have hM : 0 ≤ M := by positivity
  let T0 : ℝ := max 1 (M / eps + 1)
  have hT0pos : 0 < T0 := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hT0eps : M / T0 < eps := by
    have hden : M / eps + 1 ≤ T0 := le_max_right _ _
    have hpos : 0 < M / eps + 1 := by positivity
    calc
      M / T0 ≤ M / (M / eps + 1) := by gcongr
      _ < eps := by
        rw [div_lt_iff₀ hpos]
        have : (M / eps + 1) * eps = M + eps := by
          rw [add_mul, div_mul_cancel₀ _ heps.ne', one_mul]
        linarith
  refine ⟨T0, fun T hT => ?_⟩
  have hTpos : 0 < T := lt_of_lt_of_le hT0pos hT
  have heq : ∫ s in (0 : ℝ)..T, evolutionPhase s w =
      c⁻¹ * (evolutionPhase T w - 1) := by
    have hsub : ∫ s in (0 : ℝ)..T, c * evolutionPhase s w =
        evolutionPhase T w - evolutionPhase 0 w :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (hder T) (hint T)
    rw [intervalIntegral.integral_const_mul] at hsub
    have h0 : evolutionPhase 0 w = 1 := by simp [evolutionPhase]
    rw [h0] at hsub
    apply mul_left_cancel₀ hc0
    rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    exact hsub
  rw [dist_zero_right, cesaroPhase, heq, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr hTpos.le), norm_inv]
  have hphase : ‖evolutionPhase T w - 1‖ ≤ 2 := by
    calc
      ‖evolutionPhase T w - 1‖ ≤ ‖evolutionPhase T w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [norm_evolutionPhase_of_im_eq_zero T hw, norm_one]
      _ = 2 := by ring
  calc
    T⁻¹ * (‖c‖⁻¹ * ‖evolutionPhase T w - 1‖) ≤ T⁻¹ * (‖c‖⁻¹ * 2) := by gcongr
    _ = M / T := by ring
    _ ≤ M / T0 := by gcongr
    _ < eps := hT0eps

/-- A real frequency conjugates to the phase of the opposite frequency. -/
lemma evolutionPhase_mul_conj (t : ℝ) {s r : ℂ} (hr : r.im = 0) :
    evolutionPhase t s * conj (evolutionPhase t r) = evolutionPhase t (s - r) := by
  have hr' : conj r = r := (Complex.conj_eq_iff_im).2 hr
  unfold evolutionPhase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  rw [RingHom.map_mul (starRingEnd ℂ), hr']
  have hI : conj (-(t : ℂ) * Complex.I) = (t : ℂ) * Complex.I := by
    simp [mul_neg, Complex.conj_ofReal, Complex.conj_I, neg_mul, neg_neg]
  rw [hI]
  ring

/-- The Cesàro kernel depends continuously on the frequency. -/
lemma continuous_cesaroPhase (T : ℝ) : Continuous (cesaroPhase T) := by
  unfold cesaroPhase
  refine Continuous.const_smul ?_ (T⁻¹)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun w t => evolutionPhase t w) (by
      unfold evolutionPhase
      fun_prop) 0 T

/-- The Lorentz symbol takes values in the unit disk. -/
private lemma eigenLorentzFun_norm_le {lam z : ℂ} {eps : ℝ} (heps : 0 < eps) :
    ‖eigenLorentzFun lam eps z‖ ≤ 1 := by
  rw [eigenLorentzFun, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    div_le_one (by positivity)]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- Lorentz symbols converge pointwise to the eigenvalue indicator. -/
private lemma tendsto_eigenLorentzFun (lam z : ℂ) :
    Tendsto (fun n : ℕ => eigenLorentzFun lam (1 / (n + 1 : ℝ)) z) atTop
      (𝓝 (if z = lam then (1 : ℂ) else 0)) := by
  by_cases h : z = lam
  · subst h
    refine tendsto_const_nhds.congr fun n => ?_
    rw [ite_eq_left rfl, eigenLorentzFun, sub_self, norm_zero, zero_pow two_ne_zero, zero_add]
    have hpos : (1 / (n + 1 : ℝ)) ^ 2 ≠ 0 := by positivity
    rw [div_self hpos, Complex.ofReal_one]
  · rw [ite_eq_right h]
    have hd : 0 < ‖z - lam‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h)) 2
    have hinv : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ)) ^ 2) atTop (𝓝 0) := by
      have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      simpa [one_div] using (tendsto_inv_atTop_zero.comp hnat).pow 2
    have hle (n : ℕ) : (1 / (n + 1 : ℝ)) ^ 2 /
        (‖z - lam‖ ^ 2 + (1 / (n + 1 : ℝ)) ^ 2) ≤
        (1 / (n + 1 : ℝ)) ^ 2 / ‖z - lam‖ ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg (1 / (n + 1 : ℝ))) hd
        (le_add_of_nonneg_right (sq_nonneg _))
    have hupper : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ)) ^ 2 / ‖z - lam‖ ^ 2)
        atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using hinv.mul_const (‖z - lam‖ ^ 2)⁻¹
    exact (Complex.continuous_ofReal.tendsto 0).comp
      (squeeze_zero (fun _ => by positivity) hle hupper)

/-- Integrating the Lorentz symbol recovers its diagonal matrix element. -/
private lemma integral_eigenLorentzFun_eq (A : H →L[ℂ] H) [IsStarNormal A] (ξ : H)
    (lam : ℂ) {eps : ℝ} (heps : 0 < eps) :
    ∫ x, eigenLorentzFun lam eps x ∂(A.diagMeasure ξ) =
      ⟪ξ, eigenLorentz A lam eps ξ⟫_ℂ := by
  simpa [eigenLorentz] using ContinuousLinearMap.integral_diagMeasure_eq_inner_cfc A ξ
    (eigenLorentzFun lam eps) (continuous_eigenLorentzFun heps).continuousOn

omit [CompleteSpace H] in
/-- Real eigenvectors lie in the pure-point subspace. -/
private lemma ker_le_purePointOperatorSubspace (A : H →L[ℂ] H) {lam : ℂ}
    (hlam : lam.im = 0) :
    (A - lam • (1 : H →L[ℂ] H)).ker ≤ purePointOperatorSubspace A := by
  intro v hv
  have hlam' : lam = (lam.re : ℂ) := Complex.ext rfl hlam
  have hAv : A v = (lam.re : ℂ) • v := by
    have hv0 : (A - lam • (1 : H →L[ℂ] H)) v = 0 := LinearMap.mem_ker.mp hv
    rw [sub_apply, smul_apply, one_apply_eq_self, sub_eq_zero] at hv0
    rw [← hlam']
    exact hv0
  exact (Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨lam.re, hAv⟩)

/-- A vector orthogonal to the pure-point subspace has no eigenprojection. -/
private lemma eigenProjection_eq_zero_of_mem_orthogonal (A : H →L[ℂ] H)
    {lam : ℂ} (hlam : lam.im = 0) {ξ : H}
    (hξ : ξ ∈ (purePointOperatorSubspace A)ᗮ) :
    (A - lam • (1 : H →L[ℂ] H)).ker.starProjection ξ = 0 := by
  let B := A - lam • (1 : H →L[ℂ] H)
  have hmem : B.ker.starProjection ξ ∈ purePointOperatorSubspace A :=
    ker_le_purePointOperatorSubspace A hlam (B.ker.starProjection_apply_mem ξ)
  have hinner : ⟪B.ker.starProjection ξ, ξ⟫_ℂ = 0 :=
    ((purePointOperatorSubspace A).mem_orthogonal ξ).1 hξ _ hmem
  have hnorm := B.ker.re_inner_starProjection_eq_normSq ξ
  rw [hinner, RCLike.zero_re] at hnorm
  rw [Submodule.starProjection_apply]
  exact congrArg Subtype.val (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm.symm))

/-- Diagonal measures of continuous vectors are non-atomic. -/
lemma diagMeasure_real_singleton_eq_zero (A : H →L[ℂ] H) [IsStarNormal A]
    (hA : IsSelfAdjoint A) {ξ : H} (hξ : ξ ∈ (purePointOperatorSubspace A)ᗮ)
    (p : spectrum ℂ A) : (A.diagMeasure ξ).real {p} = 0 := by
  let lam : ℂ := p
  have hlam : lam.im = 0 := hA.im_eq_zero_of_mem_spectrum p.property
  let μ := A.diagMeasure ξ
  let F : ℕ → spectrum ℂ A → ℂ :=
    fun n x => eigenLorentzFun lam (1 / (n + 1 : ℝ)) (x : ℂ)
  let f : spectrum ℂ A → ℂ := fun x => if (x : ℂ) = lam then 1 else 0
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) μ :=
    ((continuous_eigenLorentzFun (by positivity : 0 < 1 / (n + 1 : ℝ))).comp
      continuous_subtype_val).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ x ∂μ, ‖F n x‖ ≤ 1 :=
    Eventually.of_forall fun x => eigenLorentzFun_norm_le (by positivity)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)) :=
    Eventually.of_forall fun x => by simpa [F, f] using tendsto_eigenLorentzFun lam (x : ℂ)
  have hint := tendsto_integral_of_dominated_convergence (μ := μ) (F := F) (f := f)
    (fun _ => 1) hmeas (integrable_const 1) hbound hlim
  have hinner : Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 0) := by
    have heq (n : ℕ) : ∫ x, F n x ∂μ =
        ⟪ξ, eigenLorentz A lam (1 / (n + 1 : ℝ)) ξ⟫_ℂ := by
      simpa [F] using integral_eigenLorentzFun_eq A ξ lam (by positivity)
    simp_rw [heq]
    have hproj := eigenProjection_eq_zero_of_mem_orthogonal A hlam hξ
    have hvec := tendsto_eigenLorentz_apply A hA hlam ξ
    have hcomp := ((innerSL ℂ ξ).continuous.tendsto
      ((A - lam • (1 : H →L[ℂ] H)).ker.starProjection ξ)).comp hvec
    have hcomp' : Tendsto
        (fun n : ℕ => ⟪ξ, eigenLorentz A lam (1 / (n + 1 : ℝ)) ξ⟫_ℂ) atTop
        (𝓝 ⟪ξ, (A - lam • (1 : H →L[ℂ] H)).ker.starProjection ξ⟫_ℂ) :=
      (tendsto_congr (f₁ := (innerSL ℂ ξ) ∘
          fun n : ℕ => eigenLorentz A lam (1 / (n + 1 : ℝ)) ξ)
        (fun n : ℕ => innerSL_apply_apply ℂ ξ
          (eigenLorentz A lam (1 / (n + 1 : ℝ)) ξ))).1 hcomp
    rw [hproj, inner_zero_right] at hcomp'
    exact hcomp'
  have hzero : ∫ x, f x ∂μ = 0 := tendsto_nhds_unique hint hinner
  have hfun : f = ({p} : Set (spectrum ℂ A)).indicator (fun _ => (1 : ℂ)) := by
    funext x
    by_cases hx : x = p
    · subst hx
      simp [f, lam, Set.indicator]
    · have hne : (x : ℂ) ≠ lam := fun h => hx (Subtype.ext h)
      simp [f, Set.indicator, hx, hne]
  rw [hfun, integral_indicator_const (1 : ℂ) (measurableSet_singleton p),
    Complex.real_smul, mul_one] at hzero
  exact Complex.ofReal_eq_zero.mp hzero

end CKMA
