/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.ProperSpace
import TauCeti.Analysis.Fourier.ChangeOfVariables

/-!
# Translation on `L²` and its Fourier transform

The squared `L²` norm is the integral of the squared pointwise norm. Translating an `L²` function
and subtracting the original function multiplies the Mathlib `L²` Fourier transform by the
character `𝐞 ⟪h, ·⟫ - 1`. The Schwartz case is TauCeti's `fourier_comp_sub_const`; the general case
follows by density of Schwartz functions in `L²`.

## Main results

* `CKMA.ofReal_norm_sq_eq_lintegral`: `‖u‖₂²` as the lower integral of `‖u x‖²`.
* `CKMA.lintegral_ofReal_norm_sq_add_eq_fourier`: `∫ |u (x + h) - u x|² dx` equals
  `∫ |𝐞 ⟪h, ξ⟫ - 1|² |û ξ|² dξ` for `u ∈ L²`.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace

variable {d : ℕ}

local notation "Euc" => EuclideanSpace ℝ (Fin d)

/-- The squared norm of an `L²` class is the integral of the squared norm of a representative. -/
theorem ofReal_norm_sq_eq_lintegral {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (f : Lp E 2 μ) :
    ENNReal.ofReal (‖f‖ ^ 2) = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
  have hpt : ∀ z : E, ‖z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
    intro z
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg z) zero_le_two, Real.rpow_two]
  have hne : eLpNorm f 2 μ ≠ ⊤ := Lp.eLpNorm_ne_top f
  calc
    ENNReal.ofReal (‖f‖ ^ 2) = (eLpNorm f 2 μ) ^ (2 : ℝ) := by
      rw [Lp.norm_def, ← Real.rpow_two,
        ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg zero_le_two,
        ENNReal.ofReal_toReal hne]
    _ = ((∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
        (Lp.aestronglyMeasurable f), ENNReal.toReal_ofNat]
    _ = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ ((1 / (2 : ℝ)) * 2) := by
      rw [← ENNReal.rpow_mul]
    _ = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
      rw [one_div_mul_cancel (two_ne_zero : (2 : ℝ) ≠ 0), ENNReal.rpow_one]
    _ = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := lintegral_congr fun x => hpt (f x)

/-- The Fourier character `𝐞 ⟪h, ξ⟫` as a complex number. -/
private def fourierPhase (h ξ : Euc) : ℂ :=
  (Real.fourierChar ⟪h, ξ⟫ : ℂ)

/-- The character `ξ ↦ 𝐞 ⟪h, ξ⟫` is continuous. -/
private lemma continuous_fourierPhase (h : Euc) : Continuous (fourierPhase h) :=
  continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp (Continuous.inner continuous_const continuous_id))

/-- The Fourier character has modulus one. -/
private lemma norm_fourierPhase (h ξ : Euc) : ‖fourierPhase h ξ‖ = 1 := by
  simp [fourierPhase]

/-- Translation of an `L²` function along `h`, as a map on the `L²` space. -/
private def lpTranslate (h : Euc) : Lp ℂ 2 (volume : Measure Euc) → Lp ℂ 2 (volume : Measure Euc) :=
  Lp.compMeasurePreserving (fun x => x + h) (measurePreserving_add_right volume h)

/-- Multiplication by `𝐞 ⟪h, ·⟫` preserves the `L²` class. -/
private lemma memLp_mul_fourierPhase (h : Euc) (u : Lp ℂ 2 (volume : Measure Euc)) :
    MemLp (fun ξ => fourierPhase h ξ * u ξ) 2 (volume : Measure Euc) := by
  have hmul : AEStronglyMeasurable (fun ξ => fourierPhase h ξ * (u : Euc → ℂ) ξ) volume :=
    (continuous_fourierPhase h).stronglyMeasurable.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable u)
  have hnorm : ∀ᵐ ξ ∂volume, ‖fourierPhase h ξ * u ξ‖ = ‖u ξ‖ := by
    filter_upwards with ξ
    rw [norm_mul, norm_fourierPhase, one_mul]
  rw [memLp_iff, eLpNorm_congr_norm_ae hmul (Lp.aestronglyMeasurable u) hnorm]
  exact Lp.eLpNorm_lt_top u

/-- The `L²` class of `ξ ↦ 𝐞 ⟪h, ξ⟫ • (u ξ)`. -/
private def lpMulPhase (h : Euc) (u : Lp ℂ 2 (volume : Measure Euc)) :
    Lp ℂ 2 (volume : Measure Euc) :=
  (memLp_mul_fourierPhase h u).toLp (fun ξ => fourierPhase h ξ * u ξ)

/-- A representative of `lpMulPhase` is pointwise multiplication by the character. -/
private lemma coeFn_lpMulPhase (h : Euc) (u : Lp ℂ 2 (volume : Measure Euc)) :
    lpMulPhase h u =ᵐ[volume] fun ξ => fourierPhase h ξ * u ξ :=
  MemLp.coeFn_toLp _

/-- Multiplication by the character preserves the `L²` norm. -/
private lemma norm_lpMulPhase (h : Euc) (u : Lp ℂ 2 (volume : Measure Euc)) :
    ‖lpMulPhase h u‖ = ‖u‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  rw [eLpNorm_congr_ae (coeFn_lpMulPhase h u)]
  have hmul : AEStronglyMeasurable (fun ξ => fourierPhase h ξ * (u : Euc → ℂ) ξ) volume :=
    (continuous_fourierPhase h).stronglyMeasurable.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable u)
  have hnorm : ∀ᵐ ξ ∂volume, ‖fourierPhase h ξ * u ξ‖ = ‖u ξ‖ := by
    filter_upwards with ξ
    rw [norm_mul, norm_fourierPhase, one_mul]
  exact eLpNorm_congr_norm_ae hmul (Lp.aestronglyMeasurable u) hnorm

/-- Multiplication by the character intertwines subtraction. -/
private lemma lpMulPhase_sub (h : Euc) (u v : Lp ℂ 2 (volume : Measure Euc)) :
    lpMulPhase h u - lpMulPhase h v = lpMulPhase h (u - v) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (lpMulPhase h u) (lpMulPhase h v), coeFn_lpMulPhase h u,
    coeFn_lpMulPhase h v, coeFn_lpMulPhase h (u - v), Lp.coeFn_sub u v] with ξ hsub hu hv huv hdiff
  rw [hsub, Pi.sub_apply, hu, hv, huv, hdiff, Pi.sub_apply, ← mul_sub]

/-- Multiplication by the character is an isometry of `L²`. -/
private lemma isometry_lpMulPhase (h : Euc) : Isometry (lpMulPhase h) := by
  refine Isometry.of_dist_eq fun u v => ?_
  rw [dist_eq_norm, dist_eq_norm, lpMulPhase_sub, norm_lpMulPhase]

set_option backward.isDefEq.respectTransparency.types false in
/-- Translating a Schwartz representative agrees with the Schwartz translation. -/
private lemma lpTranslate_toLp (h : Euc) (φ : SchwartzMap Euc ℂ) :
    lpTranslate h (φ.toLp 2) = (φ.compSubConstCLM ℂ (-h)).toLp 2 := by
  rw [lpTranslate, SchwartzMap.toLp, SchwartzMap.toLp]
  rw [Lp.toLp_compMeasurePreserving (φ.memLp 2 volume) (measurePreserving_add_right volume h)]
  exact MemLp.toLp_congr
    (((φ.memLp 2 volume).comp_measurePreserving (measurePreserving_add_right volume h)))
    ((φ.compSubConstCLM ℂ (-h)).memLp 2 volume)
    (ae_of_all volume fun x => by simp [sub_neg_eq_add])

/-- On Schwartz functions, translation multiplies the Fourier transform by `𝐞 ⟪h, ·⟫`. -/
private lemma fourier_compSubConst (h : Euc) (φ : SchwartzMap Euc ℂ) (ξ : Euc) :
    (𝓕 (φ.compSubConstCLM ℂ (-h))) ξ = fourierPhase h ξ * (𝓕 φ) ξ := by
  have hfun : ((φ.compSubConstCLM ℂ (-h)) : Euc → ℂ) = fun x => φ (x - -h) := by
    funext x
    simp
  rw [SchwartzMap.fourier_coe, hfun, TauCeti.fourier_comp_sub_const (φ : Euc → ℂ) (-h) ξ,
    ← SchwartzMap.fourier_coe, inner_neg_left, neg_neg, Circle.smul_def, smul_eq_mul,
    fourierPhase]

/-- The Fourier transform of a translated Schwartz class is modulation of its transform. -/
private lemma fourier_lpTranslate_toLp (h : Euc) (φ : SchwartzMap Euc ℂ) :
    𝓕 (lpTranslate h (φ.toLp 2)) = lpMulPhase h (𝓕 (φ.toLp 2)) := by
  rw [lpTranslate_toLp, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [SchwartzMap.coeFn_toLp (𝓕 (φ.compSubConstCLM ℂ (-h))) 2 (volume : Measure Euc),
    coeFn_lpMulPhase h ((𝓕 φ).toLp 2),
    SchwartzMap.coeFn_toLp (𝓕 φ) 2 (volume : Measure Euc)] with ξ hψ hphase hφ
  rw [hψ, hphase, hφ]
  exact fourier_compSubConst h φ ξ

/-- The Fourier transform of an `L²` translate is modulation of the transform. -/
private lemma fourier_lpTranslate (h : Euc) (u : Lp ℂ 2 (volume : Measure Euc)) :
    𝓕 (lpTranslate h u) = lpMulPhase h (𝓕 u) := by
  refine (SchwartzMap.denseRange_toLpCLM (E := Euc) (F := ℂ) (μ := (volume : Measure Euc)) (p := 2)
      ENNReal.ofNat_ne_top).induction_on u (isClosed_eq ?_ ?_) ?_
  · exact (fourierCLM ℂ (Lp ℂ 2 (volume : Measure Euc))).continuous.comp
      (Lp.isometry_compMeasurePreserving (measurePreserving_add_right volume h)).continuous
  · exact (isometry_lpMulPhase h).continuous.comp
      (fourierCLM ℂ (Lp ℂ 2 (volume : Measure Euc))).continuous
  · intro φ
    simpa [SchwartzMap.toLpCLM_apply] using fourier_lpTranslate_toLp h φ

/-- A representative of `lpMulPhase h u - u` is multiplication by `𝐞 ⟪h, ·⟫ - 1`. -/
private lemma ofReal_norm_sq_lpMulPhase_sub (h : Euc) (u : Lp ℂ 2 (volume : Measure Euc)) :
    (fun ξ => ENNReal.ofReal (‖(lpMulPhase h u - u) ξ‖ ^ 2)) =ᵐ[volume]
      fun ξ => ENNReal.ofReal
        (‖(Real.fourierChar ⟪h, ξ⟫ : ℂ) - 1‖ ^ 2 * ‖u ξ‖ ^ 2) := by
  filter_upwards [Lp.coeFn_sub (lpMulPhase h u) u, coeFn_lpMulPhase h u] with ξ hdiff hphase
  refine congrArg ENNReal.ofReal ?_
  have halg : fourierPhase h ξ * u ξ - u ξ = (fourierPhase h ξ - 1) * u ξ := by
    calc
      fourierPhase h ξ * u ξ - u ξ = fourierPhase h ξ * u ξ - 1 * u ξ := by rw [one_mul]
      _ = (fourierPhase h ξ - 1) * u ξ := by rw [← sub_mul]
  rw [hdiff, Pi.sub_apply, hphase, halg, norm_mul, mul_pow, fourierPhase]

/-- The squared `L²` increment equals the Fourier integral weighted by `|𝐞 ⟪h, ξ⟫ - 1|²`. -/
theorem lintegral_ofReal_norm_sq_add_eq_fourier (h : EuclideanSpace ℝ (Fin d))
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    ∫⁻ x, ENNReal.ofReal (‖u (x + h) - u x‖ ^ 2) =
      ∫⁻ ξ, ENNReal.ofReal
        (‖(Real.fourierChar ⟪h, ξ⟫ : ℂ) - 1‖ ^ 2 * ‖(𝓕 u) ξ‖ ^ 2) := by
  have hsubLp : 𝓕 (lpTranslate h u - u) = lpMulPhase h (𝓕 u) - 𝓕 u := by
    rw [← fourierCLM_apply (R := ℂ), map_sub, fourierCLM_apply, fourierCLM_apply,
      fourier_lpTranslate h u]
  have hL : ∫⁻ x, ENNReal.ofReal (‖u (x + h) - u x‖ ^ 2) =
      ∫⁻ x, ENNReal.ofReal (‖(lpTranslate h u - u) x‖ ^ 2) := by
    simp_rw [lpTranslate]
    refine lintegral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub
        (Lp.compMeasurePreserving (fun x => x + h) (measurePreserving_add_right volume h) u) u,
      Lp.coeFn_compMeasurePreserving u (measurePreserving_add_right volume h)] with x hdiff hcomp
    rw [hdiff, Pi.sub_apply, hcomp, Function.comp_apply]
  have h2 : ∫⁻ x, ENNReal.ofReal (‖(lpTranslate h u - u) x‖ ^ 2) =
      ENNReal.ofReal (‖lpTranslate h u - u‖ ^ 2) :=
    (ofReal_norm_sq_eq_lintegral _).symm
  have h3 : ENNReal.ofReal (‖lpTranslate h u - u‖ ^ 2) =
      ENNReal.ofReal (‖𝓕 (lpTranslate h u - u)‖ ^ 2) := by
    rw [Lp.norm_fourier_eq]
  have h4 : ENNReal.ofReal (‖𝓕 (lpTranslate h u - u)‖ ^ 2) =
      ∫⁻ ξ, ENNReal.ofReal (‖(𝓕 (lpTranslate h u - u)) ξ‖ ^ 2) :=
    ofReal_norm_sq_eq_lintegral _
  have h5 : ∫⁻ ξ, ENNReal.ofReal (‖(𝓕 (lpTranslate h u - u)) ξ‖ ^ 2) =
      ∫⁻ ξ, ENNReal.ofReal (‖(lpMulPhase h (𝓕 u) - 𝓕 u) ξ‖ ^ 2) := by
    rw [hsubLp]
  have h6 : ∫⁻ ξ, ENNReal.ofReal (‖(lpMulPhase h (𝓕 u) - 𝓕 u) ξ‖ ^ 2) =
      ∫⁻ ξ, ENNReal.ofReal
        (‖(Real.fourierChar ⟪h, ξ⟫ : ℂ) - 1‖ ^ 2 * ‖(𝓕 u) ξ‖ ^ 2) :=
    lintegral_congr_ae (ofReal_norm_sq_lpMulPhase_sub h (𝓕 u))
  exact (((hL.trans h2).trans h3).trans h4).trans (h5.trans h6)

end CKMA
