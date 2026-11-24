/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import CKMA.Analysis.Sobolev.Fractional.Kernel
public import CKMA.Analysis.Sobolev.Fractional.Shift
public import CKMA.Analysis.Sobolev.Fractional.Translate
public import CKMA.Analysis.Sobolev.Fractional.Weight

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Fractional Hilbert and Bessel-potential energies

Gagliardo fractional square energy and Bessel-potential energy on L² for orders strictly
between zero and one. The Fourier identity has a positive finite normalization constant;
`exists_lintegral_fourierChar_sub_one_sq_div_rpow` evaluates the translation weight that
produces it.
Finite energies describe the same functions and the inhomogeneous energies are comparable.
The Fourier transform is Mathlib's L² operator and all energies retain extended values.
Source: GAPS 26.37.

## Main definitions

* `CKMA.fractionalEnergy`: Gagliardo squared fractional `H^s` seminorm on `ℝ^d`.
* `CKMA.besselPotentialEnergy`: inhomogeneous Bessel-potential `H^s` energy via the `L²` Fourier
  transform.

## Main results

* `CKMA.fractionalEnergy_eq_fourier`: Fourier representation of the Gagliardo fractional `H^s`
  seminorm (**26.37**).
* `CKMA.fractionalEnergy_ne_top_iff`, `CKMA.fractional_bessel_energy_comparable`: equivalence of
  finite Gagliardo and Bessel-potential energies on `L²(ℝ^d)`.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace

/-- Gagliardo's squared fractional `L²` seminorm, allowing infinite energy. -/
@[expose]
def fractionalEnergy {d : ℕ} (s : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℂ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, ENNReal.ofReal (‖u x - u y‖ ^ 2) /
    ENNReal.ofReal (‖x - y‖ ^ ((d : ℝ) + 2 * s))

/-- The Bessel-potential energy at order `s`, on the Fourier side of `L²`. -/
@[expose]
def besselPotentialEnergy {d : ℕ} (s : ℝ)
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * ‖(𝓕 u) ξ‖ ^ 2)

/-- Euclidean space indexed by the empty type is a single point. -/
private lemma euclideanSpace_fin_zero_eq (x y : EuclideanSpace ℝ (Fin 0)) : x = y := by
  ext i
  exact i.elim0

/-- In dimension zero the Gagliardo quotient vanishes: the domain is a single point. -/
private lemma fractionalEnergy_eq_zero_dim {s : ℝ} (u : EuclideanSpace ℝ (Fin 0) → ℂ) :
    fractionalEnergy s u = 0 := by
  rw [fractionalEnergy]
  refine (lintegral_congr fun x => ?_).trans lintegral_zero
  refine (lintegral_congr fun y => ?_).trans lintegral_zero
  obtain rfl := euclideanSpace_fin_zero_eq x y
  simp [sub_self, norm_zero, zero_pow two_ne_zero, ENNReal.ofReal_zero, ENNReal.zero_div]

/-- In dimension zero the Fourier weight `‖ξ‖^{2s} ‖𝓕 u‖²` integrates to zero. -/
private lemma fourierWeight_eq_zero_dim {s : ℝ} (hs : 0 < s)
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 0)))) :
    ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * s) * ‖(𝓕 u) ξ‖ ^ 2) = 0 := by
  have hzero : ∀ ξ : EuclideanSpace ℝ (Fin 0),
      ENNReal.ofReal (‖ξ‖ ^ (2 * s) * ‖(𝓕 u) ξ‖ ^ 2) = 0 := by
    intro ξ
    obtain rfl := euclideanSpace_fin_zero_eq ξ 0
    simp [norm_zero, Real.zero_rpow (mul_ne_zero two_ne_zero hs.ne'), zero_mul, ENNReal.ofReal_zero]
  rw [lintegral_congr hzero, lintegral_zero]

/-- In dimension zero the Bessel energy is the squared `L²` norm. -/
private lemma besselPotentialEnergy_eq_normSq_zero {s : ℝ}
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 0)))) :
    besselPotentialEnergy s u = ENNReal.ofReal (‖u‖ ^ 2) := by
  have hpt : ∀ ξ : EuclideanSpace ℝ (Fin 0),
      ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * ‖(𝓕 u) ξ‖ ^ 2) =
        ENNReal.ofReal (‖(𝓕 u) ξ‖ ^ 2) := by
    intro ξ
    obtain rfl := euclideanSpace_fin_zero_eq ξ 0
    simp [norm_zero, zero_pow two_ne_zero, Real.one_rpow, one_mul]
  rw [besselPotentialEnergy, lintegral_congr hpt]
  exact (ofReal_norm_sq_eq_lintegral (𝓕 u)).symm.trans (by simp [Lp.norm_fourier_eq])

/-- The real quotient and the extended quotient agree, including on the diagonal. -/
private lemma ofReal_phase_mul_div {d : ℕ} {p : ℝ} (hp : 0 < p) (h ξ : EuclideanSpace ℝ (Fin d))
    (z : ℂ) :
    ENNReal.ofReal (‖(Real.fourierChar ⟪h, ξ⟫ : ℂ) - 1‖ ^ 2 * ‖z‖ ^ 2) /
        ENNReal.ofReal (‖h‖ ^ p) =
      ENNReal.ofReal (‖z‖ ^ 2) *
        ENNReal.ofReal (‖(Real.fourierChar ⟪h, ξ⟫ : ℂ) - 1‖ ^ 2 / ‖h‖ ^ p) := by
  set a : ℝ := ‖(Real.fourierChar ⟪h, ξ⟫ : ℂ) - 1‖ ^ 2
  have ha : 0 ≤ a := sq_nonneg _
  by_cases hh : h = 0
  · subst hh
    simp [a, inner_zero_left, sub_self, norm_zero, zero_pow two_ne_zero, zero_mul,
      mul_zero, ENNReal.ofReal_zero, ENNReal.zero_div, Real.zero_rpow hp.ne']
  · have hden : 0 < ‖h‖ ^ p := Real.rpow_pos_of_pos (norm_pos_iff.mpr hh) p
    calc
      ENNReal.ofReal (a * ‖z‖ ^ 2) / ENNReal.ofReal (‖h‖ ^ p)
          = (ENNReal.ofReal a * ENNReal.ofReal (‖z‖ ^ 2)) / ENNReal.ofReal (‖h‖ ^ p) := by
            rw [ENNReal.ofReal_mul ha]
      _ = ENNReal.ofReal a / ENNReal.ofReal (‖h‖ ^ p) * ENNReal.ofReal (‖z‖ ^ 2) := by
            rw [ENNReal.mul_div_right_comm]
      _ = ENNReal.ofReal (a / ‖h‖ ^ p) * ENNReal.ofReal (‖z‖ ^ 2) := by
            rw [← ENNReal.ofReal_div_of_pos hden]
      _ = ENNReal.ofReal (‖z‖ ^ 2) * ENNReal.ofReal (a / ‖h‖ ^ p) := by rw [mul_comm]

/-- `n * (K * r) = K * (r * n)` as extended reals, for nonnegative factors. -/
private lemma ofReal_mul_const_rpow {K r n : ℝ} (hK : 0 ≤ K) (hn : 0 ≤ n) :
    ENNReal.ofReal n * ENNReal.ofReal (K * r) =
      ENNReal.ofReal K * ENNReal.ofReal (r * n) := by
  have hre : n * (K * r) = K * (r * n) := by
    calc
      n * (K * r) = n * K * r := by rw [mul_assoc]
      _ = K * n * r := by rw [mul_comm n K]
      _ = K * (n * r) := by rw [mul_assoc]
      _ = K * (r * n) := by rw [mul_comm n r]
  rw [← ENNReal.ofReal_mul hn, hre, ENNReal.ofReal_mul hK]

/-- The squared modulus of an `L²` representative is measurable. -/
private lemma measurable_fourier_normSq {d : ℕ}
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    Measurable fun ξ : EuclideanSpace ℝ (Fin d) => ENNReal.ofReal (‖(𝓕 u) ξ‖ ^ 2) := by
  refine ENNReal.measurable_ofReal.comp ?_
  exact (continuous_pow 2).measurable.comp
    (measurable_norm.comp (Lp.stronglyMeasurable (𝓕 u)).measurable)

/-- The weighted density `‖ξ‖^{2s} ‖𝓕 u‖²` is measurable. -/
private lemma measurable_rpow_normSq {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    Measurable fun ξ : EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (‖ξ‖ ^ (2 * s) * ‖(𝓕 u) ξ‖ ^ 2) := by
  refine ENNReal.measurable_ofReal.comp ?_
  refine Measurable.mul ?_ ?_
  · have hs' : 0 ≤ 2 * s := mul_nonneg zero_le_two hs
    exact ((continuous_norm.comp continuous_id).rpow_const fun _ => Or.inr hs').measurable
  · exact (continuous_pow 2).measurable.comp
      (measurable_norm.comp (Lp.stronglyMeasurable (𝓕 u)).measurable)

/-- The integrand `|𝐞 ⟪h, ξ⟫ - 1|² ‖𝓕 u‖²` is measurable in the frequency. -/
private lemma measurable_phase_mul_normSq {d : ℕ} (h : EuclideanSpace ℝ (Fin d))
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    Measurable fun ξ : EuclideanSpace ℝ (Fin d) => ENNReal.ofReal
      (‖(Real.fourierChar ⟪h, ξ⟫ : ℂ) - 1‖ ^ 2 * ‖(𝓕 u) ξ‖ ^ 2) := by
  have hchar : Continuous fun ξ : EuclideanSpace ℝ (Fin d) => (Real.fourierChar ⟪h, ξ⟫ : ℂ) :=
    continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (Continuous.inner continuous_const continuous_id))
  refine ENNReal.measurable_ofReal.comp ?_
  refine Measurable.mul ?_ ?_
  · exact (((hchar.sub continuous_const).norm.pow 2)).measurable
  · exact (continuous_pow 2).measurable.comp
      (measurable_norm.comp (Lp.stronglyMeasurable (𝓕 u)).measurable)

/-- The phase quotient in the increment is measurable. -/
private lemma measurable_phaseQuot {d : ℕ} {p : ℝ} (hp : 0 ≤ p) (ξ : EuclideanSpace ℝ (Fin d)) :
    Measurable fun h : EuclideanSpace ℝ (Fin d) => ENNReal.ofReal
      (‖(Real.fourierChar ⟪h, ξ⟫ : ℂ) - 1‖ ^ 2 / ‖h‖ ^ p) := by
  have hchar : Continuous fun h : EuclideanSpace ℝ (Fin d) => (Real.fourierChar ⟪h, ξ⟫ : ℂ) :=
    continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (Continuous.inner continuous_id continuous_const))
  refine ENNReal.measurable_ofReal.comp ?_
  refine Measurable.div ?_ ?_
  · exact (((hchar.sub continuous_const).norm.pow 2)).measurable
  · exact ((continuous_norm.comp continuous_id).rpow_const fun _ => Or.inr hp).measurable

/-- The product of the Fourier density and the phase quotient is measurable on the product. -/
private lemma measurable_pair_phase {d : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    Measurable fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (‖(𝓕 u) q.2‖ ^ 2) * ENNReal.ofReal
        (‖(Real.fourierChar ⟪q.1, q.2⟫ : ℂ) - 1‖ ^ 2 / ‖q.1‖ ^ p) := by
  have hchar : Continuous fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      (Real.fourierChar ⟪q.1, q.2⟫ : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (Continuous.inner continuous_fst continuous_snd))
  have hleft : Measurable fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (‖(𝓕 u) q.2‖ ^ 2) := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact (continuous_pow 2).measurable.comp (measurable_norm.comp
      ((Lp.stronglyMeasurable (𝓕 u)).measurable.comp measurable_snd))
  have hright : Measurable fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal
        (‖(Real.fourierChar ⟪q.1, q.2⟫ : ℂ) - 1‖ ^ 2 / ‖q.1‖ ^ p) := by
    refine ENNReal.measurable_ofReal.comp ?_
    refine Measurable.div ?_ ?_
    · exact (((hchar.sub continuous_const).norm.pow 2)).measurable
    · exact ((continuous_norm.comp continuous_fst).rpow_const fun _ => Or.inr hp).measurable
  exact hleft.mul hright

/-- For positive dimension, the Gagliardo energy is the kernel constant times the Fourier weight. -/
private lemma fractionalEnergy_eq_fourier_pos {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : 0 < s)
    (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))),
      fractionalEnergy s u = ENNReal.ofReal C *
        ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * s) * ‖(𝓕 u) ξ‖ ^ 2) := by
  have hp : 0 < (d : ℝ) + 2 * s := by positivity
  obtain ⟨K, hK, hkernel⟩ := exists_lintegral_fourierChar_sub_one_sq_div_rpow hd hs hs1
  refine ⟨K, hK, fun u => ?_⟩
  have hshift := lintegral_sq_div_rpow_eq_translate hp (Lp.stronglyMeasurable u)
  have hdiv : ∀ h : EuclideanSpace ℝ (Fin d),
      (∫⁻ ξ, ENNReal.ofReal
        (‖(Real.fourierChar ⟪h, ξ⟫ : ℂ) - 1‖ ^ 2 * ‖(𝓕 u) ξ‖ ^ 2)) /
        ENNReal.ofReal (‖h‖ ^ ((d : ℝ) + 2 * s)) =
      ∫⁻ ξ, ENNReal.ofReal (‖(𝓕 u) ξ‖ ^ 2) * ENNReal.ofReal
        (‖(Real.fourierChar ⟪h, ξ⟫ : ℂ) - 1‖ ^ 2 / ‖h‖ ^ ((d : ℝ) + 2 * s)) := by
    intro h
    have hmeas : AEMeasurable (fun ξ : EuclideanSpace ℝ (Fin d) => ENNReal.ofReal
        (‖(Real.fourierChar ⟪h, ξ⟫ : ℂ) - 1‖ ^ 2 * ‖(𝓕 u) ξ‖ ^ 2)) volume :=
      (measurable_phase_mul_normSq h u).aemeasurable
    rw [ENNReal.div_eq_inv_mul, ← lintegral_const_mul'' _ hmeas]
    refine lintegral_congr fun ξ => ?_
    rw [← ENNReal.div_eq_inv_mul]
    exact ofReal_phase_mul_div hp h ξ ((𝓕 u) ξ)
  have hun : AEMeasurable (Function.uncurry fun h ξ => ENNReal.ofReal (‖(𝓕 u) ξ‖ ^ 2) *
      ENNReal.ofReal (‖(Real.fourierChar ⟪h, ξ⟫ : ℂ) - 1‖ ^ 2 / ‖h‖ ^ ((d : ℝ) + 2 * s)))
      (volume.prod volume) := by
    exact (measurable_pair_phase hp.le u).aemeasurable
  have h1 : fractionalEnergy s u =
      ∫⁻ h, (∫⁻ x, ENNReal.ofReal (‖u (x + h) - u x‖ ^ 2)) /
        ENNReal.ofReal (‖h‖ ^ ((d : ℝ) + 2 * s)) := by
    rw [fractionalEnergy]
    exact hshift
  have h2 : (∫⁻ h, (∫⁻ x, ENNReal.ofReal (‖u (x + h) - u x‖ ^ 2)) /
        ENNReal.ofReal (‖h‖ ^ ((d : ℝ) + 2 * s))) =
      ∫⁻ h, (∫⁻ ξ, ENNReal.ofReal
          (‖(Real.fourierChar ⟪h, ξ⟫ : ℂ) - 1‖ ^ 2 * ‖(𝓕 u) ξ‖ ^ 2)) /
        ENNReal.ofReal (‖h‖ ^ ((d : ℝ) + 2 * s)) := by
    refine lintegral_congr fun h => ?_
    exact congrArg (fun z => z / ENNReal.ofReal (‖h‖ ^ ((d : ℝ) + 2 * s)))
      (lintegral_ofReal_norm_sq_add_eq_fourier h u)
  have h3 : (∫⁻ h, (∫⁻ ξ, ENNReal.ofReal
          (‖(Real.fourierChar ⟪h, ξ⟫ : ℂ) - 1‖ ^ 2 * ‖(𝓕 u) ξ‖ ^ 2)) /
        ENNReal.ofReal (‖h‖ ^ ((d : ℝ) + 2 * s))) =
      ∫⁻ h, ∫⁻ ξ, ENNReal.ofReal (‖(𝓕 u) ξ‖ ^ 2) * ENNReal.ofReal
        (‖(Real.fourierChar ⟪h, ξ⟫ : ℂ) - 1‖ ^ 2 / ‖h‖ ^ ((d : ℝ) + 2 * s)) :=
    lintegral_congr hdiv
  have h4 : (∫⁻ h, ∫⁻ ξ, ENNReal.ofReal (‖(𝓕 u) ξ‖ ^ 2) * ENNReal.ofReal
        (‖(Real.fourierChar ⟪h, ξ⟫ : ℂ) - 1‖ ^ 2 / ‖h‖ ^ ((d : ℝ) + 2 * s))) =
      ∫⁻ ξ, ∫⁻ h, ENNReal.ofReal (‖(𝓕 u) ξ‖ ^ 2) * ENNReal.ofReal
        (‖(Real.fourierChar ⟪h, ξ⟫ : ℂ) - 1‖ ^ 2 / ‖h‖ ^ ((d : ℝ) + 2 * s)) :=
    lintegral_lintegral_swap hun
  have h5 : (∫⁻ ξ, ∫⁻ h, ENNReal.ofReal (‖(𝓕 u) ξ‖ ^ 2) * ENNReal.ofReal
        (‖(Real.fourierChar ⟪h, ξ⟫ : ℂ) - 1‖ ^ 2 / ‖h‖ ^ ((d : ℝ) + 2 * s))) =
      ∫⁻ ξ, ENNReal.ofReal (‖(𝓕 u) ξ‖ ^ 2) * ENNReal.ofReal (K * ‖ξ‖ ^ (2 * s)) := by
    refine lintegral_congr fun ξ => ?_
    rw [lintegral_const_mul'' _ (measurable_phaseQuot hp.le ξ).aemeasurable, hkernel ξ]
  have h6 : (∫⁻ ξ, ENNReal.ofReal (‖(𝓕 u) ξ‖ ^ 2) * ENNReal.ofReal (K * ‖ξ‖ ^ (2 * s))) =
      ∫⁻ ξ, ENNReal.ofReal K *
        ENNReal.ofReal (‖ξ‖ ^ (2 * s) * ‖(𝓕 u) ξ‖ ^ 2) := by
    refine lintegral_congr fun ξ => ?_
    exact ofReal_mul_const_rpow hK.le (sq_nonneg _)
  have h7 : (∫⁻ ξ, ENNReal.ofReal K *
        ENNReal.ofReal (‖ξ‖ ^ (2 * s) * ‖(𝓕 u) ξ‖ ^ 2)) =
      ENNReal.ofReal K * ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * s) * ‖(𝓕 u) ξ‖ ^ 2) :=
    lintegral_const_mul'' _ (measurable_rpow_normSq hs.le u).aemeasurable
  exact (h1.trans h2).trans ((h3.trans h4).trans ((h5.trans h6).trans h7))

/-- Pointwise lower bound for the Bessel weight against `1 + ‖ξ‖^{2s}`. -/
private lemma bessel_integrand_ge {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (ξ : EuclideanSpace ℝ (Fin d))
    (z : ℂ) :
    ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (‖z‖ ^ 2) +
        ENNReal.ofReal (‖ξ‖ ^ (2 * s) * ‖z‖ ^ 2)) ≤
      ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * ‖z‖ ^ 2) :=
  (ofReal_bessel_weight_bounds hs (norm_nonneg ξ) (sq_nonneg ‖z‖)).1

/-- Pointwise upper bound for the Bessel weight by a multiple of `1 + ‖ξ‖^{2s}`. -/
private lemma bessel_integrand_le {d : ℕ} {s : ℝ} (hs : 0 ≤ s) (ξ : EuclideanSpace ℝ (Fin d))
    (z : ℂ) :
    ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * ‖z‖ ^ 2) ≤
      ENNReal.ofReal (2 ^ s) * (ENNReal.ofReal (‖z‖ ^ 2) +
        ENNReal.ofReal (‖ξ‖ ^ (2 * s) * ‖z‖ ^ 2)) :=
  (ofReal_bessel_weight_bounds hs (norm_nonneg ξ) (sq_nonneg ‖z‖)).2

/-- Two-sided comparison of the inhomogeneous energies when the dimension is positive. -/
private lemma fractional_bessel_bound {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))),
        ENNReal.ofReal c * (ENNReal.ofReal (‖u‖ ^ 2) + fractionalEnergy s u) ≤
            besselPotentialEnergy s u ∧
          besselPotentialEnergy s u ≤
            ENNReal.ofReal C * (ENNReal.ofReal (‖u‖ ^ 2) + fractionalEnergy s u) := by
  obtain ⟨K, hK, hId⟩ := fractionalEnergy_eq_fourier_pos hd hs hs1
  refine ⟨1 / (2 * max K 1), 2 ^ s * max K⁻¹ 1, ?_, ?_, fun u => ?_⟩
  · exact div_pos zero_lt_one (mul_pos two_pos (lt_of_lt_of_le zero_lt_one (le_max_right K 1)))
  · exact mul_pos (Real.rpow_pos_of_pos two_pos s)
      (lt_of_lt_of_le zero_lt_one (le_max_right K⁻¹ 1))
  set A : ℝ≥0∞ := ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * s) * ‖(𝓕 u) ξ‖ ^ 2)
  have hE : fractionalEnergy s u = ENNReal.ofReal K * A := hId u
  have hN : ∫⁻ ξ, ENNReal.ofReal (‖(𝓕 u) ξ‖ ^ 2) = ENNReal.ofReal (‖u‖ ^ 2) := by
    calc
      ∫⁻ ξ, ENNReal.ofReal (‖(𝓕 u) ξ‖ ^ 2) = ENNReal.ofReal (‖𝓕 u‖ ^ 2) :=
        (ofReal_norm_sq_eq_lintegral (𝓕 u)).symm
      _ = ENNReal.ofReal (‖u‖ ^ 2) := by simp [Lp.norm_fourier_eq]
  let fN : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun ξ => ENNReal.ofReal (‖(𝓕 u) ξ‖ ^ 2)
  let fA : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ :=
    fun ξ => ENNReal.ofReal (‖ξ‖ ^ (2 * s) * ‖(𝓕 u) ξ‖ ^ 2)
  let fSum : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun ξ => fN ξ + fA ξ
  let fHalf : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun ξ => ENNReal.ofReal (1 / 2) * fSum ξ
  let fUp : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ := fun ξ => ENNReal.ofReal (2 ^ s) * fSum ξ
  let fBess : EuclideanSpace ℝ (Fin d) → ℝ≥0∞ :=
    fun ξ => ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ s * ‖(𝓕 u) ξ‖ ^ 2)
  have hmeasN : AEMeasurable fN volume := (measurable_fourier_normSq u).aemeasurable
  have hmeasA : AEMeasurable fA volume := (measurable_rpow_normSq hs.le u).aemeasurable
  have hmeasSum : AEMeasurable fSum volume := hmeasN.add hmeasA
  have hge := fun ξ => bessel_integrand_ge hs.le ξ ((𝓕 u) ξ)
  have hupper := fun ξ => bessel_integrand_le hs.le ξ ((𝓕 u) ξ)
  have hge' : ∀ ξ, fHalf ξ ≤ fBess ξ := hge
  have hupper' : ∀ ξ, fBess ξ ≤ fUp ξ := hupper
  have hN' : (∫⁻ ξ, fN ξ) = ENNReal.ofReal (‖u‖ ^ 2) := hN
  have hA' : (∫⁻ ξ, fA ξ) = A := by
    unfold A
    rfl
  have hsumEq : (∫⁻ ξ, fN ξ) + (∫⁻ ξ, fA ξ) = ∫⁻ ξ, fSum ξ :=
    (lintegral_add_left' hmeasN fA).symm
  have hhalfEq : (∫⁻ ξ, fHalf ξ) = ENNReal.ofReal (1 / 2) * ∫⁻ ξ, fSum ξ :=
    lintegral_const_mul'' (ENNReal.ofReal (1 / 2)) hmeasSum
  have hupEq : (∫⁻ ξ, fUp ξ) = ENNReal.ofReal (2 ^ s) * ∫⁻ ξ, fSum ξ :=
    lintegral_const_mul'' (ENNReal.ofReal (2 ^ s)) hmeasSum
  have hle : (∫⁻ ξ, fHalf ξ) ≤ ∫⁻ ξ, fBess ξ := lintegral_mono hge'
  have hle' : (∫⁻ ξ, fBess ξ) ≤ ∫⁻ ξ, fUp ξ := lintegral_mono hupper'
  have hBess : (∫⁻ ξ, fBess ξ) = besselPotentialEnergy s u := by
    rw [besselPotentialEnergy]
  have hlo : ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (‖u‖ ^ 2) + A) ≤
      besselPotentialEnergy s u := by
    calc
      ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (‖u‖ ^ 2) + A)
          = ENNReal.ofReal (1 / 2) * ((∫⁻ ξ, fN ξ) + (∫⁻ ξ, fA ξ)) := by
            rw [← hN', ← hA']
      _ = ENNReal.ofReal (1 / 2) * ∫⁻ ξ, fSum ξ := by rw [hsumEq]
      _ = ∫⁻ ξ, fHalf ξ := hhalfEq.symm
      _ ≤ ∫⁻ ξ, fBess ξ := hle
      _ = besselPotentialEnergy s u := hBess
  have hhi : besselPotentialEnergy s u ≤
      ENNReal.ofReal (2 ^ s) * (ENNReal.ofReal (‖u‖ ^ 2) + A) := by
    calc
      besselPotentialEnergy s u = ∫⁻ ξ, fBess ξ := hBess.symm
      _ ≤ ∫⁻ ξ, fUp ξ := hle'
      _ = ENNReal.ofReal (2 ^ s) * ∫⁻ ξ, fSum ξ := hupEq
      _ = ENNReal.ofReal (2 ^ s) * ((∫⁻ ξ, fN ξ) + (∫⁻ ξ, fA ξ)) := by rw [← hsumEq]
      _ = ENNReal.ofReal (2 ^ s) * (ENNReal.ofReal (‖u‖ ^ 2) + A) := by rw [hN', hA']
  have hcmp := ennreal_weighted_comparable hK hlo hhi
  rw [← hE] at hcmp
  exact hcmp

/-- **26.37**: the fractional Hilbert identity with a positive finite convention-dependent constant.
  -/
theorem fractionalEnergy_eq_fourier {d : ℕ} {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1) : ∃ C : ℝ, 0 < C ∧
      ∀ u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))),
        fractionalEnergy s u = ENNReal.ofReal C *
          ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ (2 * s) * ‖(𝓕 u) ξ‖ ^ 2) := by
  cases d with
  | zero =>
    refine ⟨1, zero_lt_one, fun u => ?_⟩
    simp [fractionalEnergy_eq_zero_dim, fourierWeight_eq_zero_dim hs, ENNReal.ofReal_one]
  | succ n =>
    exact fractionalEnergy_eq_fourier_pos (Nat.succ_pos n) hs hs1

/-- Finite Gagliardo energy and finite Bessel energy describe the same `L²` functions. -/
theorem fractionalEnergy_ne_top_iff {d : ℕ} {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1)
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    fractionalEnergy s u ≠ ∞ ↔ besselPotentialEnergy s u ≠ ∞ := by
  cases d with
  | zero =>
    rw [fractionalEnergy_eq_zero_dim, besselPotentialEnergy_eq_normSq_zero]
    simp
  | succ n =>
    obtain ⟨c, _, hc, _, hbound⟩ := fractional_bessel_bound (Nat.succ_pos n) hs hs1
    obtain ⟨hlo, hhi⟩ := hbound u
    constructor
    · intro hE
      have hsum : ENNReal.ofReal (‖u‖ ^ 2) + fractionalEnergy s u ≠ ⊤ :=
        ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hE⟩
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsum) hhi
    · intro hB
      have hprod : ENNReal.ofReal c * (ENNReal.ofReal (‖u‖ ^ 2) + fractionalEnergy s u) ≠ ⊤ :=
        ne_top_of_le_ne_top hB hlo
      have hsum : ENNReal.ofReal (‖u‖ ^ 2) + fractionalEnergy s u ≠ ⊤ := by
        intro htop
        exact hprod (ENNReal.mul_eq_top.2 (Or.inl ⟨(ENNReal.ofReal_pos.2 hc).ne', htop⟩))
      exact (ENNReal.add_ne_top.1 hsum).2


/-- Quantitative equivalence of the inhomogeneous fractional and Bessel square energies. -/
theorem fractional_bessel_energy_comparable {d : ℕ} (hd : 0 < d) {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1) : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))),
        ENNReal.ofReal c * (ENNReal.ofReal (‖u‖ ^ 2) + fractionalEnergy s u) ≤
          besselPotentialEnergy s u ∧
        besselPotentialEnergy s u ≤
          ENNReal.ofReal C * (ENNReal.ofReal (‖u‖ ^ 2) + fractionalEnergy s u) :=
  fractional_bessel_bound hd hs hs1

end CKMA
