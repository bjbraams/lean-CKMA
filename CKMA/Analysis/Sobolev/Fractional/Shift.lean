/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Translation form of a Gagliardo double integral

For a strongly measurable `ℂ`-valued function on Euclidean space and a positive exponent `p`,
the quotient `|u(x) - u(y)|² / |x - y|ᵖ` is rearranged, by left invariance of Lebesgue measure,
as an integral over the increment `h = y - x`. On the diagonal both the extended quotient and
the real quotient are zero, so the two conventions agree everywhere.

## Main results

* `CKMA.lintegral_sq_div_rpow_eq_translate`: the Gagliardo double integral equals the iterated
  integral `∫⁻ h, (∫⁻ x, |u (x + h) - u x|²) / |h|ᵖ` over the increment.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- Measurability of the squared increment `‖u (x + h) - u x‖²` in `(x, h)`. -/
private lemma measurable_translateDiff_sq {u : EuclideanSpace ℝ (Fin d) → ℂ}
    (hu : StronglyMeasurable u) :
    Measurable fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      ‖u (q.1 + q.2) - u q.1‖ ^ 2 := by
  have hum : Measurable u := hu.measurable
  refine (continuous_pow 2).measurable.comp (measurable_norm.comp ?_)
  exact (hum.comp (measurable_fst.add measurable_snd)).sub (hum.comp measurable_fst)

/-- Measurability of `‖h‖ ^ p` in `(x, h)`. -/
private lemma measurable_snd_norm_rpow {p : ℝ} (hp : 0 ≤ p) :
    Measurable fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => ‖q.2‖ ^ p := by
  refine ((continuous_norm.comp continuous_id).rpow_const fun _ => Or.inr hp).measurable.comp
    measurable_snd

/-- Measurability of `ENNReal.ofReal ‖u (x + h) - u x‖²` in `x` for fixed `h`. -/
private lemma measurable_sq_add {u : EuclideanSpace ℝ (Fin d) → ℂ} (hu : StronglyMeasurable u)
    (h : EuclideanSpace ℝ (Fin d)) :
    Measurable fun x => ENNReal.ofReal (‖u (x + h) - u x‖ ^ 2) := by
  have hum : Measurable u := hu.measurable
  refine ENNReal.measurable_ofReal.comp ?_
  refine (continuous_pow 2).measurable.comp (measurable_norm.comp ?_)
  exact (hum.comp (measurable_add_const h)).sub hum

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The Gagliardo quotient in the increment coordinate `h = y - x`. -/
theorem lintegral_sq_div_rpow_eq_translate {p : ℝ} (hp : 0 < p)
    {u : EuclideanSpace ℝ (Fin d) → ℂ} (hu : StronglyMeasurable u) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (‖u x - u y‖ ^ 2) /
        ENNReal.ofReal (‖x - y‖ ^ p)) =
      ∫⁻ h, (∫⁻ x, ENNReal.ofReal (‖u (x + h) - u x‖ ^ 2)) /
        ENNReal.ofReal (‖h‖ ^ p) := by
  have hpoint : ∀ x y : E, ENNReal.ofReal (‖u x - u y‖ ^ 2) /
      ENNReal.ofReal (‖x - y‖ ^ p) =
        ENNReal.ofReal (‖u x - u y‖ ^ 2 / ‖x - y‖ ^ p) := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      simp [sub_self, norm_zero, zero_pow two_ne_zero, ENNReal.ofReal_zero,
        ENNReal.zero_div, Real.zero_rpow hp.ne']
    · exact (ENNReal.ofReal_div_of_pos
        (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _)).symm
  rw [lintegral_congr fun x => lintegral_congr (hpoint x)]
  have hshift : ∀ x : E, ∫⁻ y, ENNReal.ofReal (‖u x - u y‖ ^ 2 / ‖x - y‖ ^ p) =
      ∫⁻ h, ENNReal.ofReal (‖u (x + h) - u x‖ ^ 2 / ‖h‖ ^ p) := by
    intro x
    rw [← lintegral_add_left_eq_self
      (fun y => ENNReal.ofReal (‖u x - u y‖ ^ 2 / ‖x - y‖ ^ p)) x]
    refine lintegral_congr fun h => ?_
    rw [norm_sub_rev, sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg]
  rw [lintegral_congr hshift]
  have hquot : ∀ x h : E, ENNReal.ofReal (‖u (x + h) - u x‖ ^ 2 / ‖h‖ ^ p) =
      ENNReal.ofReal (‖u (x + h) - u x‖ ^ 2) / ENNReal.ofReal (‖h‖ ^ p) := by
    intro x h
    by_cases hh : h = 0
    · subst hh
      simp [add_zero, sub_self, norm_zero, zero_pow two_ne_zero, ENNReal.ofReal_zero,
        ENNReal.zero_div, Real.zero_rpow hp.ne']
    · exact ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr hh) _)
  rw [lintegral_congr fun x => lintegral_congr (hquot x)]
  have hun : AEMeasurable (Function.uncurry fun x h =>
      ENNReal.ofReal (‖u (x + h) - u x‖ ^ 2) / ENNReal.ofReal (‖h‖ ^ p))
      (volume.prod volume) := by
    have hnum : Measurable fun q : E × E =>
        ENNReal.ofReal (‖u (q.1 + q.2) - u q.1‖ ^ 2) :=
      ENNReal.measurable_ofReal.comp (measurable_translateDiff_sq hu)
    have hden : Measurable fun q : E × E => ENNReal.ofReal (‖q.2‖ ^ p) :=
      ENNReal.measurable_ofReal.comp (measurable_snd_norm_rpow hp.le)
    exact (hnum.div hden).aemeasurable
  rw [lintegral_lintegral_swap hun]
  refine lintegral_congr fun h => ?_
  have hmeas : AEMeasurable (fun x => ENNReal.ofReal (‖u (x + h) - u x‖ ^ 2)) volume :=
    (measurable_sq_add hu h).aemeasurable
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const'' _ hmeas, ← div_eq_mul_inv]

end CKMA
