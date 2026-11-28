/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.BoxIntegral.Box.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Covering.Vitali

/-!
# One-dimensional weak type and the strong maximal kernel

Axis-parallel rectangles, the strong maximal operator, and the uncentered weak-type bound on
the line. The endpoint growth is `u(1+log⁺u)^(d-1)`, and the iteration kernel compares a
half-scaled growth of order `n` with the growth of order `n + 1`.

## Main definitions

* `CKMA.OpenRectangle`: bounded open axis-parallel rectangles in `ℝ^d` with positive side lengths,
  given as Mathlib's `BoxIntegral.Box (Fin d)` with the open interior as carrier.
* `CKMA.strongMaximalFunction`: the uncentered strong maximal operator.
* `CKMA.strongMaximalGrowth`: the Orlicz growth function `u (1 + log⁺ u)^{d-1}`.
* `CKMA.IsLocallyLLog`, `CKMA.RectanglesDifferentiateAt`: local `L(log⁺ L)^{d-1}` integrability and
  pointwise rectangular differentiation.
* `CKMA.OpenInterval`, `CKMA.RatInterval`: open intervals with real and with rational endpoints.
* `CKMA.intervalMaximalFunction`: the uncentered maximal function on `ℝ` of a function with values
  in `ℝ≥0∞`, the supremum of its averages over the open intervals containing the point.
* `CKMA.strongMaximalIterationFactor`: the constant `2 (1 + log 4)^n` of the iteration kernel.

## Main results

* `CKMA.exists_ratInterval_of_average_gt`: a strict interval average persists on a slightly
  larger interval with rational endpoints.
* `CKMA.intervalMaximalFunction_weakType`: weak-type `(1, 1)` inequality with constant `5` for the
  one-dimensional uncentered maximal function, by the Vitali covering lemma.
* `CKMA.strongMaximal_weakType_one`: the strong maximal operator on `ℝ¹` is of weak type `(1, 1)`.
* `CKMA.strongMaximalGrowth_scaled_kernel`: kernel inequality bounding half the growth of order
  `n` at `2u` plus its logarithmic integral by a multiple of the growth of order `n + 1` at `u`.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Set
open scoped BigOperators ENNReal

/-- A bounded open axis-parallel box with positive side lengths in `ℝ^d`: Mathlib's
`BoxIntegral.Box` on the index type `Fin d`, used through its open interior
`CKMA.OpenRectangle.carrier`. -/
abbrev OpenRectangle (d : ℕ) : Type := BoxIntegral.Box (Fin d)

/-- The underlying open set of a rectangle. -/
@[expose]
def OpenRectangle.carrier {d : ℕ} (R : OpenRectangle d) : Set (Fin d → ℝ) :=
  {x | ∀ j, R.lower j < x j ∧ x j < R.upper j}

/-- A point lies in a rectangle when each coordinate lies strictly between the side endpoints. -/
theorem OpenRectangle.mem_carrier {d : ℕ} {R : OpenRectangle d} {x : Fin d → ℝ} :
    x ∈ R.carrier ↔ ∀ j, R.lower j < x j ∧ x j < R.upper j :=
  Iff.rfl

/-- Sum of side lengths, an equivalent fixed-dimensional measure of shrinking rectangles. -/
@[expose]
def OpenRectangle.totalWidth {d : ℕ} (R : OpenRectangle d) : ℝ :=
  ∑ j, (R.upper j - R.lower j)

/-- The total width is the sum of the side lengths. -/
theorem OpenRectangle.totalWidth_def {d : ℕ} (R : OpenRectangle d) :
    R.totalWidth = ∑ j, (R.upper j - R.lower j) :=
  rfl

/-- Signed average on a rectangle; used when local integrability is assumed. -/
@[expose]
def OpenRectangle.average {d : ℕ} (R : OpenRectangle d) (f : (Fin d → ℝ) → ℝ) : ℝ :=
  (volume R.carrier).toReal⁻¹ * ∫ y in R.carrier, f y

/-- The average is the Bochner integral over the rectangle divided by its volume. -/
theorem OpenRectangle.average_def {d : ℕ} (R : OpenRectangle d) (f : (Fin d → ℝ) → ℝ) :
    R.average f = (volume R.carrier).toReal⁻¹ * ∫ y in R.carrier, f y :=
  rfl

/-- The positive strong maximal operator, retaining infinite local integrals. -/
@[expose]
def strongMaximalFunction {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ≥0∞ :=
  ⨆ (R : OpenRectangle d) (_hx : x ∈ R.carrier),
    (∫⁻ y in R.carrier, ENNReal.ofReal |f y|) / volume R.carrier

/-- The strong maximal function is the supremum of the averages of `|f|` over the rectangles
containing the point. -/
theorem strongMaximalFunction_def {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    strongMaximalFunction f x = ⨆ (R : OpenRectangle d) (_hx : x ∈ R.carrier),
      (∫⁻ y in R.carrier, ENNReal.ofReal |f y|) / volume R.carrier :=
  rfl

/-- The average of `|f|` over a rectangle containing `x` is at most the strong maximal function
at `x`. -/
theorem le_strongMaximalFunction {d : ℕ} (f : (Fin d → ℝ) → ℝ) {x : Fin d → ℝ}
    {R : OpenRectangle d} (hx : x ∈ R.carrier) :
    (∫⁻ y in R.carrier, ENNReal.ofReal |f y|) / volume R.carrier ≤ strongMaximalFunction f x :=
  le_iSup₂_of_le R hx le_rfl

/-- A bound for the averages of `|f|` over all rectangles containing `x` bounds the strong
maximal function at `x`. -/
theorem strongMaximalFunction_le {d : ℕ} {f : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ} {c : ℝ≥0∞}
    (h : ∀ R : OpenRectangle d, x ∈ R.carrier →
      (∫⁻ y in R.carrier, ENNReal.ofReal |f y|) / volume R.carrier ≤ c) :
    strongMaximalFunction f x ≤ c :=
  iSup₂_le h

/-- The strong maximal function exceeds `c` at `x` exactly when the average of `|f|` over some
rectangle containing `x` does. -/
theorem lt_strongMaximalFunction_iff {d : ℕ} {f : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    {c : ℝ≥0∞} :
    c < strongMaximalFunction f x ↔ ∃ R : OpenRectangle d, x ∈ R.carrier ∧
      c < (∫⁻ y in R.carrier, ENNReal.ofReal |f y|) / volume R.carrier := by
  simp only [strongMaximalFunction, lt_iSup_iff, exists_prop]

/-- The endpoint Orlicz growth `u(1+log⁺u)^(d-1)` for nonnegative `u`. -/
@[expose]
def strongMaximalGrowth (d : ℕ) (u : ℝ) : ℝ :=
  u * (1 + Real.posLog u) ^ (d - 1)

/-- The growth function is `u (1 + log⁺ u)^(d-1)`. -/
theorem strongMaximalGrowth_def (d : ℕ) (u : ℝ) :
    strongMaximalGrowth d u = u * (1 + Real.posLog u) ^ (d - 1) :=
  rfl

/-- `1 + log⁺ (c u) ≤ (1 + |log c|) (1 + log⁺ u)` for all real `c` and `u`. -/
theorem one_add_posLog_mul_le (c u : ℝ) :
    1 + Real.posLog (c * u) ≤ (1 + |Real.log c|) * (1 + Real.posLog u) := by
  have hc : Real.posLog c ≤ |Real.log c| := by
    rw [Real.abs_log_eq_posLog_add_posLog_inv]
    linarith [Real.posLog_nonneg (x := c⁻¹)]
  nlinarith [Real.posLog_mul (x := c) (y := u), abs_nonneg (Real.log c),
    Real.posLog_nonneg (x := u)]

/-- Local endpoint integrability, expressed on all compact subsets. -/
@[expose]
def IsLocallyLLog (d : ℕ) (f : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ K : Set (Fin d → ℝ), IsCompact K →
    IntegrableOn (fun x ↦ strongMaximalGrowth d |f x|) K

/-- Unfolding of `CKMA.IsLocallyLLog`. -/
theorem isLocallyLLog_iff {d : ℕ} {f : (Fin d → ℝ) → ℝ} :
    IsLocallyLLog d f ↔ ∀ K : Set (Fin d → ℝ), IsCompact K →
      IntegrableOn (fun x ↦ strongMaximalGrowth d |f x|) K :=
  Iff.rfl

/-- All rectangles containing the point, with unrestricted eccentricity, recover its value. -/
@[expose]
def RectanglesDifferentiateAt {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ R : OpenRectangle d,
    x ∈ R.carrier → R.totalWidth < δ → |R.average f - f x| < ε

/-- Unfolding of `CKMA.RectanglesDifferentiateAt`. -/
theorem rectanglesDifferentiateAt_iff {d : ℕ} {f : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ} :
    RectanglesDifferentiateAt f x ↔ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ R : OpenRectangle d, x ∈ R.carrier → R.totalWidth < δ → |R.average f - f x| < ε :=
  Iff.rfl

/-- An open bounded interval, the one-dimensional case of an open rectangle. -/
structure OpenInterval where
  /-- Left endpoint. -/
  left : ℝ
  /-- Right endpoint. -/
  right : ℝ
  /-- The interval is nonempty. -/
  left_lt_right : left < right

namespace OpenInterval

/-- The underlying open interval. -/
@[expose]
def carrier (I : OpenInterval) : Set ℝ := Ioo I.left I.right

/-- The carrier is the open interval between the endpoints. -/
theorem carrier_def (I : OpenInterval) : I.carrier = Ioo I.left I.right :=
  rfl

/-- Euclidean length. -/
@[expose]
def length (I : OpenInterval) : ℝ := I.right - I.left

/-- The length is the difference of the endpoints. -/
theorem length_def (I : OpenInterval) : I.length = I.right - I.left :=
  rfl

/-- The length is positive. -/
theorem length_pos (I : OpenInterval) : 0 < I.length := sub_pos.2 I.left_lt_right

/-- The carrier is nonempty. -/
private theorem carrier_nonempty (I : OpenInterval) : I.carrier.Nonempty :=
  nonempty_Ioo.2 I.left_lt_right

end OpenInterval

/-- Extended average of a nonnegative function over an open interval. -/
@[expose]
def intervalAverage (g : ℝ → ℝ≥0∞) (I : OpenInterval) : ℝ≥0∞ :=
  (∫⁻ t in I.carrier, g t) / ENNReal.ofReal I.length

/-- The interval average is the lower integral divided by the length. -/
theorem intervalAverage_def (g : ℝ → ℝ≥0∞) (I : OpenInterval) :
    intervalAverage g I = (∫⁻ t in I.carrier, g t) / ENNReal.ofReal I.length :=
  rfl

/-- The uncentered maximal function of a function with values in the extended nonnegative reals. -/
@[expose]
def intervalMaximalFunction (φ : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ⨆ I : OpenInterval, ⨆ (_ : x ∈ I.carrier), intervalAverage φ I

/-- Unfolding of `CKMA.intervalMaximalFunction`. -/
theorem intervalMaximalFunction_def (φ : ℝ → ℝ≥0∞) (x : ℝ) :
    intervalMaximalFunction φ x = ⨆ I : OpenInterval, ⨆ (_ : x ∈ I.carrier), intervalAverage φ I :=
  rfl

/-- The average over an interval containing `x` is at most the maximal function at `x`. -/
theorem intervalAverage_le_intervalMaximalFunction (φ : ℝ → ℝ≥0∞) {x : ℝ} {I : OpenInterval}
    (hx : x ∈ I.carrier) : intervalAverage φ I ≤ intervalMaximalFunction φ x :=
  le_iSup₂_of_le I hx le_rfl

/-- The maximal function exceeds `c` at `x` exactly when the average over some open interval
containing `x` does. -/
theorem lt_intervalMaximalFunction_iff {φ : ℝ → ℝ≥0∞} {x : ℝ} {c : ℝ≥0∞} :
    c < intervalMaximalFunction φ x ↔
      ∃ I : OpenInterval, x ∈ I.carrier ∧ c < intervalAverage φ I := by
  simp only [intervalMaximalFunction, lt_iSup_iff, exists_prop]

/-- The uncentered one-dimensional Hardy–Littlewood maximal function. -/
private def oneDimMaximal (g : ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  intervalMaximalFunction (fun t ↦ ENNReal.ofReal |g t|) x

/-- An open interval with rational endpoints. -/
structure RatInterval where
  /-- Left endpoint. -/
  left : ℚ
  /-- Right endpoint. -/
  right : ℚ
  /-- The endpoints are ordered. -/
  left_lt_right : left < right

namespace RatInterval

/-- The underlying open interval. -/
@[expose]
def carrier (I : RatInterval) : Set ℝ := Ioo (I.left : ℝ) (I.right : ℝ)

/-- The carrier is the real open interval between the endpoints. -/
theorem carrier_def (I : RatInterval) : I.carrier = Ioo (I.left : ℝ) (I.right : ℝ) :=
  rfl

/-- Euclidean length. -/
@[expose]
def length (I : RatInterval) : ℝ := (I.right : ℝ) - (I.left : ℝ)

/-- The length is the difference of the endpoints. -/
theorem length_def (I : RatInterval) : I.length = (I.right : ℝ) - (I.left : ℝ) :=
  rfl

/-- The length is positive. -/
theorem length_pos (I : RatInterval) : 0 < I.length := by
  simpa [length] using (Rat.cast_lt (K := ℝ)).2 I.left_lt_right

/-- The carrier is a nonempty open interval. -/
private theorem carrier_nonempty (I : RatInterval) : I.carrier.Nonempty :=
  nonempty_Ioo.2 (by exact_mod_cast I.left_lt_right)

/-- The rational-endpoint intervals are a countable family. -/
@[expose]
instance : Countable RatInterval :=
  Function.Injective.countable (f := fun I : RatInterval ↦ (I.left, I.right))
    (fun I J h ↦ by cases I; cases J; aesop)

/-- View a rational interval as an open interval. -/
@[expose]
def toOpen (I : RatInterval) : OpenInterval where
  left := I.left
  right := I.right
  left_lt_right := by exact_mod_cast I.left_lt_right

/-- The left endpoint of the underlying open interval. -/
theorem toOpen_left (I : RatInterval) : I.toOpen.left = I.left :=
  rfl

/-- The right endpoint of the underlying open interval. -/
theorem toOpen_right (I : RatInterval) : I.toOpen.right = I.right :=
  rfl

/-- The carrier agrees with the underlying open interval. -/
theorem carrier_toOpen (I : RatInterval) : I.toOpen.carrier = I.carrier := rfl

/-- Lengths agree after forgetting rationality of the endpoints. -/
theorem length_toOpen (I : RatInterval) : I.toOpen.length = I.length := rfl

end RatInterval

/-- Extended average over a rational-endpoint interval. -/
@[expose]
def ratIntervalAverage (g : ℝ → ℝ≥0∞) (I : RatInterval) : ℝ≥0∞ :=
  intervalAverage g I.toOpen

/-- The rational interval average is the average over the underlying open interval. -/
theorem ratIntervalAverage_def (g : ℝ → ℝ≥0∞) (I : RatInterval) :
    ratIntervalAverage g I = intervalAverage g I.toOpen :=
  rfl

/-- The real enlargement of a rational interval by the factor `τ` on each side. -/
private def ratEnlargement (τ : ℝ) (J : RatInterval) : Set ℝ :=
  Ioo ((J.left : ℝ) - τ * J.length) ((J.right : ℝ) + τ * J.length)

/-- Enlargement multiplies the length by `1 + 2τ`, as an identity of endpoints. -/
private theorem volume_ratEnlargement (τ : ℝ) (J : RatInterval) :
    volume (ratEnlargement τ J) = ENNReal.ofReal ((1 + 2 * τ) * J.length) := by
  have hdiff :
      ((J.right : ℝ) + τ * J.length) - ((J.left : ℝ) - τ * J.length) =
        (1 + 2 * τ) * J.length := by
    simp only [RatInterval.length]
    ring
  rw [ratEnlargement, Real.volume_Ioo, hdiff]

/-- An interval that meets a comparable selected interval sits inside its enlargement. -/
private theorem carrier_subset_ratEnlargement {τ : ℝ} {I J : RatInterval}
    (hcap : (I.carrier ∩ J.carrier).Nonempty) (hlen : I.length ≤ τ * J.length) :
    I.carrier ⊆ ratEnlargement τ J := by
  intro x hx
  rcases hcap with ⟨z, hzI, hzJ⟩
  have hx1 : (I.left : ℝ) < x := hx.1
  have hx2 : x < (I.right : ℝ) := hx.2
  have hzI1 : (I.left : ℝ) < z := hzI.1
  have hzI2 : z < (I.right : ℝ) := hzI.2
  have hzJ1 : (J.left : ℝ) < z := hzJ.1
  have hzJ2 : z < (J.right : ℝ) := hzJ.2
  have hLi : I.length = (I.right : ℝ) - (I.left : ℝ) := rfl
  have hLj : J.length = (J.right : ℝ) - (J.left : ℝ) := rfl
  refine ⟨?_, ?_⟩
  · have : (J.left : ℝ) - τ * J.length < x := by
      have hxz : z - I.length < x := by
        linarith
      have hz : (J.left : ℝ) - τ * J.length ≤ z - I.length := by
        linarith
      linarith
    exact this
  · have : x < (J.right : ℝ) + τ * J.length := by
      have hxz : x < z + I.length := by
        linarith
      have hz : z + I.length ≤ (J.right : ℝ) + τ * J.length := by
        linarith
      linarith
    exact this

/-- A strict interval average survives a small outward rational perturbation. No integrability
of `g` is assumed: if its integral over `I` is infinite, so is its average over any larger
interval. -/
theorem exists_ratInterval_of_average_gt (g : ℝ → ℝ≥0∞) (I : OpenInterval) {α : ℝ}
    (hα : 0 < α) (havg : ENNReal.ofReal α < intervalAverage g I) :
    ∃ J : RatInterval, I.carrier ⊆ J.carrier ∧ ENNReal.ofReal α < ratIntervalAverage g J := by
  by_cases hI0 : ∫⁻ t in I.carrier, g t = ∞
  · obtain ⟨p, _, hp2⟩ := exists_rat_btwn (show I.left - 1 < I.left by linarith)
    obtain ⟨q, hq1, _⟩ := exists_rat_btwn (show I.right < I.right + 1 by linarith)
    let J : RatInterval := ⟨p, q, by exact_mod_cast (hp2.trans I.left_lt_right).trans hq1⟩
    have hsub : I.carrier ⊆ J.carrier := fun t ht ↦ ⟨hp2.trans ht.1, ht.2.trans hq1⟩
    have hint : ∫⁻ t in J.carrier, g t = ∞ := top_unique (hI0 ▸ lintegral_mono_set hsub)
    refine ⟨J, hsub, ?_⟩
    rw [ratIntervalAverage, intervalAverage, RatInterval.carrier_toOpen, hint,
      ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]
    exact ENNReal.ofReal_lt_top
  have hL : 0 < I.length := I.length_pos
  have hmul : ENNReal.ofReal α * ENNReal.ofReal I.length < ∫⁻ t in I.carrier, g t := by
    refine (ENNReal.lt_div_iff_mul_lt ?_ ?_).1 havg
    · exact Or.inl (ne_of_gt (ENNReal.ofReal_pos.2 hL))
    · exact Or.inl ENNReal.ofReal_ne_top
  have hprod : ENNReal.ofReal (α * I.length) < ∫⁻ t in I.carrier, g t := by
    simpa [ENNReal.ofReal_mul hα.le] using hmul
  have hI0pos : 0 < ∫⁻ t in I.carrier, g t :=
    (ENNReal.ofReal_pos.2 (mul_pos hα hL)).trans hprod
  have hto : 0 < (∫⁻ t in I.carrier, g t).toReal :=
    ENNReal.toReal_pos hI0pos.ne' hI0
  have hroom : α * I.length < (∫⁻ t in I.carrier, g t).toReal := by
    rw [← ENNReal.ofReal_lt_ofReal_iff hto, ENNReal.ofReal_toReal hI0]
    exact hprod
  set room : ℝ := (∫⁻ t in I.carrier, g t).toReal - α * I.length
  have hroompos : 0 < room := sub_pos.2 hroom
  set δ : ℝ := room / (4 * α)
  have hδ : 0 < δ := div_pos hroompos (mul_pos (by norm_num : (0 : ℝ) < 4) hα)
  have hδavg : α * (I.length + 2 * δ) < (∫⁻ t in I.carrier, g t).toReal := by
    have hδeq : 2 * α * δ = room / 2 := by
      unfold δ
      field_simp [hα.ne']
      ring
    linarith [hδeq, hroompos]
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show I.left - δ < I.left by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show I.right < I.right + δ by linarith)
  have hpq : (p : ℝ) < (q : ℝ) := by linarith [I.left_lt_right]
  let J : RatInterval := ⟨p, q, by exact_mod_cast hpq⟩
  have hsub : I.carrier ⊆ J.carrier := by
    intro x hx
    exact ⟨lt_trans hp2 hx.1, lt_trans hx.2 hq1⟩
  have hlen : J.length < I.length + 2 * δ := by
    simp only [RatInterval.length, OpenInterval.length]
    linarith
  have hJpos : 0 < J.length := J.length_pos
  have hαlen : α * J.length < (∫⁻ t in I.carrier, g t).toReal := by
    nlinarith
  have hint : ∫⁻ t in I.carrier, g t ≤ ∫⁻ t in J.carrier, g t :=
    lintegral_mono_set hsub
  have hstrict : ENNReal.ofReal (α * J.length) < ∫⁻ t in J.carrier, g t := by
    refine lt_of_lt_of_le ?_ hint
    rw [← ENNReal.ofReal_toReal hI0]
    exact (ENNReal.ofReal_lt_ofReal_iff hto).2 hαlen
  have hdiv : ENNReal.ofReal α <
      (∫⁻ t in J.carrier, g t) / ENNReal.ofReal J.length := by
    refine (ENNReal.lt_div_iff_mul_lt ?_ ?_).2 ?_
    · exact Or.inl (ne_of_gt (ENNReal.ofReal_pos.2 hJpos))
    · exact Or.inl ENNReal.ofReal_ne_top
    simpa [ENNReal.ofReal_mul hα.le] using hstrict
  refine ⟨J, hsub, ?_⟩
  simpa [ratIntervalAverage, intervalAverage, RatInterval.carrier_toOpen,
    RatInterval.length_toOpen] using hdiv

/-- A rational interval on which the average exceeds `α` carries more than `α` times its
length. -/
private theorem mul_length_lt_of_lt_ratIntervalAverage {φ : ℝ → ℝ≥0∞} {α : ℝ}
    {I : RatInterval} (hI : ENNReal.ofReal α < ratIntervalAverage φ I) :
    ENNReal.ofReal α * ENNReal.ofReal I.length < ∫⁻ s in I.carrier, φ s :=
  (ENNReal.lt_div_iff_mul_lt (Or.inl (ENNReal.ofReal_pos.2 I.length_pos).ne')
    (Or.inl ENNReal.ofReal_ne_top)).1 hI

/-- A rational interval on which the average of an integrable `φ` exceeds `α > 0` has length at
most `‖φ‖₁ / α`. -/
private theorem length_le_of_lt_ratIntervalAverage {φ : ℝ → ℝ≥0∞} {α : ℝ} (hα : 0 < α)
    (hfin : ∫⁻ t, φ t ≠ ∞) {I : RatInterval} (hI : ENNReal.ofReal α < ratIntervalAverage φ I) :
    I.length ≤ (∫⁻ s, φ s).toReal / α := by
  have hlt : ENNReal.ofReal (α * I.length) < ∫⁻ s, φ s := by
    rw [ENNReal.ofReal_mul hα.le]
    exact (mul_length_lt_of_lt_ratIntervalAverage hI).trans_le (setLIntegral_le_lintegral _ _)
  rw [le_div_iff₀ hα, mul_comm]
  exact ((ENNReal.ofReal_lt_iff_lt_toReal (mul_pos hα I.length_pos).le hfin).1 hlt).le

/-- The uncentered maximal function on `ℝ` is weak type `(1, 1)` with constant `5`. -/
theorem intervalMaximalFunction_weakType (φ : ℝ → ℝ≥0∞) {α : ℝ} (hα : 0 < α) :
    volume {x | ENNReal.ofReal α < intervalMaximalFunction φ x} ≤
      ENNReal.ofReal 5 * (∫⁻ x, φ x) / ENNReal.ofReal α := by
  by_cases hfin : ∫⁻ t, φ t = ∞
  · rw [hfin, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by norm_num : (0 : ℝ) < 5)).ne',
      ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]
    exact le_top
  let t : Set RatInterval := {I | ENNReal.ofReal α < ratIntervalAverage φ I}
  have hcover_rat : {x | ENNReal.ofReal α < intervalMaximalFunction φ x} ⊆ ⋃ I ∈ t, I.carrier := by
    intro x hx
    obtain ⟨I, hxI, havg⟩ := lt_intervalMaximalFunction_iff.1 hx
    obtain ⟨J, hsub, hJ⟩ := exists_ratInterval_of_average_gt φ I hα havg
    exact mem_iUnion₂.2 ⟨J, hJ, hsub hxI⟩
  obtain ⟨u, hut, hdisj, hsel⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun I : RatInterval ↦ I.carrier) t (fun I ↦ I.length) 2
      (by norm_num) (fun I _ ↦ I.length_pos.le) _
      (fun I hI ↦ length_le_of_lt_ratIntervalAverage hα hfin hI)
      (fun I _ ↦ I.carrier_nonempty)
  have hcount : u.Countable :=
    hdisj.countable_of_nonempty_interior fun I _ ↦ by
      rw [RatInterval.carrier_def, isOpen_Ioo.interior_eq]
      exact I.carrier_nonempty
  have hsub_enl : ⋃ I ∈ t, I.carrier ⊆ ⋃ J ∈ u, ratEnlargement 2 J := by
    intro x hx
    obtain ⟨I, hIt, hxI⟩ := mem_iUnion₂.1 hx
    obtain ⟨J, hJu, hcap, hlen⟩ := hsel I hIt
    exact mem_iUnion₂.2 ⟨J, hJu, carrier_subset_ratEnlargement hcap hlen hxI⟩
  have hvol : volume {x | ENNReal.ofReal α < intervalMaximalFunction φ x} ≤
      ∑' J : u, ENNReal.ofReal 5 * ENNReal.ofReal (J : RatInterval).length := by
    refine le_trans (measure_mono (hcover_rat.trans hsub_enl)) ?_
    rw [Set.biUnion_eq_iUnion]
    refine (measure_iUnion_le _).trans_eq (tsum_congr fun J ↦ ?_)
    rw [volume_ratEnlargement, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hsum_int : ∑' J : u, ∫⁻ s in (J : RatInterval).carrier, φ s ≤ ∫⁻ s, φ s := by
    have hm : ∀ I ∈ u, MeasurableSet I.carrier := fun _ _ ↦ measurableSet_Ioo
    rw [← lintegral_biUnion hcount hm hdisj φ]
    exact setLIntegral_le_lintegral _ _
  have hsum_len : ∑' J : u, ENNReal.ofReal (J : RatInterval).length ≤
      (∫⁻ s, φ s) / ENNReal.ofReal α := by
    refine (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hα).ne')
      (Or.inl ENNReal.ofReal_ne_top)).2 ?_
    rw [mul_comm, ← ENNReal.tsum_mul_left]
    exact (tsum_le_tsum fun J ↦
      (mul_length_lt_of_lt_ratIntervalAverage (hut J.2)).le).trans hsum_int
  calc
    _ ≤ ∑' J : u, ENNReal.ofReal 5 * ENNReal.ofReal (J : RatInterval).length := hvol
    _ ≤ ENNReal.ofReal 5 * ((∫⁻ s, φ s) / ENNReal.ofReal α) := by
      rw [ENNReal.tsum_mul_left]
      gcongr
    _ = (ENNReal.ofReal 5 * ∫⁻ x, φ x) / ENNReal.ofReal α := by
      simp only [div_eq_mul_inv, mul_assoc]

/-- The real uncentered maximal function is weak type `(1, 1)` with constant `5`. -/
private theorem oneDimMaximal_weakType (g : ℝ → ℝ) {α : ℝ} (hα : 0 < α) :
    volume {x | ENNReal.ofReal α < oneDimMaximal g x} ≤
      ENNReal.ofReal 5 * ∫⁻ x, ENNReal.ofReal (|g x| / α) := by
  have hmul := lintegral_const_mul' (μ := (volume : Measure ℝ)) (ENNReal.ofReal α)⁻¹
    (fun s ↦ ENNReal.ofReal |g s|)
    (ENNReal.inv_ne_top.2 (ne_of_gt (ENNReal.ofReal_pos.2 hα)))
  have hscale : (∫⁻ s, ENNReal.ofReal |g s|) / ENNReal.ofReal α =
      ∫⁻ s, ENNReal.ofReal (|g s| / α) := by
    calc
      (∫⁻ s, ENNReal.ofReal |g s|) / ENNReal.ofReal α =
          (∫⁻ s, ENNReal.ofReal |g s|) * (ENNReal.ofReal α)⁻¹ := by
        rw [div_eq_mul_inv]
      _ = (ENNReal.ofReal α)⁻¹ * ∫⁻ s, ENNReal.ofReal |g s| := by
        rw [mul_comm]
      _ = ∫⁻ s, (ENNReal.ofReal α)⁻¹ * ENNReal.ofReal |g s| := hmul.symm
      _ = ∫⁻ s, ENNReal.ofReal (|g s| / α) := by
        refine lintegral_congr fun s ↦ ?_
        rw [ENNReal.ofReal_div_of_pos hα, div_eq_mul_inv, mul_comm]
  have hEN := intervalMaximalFunction_weakType (fun t ↦ ENNReal.ofReal |g t|) hα
  have hRHS :
      (ENNReal.ofReal 5 * ∫⁻ t, ENNReal.ofReal |g t|) / ENNReal.ofReal α =
        ENNReal.ofReal 5 * ∫⁻ x, ENNReal.ofReal (|g x| / α) := by
    calc
      (ENNReal.ofReal 5 * ∫⁻ t, ENNReal.ofReal |g t|) / ENNReal.ofReal α =
          ENNReal.ofReal 5 *
            ((∫⁻ t, ENNReal.ofReal |g t|) / ENNReal.ofReal α) := by
        simp only [div_eq_mul_inv, mul_assoc]
      _ = ENNReal.ofReal 5 * ∫⁻ x, ENNReal.ofReal (|g x| / α) := by
        rw [hscale]
  rw [hRHS] at hEN
  exact hEN

/-- In dimension one the endpoint growth is the identity. -/
private theorem strongMaximalGrowth_one (u : ℝ) : strongMaximalGrowth 1 u = u := by
  simp [strongMaximalGrowth_def]

/-- The endpoint growth dominates the identity on the nonnegative reals. -/
theorem strongMaximalGrowth_ge_self {d : ℕ} {u : ℝ} (hu : 0 ≤ u) :
    u ≤ strongMaximalGrowth d u := by
  have hbase : (1 : ℝ) ≤ 1 + Real.posLog u := le_add_of_nonneg_right Real.posLog_nonneg
  exact le_mul_of_one_le_right hu (one_le_pow₀ hbase)

/-- The carrier of a rectangle is the product of its open sides. -/
theorem OpenRectangle.carrier_eq_pi {d : ℕ} (R : OpenRectangle d) :
    R.carrier = pi univ fun j ↦ Ioo (R.lower j) (R.upper j) := by
  ext x
  simp [OpenRectangle.carrier, mem_Ioo]

/-- The carrier of a rectangle is the open interior `BoxIntegral.Box.Ioo` of the box. -/
theorem OpenRectangle.carrier_eq_Ioo {d : ℕ} (R : OpenRectangle d) :
    R.carrier = BoxIntegral.Box.Ioo R :=
  R.carrier_eq_pi

/-- The volume of a rectangle is the product of its side lengths. -/
theorem OpenRectangle.volume_carrier {d : ℕ} (R : OpenRectangle d) :
    volume R.carrier = ∏ j, ENNReal.ofReal (R.upper j - R.lower j) := by
  rw [R.carrier_eq_pi, Real.volume_pi_Ioo]

/-- On `Fin 1` the strong maximal function is the uncentered maximal function of the line. -/
private theorem strongMaximalFunction_finOne (f : (Fin 1 → ℝ) → ℝ) (x : Fin 1 → ℝ) :
    strongMaximalFunction f x = oneDimMaximal (fun t ↦ f fun _ : Fin 1 ↦ t) (x 0) := by
  let g : ℝ → ℝ := fun t ↦ f fun _ : Fin 1 ↦ t
  let e := MeasurableEquiv.funUnique (Fin 1) ℝ
  have hev : MeasurePreserving e volume volume := volume_preserving_funUnique (Fin 1) ℝ
  have he0 : ∀ y : Fin 1 → ℝ, e y = y 0 := fun _ ↦ rfl
  have hconst : ∀ y : Fin 1 → ℝ, f y = g (y 0) := by
    intro y
    have hy : y = fun _ : Fin 1 ↦ y 0 := by
      ext i
      fin_cases i
      rfl
    rw [hy]
  have hcarrier : ∀ R : OpenRectangle 1,
      R.carrier = e ⁻¹' Ioo (R.lower 0) (R.upper 0) := by
    intro R
    ext y
    simp only [OpenRectangle.carrier, mem_preimage, mem_Ioo, he0]
    constructor
    · intro hy
      exact hy 0
    · intro hy j
      fin_cases j
      exact hy
  have hvol : ∀ R : OpenRectangle 1,
      volume R.carrier = ENNReal.ofReal (R.upper 0 - R.lower 0) := by
    intro R
    rw [hcarrier R, hev.measure_preimage_equiv, Real.volume_Ioo]
  have hint : ∀ R : OpenRectangle 1,
      (∫⁻ y in R.carrier, ENNReal.ofReal |f y|) =
        ∫⁻ t in Ioo (R.lower 0) (R.upper 0), ENNReal.ofReal |g t| := by
    intro R
    let s : Set ℝ := Ioo (R.lower 0) (R.upper 0)
    have hs : MeasurableSet s := measurableSet_Ioo
    have hspre : MeasurableSet (e ⁻¹' s) := hs.preimage e.measurable
    simp_rw [show ∀ y, ENNReal.ofReal |f y| = ENNReal.ofReal |g (e y)| by
      intro y; rw [hconst y, he0 y], hcarrier R]
    rw [← lintegral_indicator hspre]
    have hcomp := hev.lintegral_comp_emb e.measurableEmbedding
      (s.indicator fun t ↦ ENNReal.ofReal |g t|)
    rw [lintegral_indicator hs] at hcomp
    rw [← hcomp]
    congr 1
  apply le_antisymm
  · refine iSup_le fun R ↦ iSup_le fun hxR ↦ ?_
    let I : OpenInterval := ⟨R.lower 0, R.upper 0, R.lower_lt_upper 0⟩
    have hxI : x 0 ∈ I.carrier := by
      rw [OpenInterval.carrier, mem_Ioo]
      exact hxR 0
    have havg : (∫⁻ y in R.carrier, ENNReal.ofReal |f y|) / volume R.carrier =
        intervalAverage (fun t ↦ ENNReal.ofReal |g t|) I := by
      simp only [intervalAverage, OpenInterval.carrier, OpenInterval.length]
      rw [hint R, hvol R]
    rw [havg]
    exact (le_iSup (fun h : x 0 ∈ I.carrier ↦
      intervalAverage (fun t ↦ ENNReal.ofReal |g t|) I) hxI).trans
      (le_iSup (fun J : OpenInterval ↦ ⨆ h : x 0 ∈ J.carrier,
        intervalAverage (fun t ↦ ENNReal.ofReal |g t|) J) I)
  · refine iSup_le fun I ↦ iSup_le fun hxI ↦ ?_
    let R : OpenRectangle 1 := ⟨fun _ ↦ I.left, fun _ ↦ I.right, fun _ ↦ I.left_lt_right⟩
    have hxR : x ∈ R.carrier := by
      intro j
      fin_cases j
      rw [OpenInterval.carrier, mem_Ioo] at hxI
      exact hxI
    have havg : intervalAverage (fun t ↦ ENNReal.ofReal |g t|) I =
        (∫⁻ y in R.carrier, ENNReal.ofReal |f y|) / volume R.carrier := by
      simp only [intervalAverage, OpenInterval.carrier, OpenInterval.length]
      rw [hint R, hvol R]
    rw [havg]
    exact (le_iSup (fun h : x ∈ R.carrier ↦
      (∫⁻ y in R.carrier, ENNReal.ofReal |f y|) / volume R.carrier) hxR).trans
      (le_iSup (fun S : OpenRectangle 1 ↦ ⨆ h : x ∈ S.carrier,
        (∫⁻ y in S.carrier, ENNReal.ofReal |f y|) / volume S.carrier) R)

/-- The strong maximal operator on a line is weak type `(1, 1)`. -/
theorem strongMaximal_weakType_one (f : (Fin 1 → ℝ) → ℝ) {a : ℝ} (ha : 0 < a) :
    volume {x | ENNReal.ofReal a < strongMaximalFunction f x} ≤
      ENNReal.ofReal 5 *
        ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth 1 (|f x| / a)) := by
  let g : ℝ → ℝ := fun t ↦ f fun _ : Fin 1 ↦ t
  let e := MeasurableEquiv.funUnique (Fin 1) ℝ
  have hev : MeasurePreserving e volume volume := volume_preserving_funUnique (Fin 1) ℝ
  have he0 : ∀ y : Fin 1 → ℝ, e y = y 0 := fun _ ↦ rfl
  have hset : {x | ENNReal.ofReal a < strongMaximalFunction f x} =
      e ⁻¹' {t | ENNReal.ofReal a < oneDimMaximal g t} := by
    ext x
    simp [strongMaximalFunction_finOne, he0, g]
  have hint : ∫⁻ x, ENNReal.ofReal (|f x| / a) = ∫⁻ t, ENNReal.ofReal (|g t| / a) := by
    have hpt : ∀ x, ENNReal.ofReal (|f x| / a) = ENNReal.ofReal (|g (e x)| / a) := by
      intro x
      have hx : f x = g (x 0) := by
        have : x = fun _ : Fin 1 ↦ x 0 := by
          ext i
          fin_cases i
          rfl
        rw [this]
      rw [hx, he0 x]
    simp_rw [hpt]
    exact hev.lintegral_comp_emb e.measurableEmbedding fun t ↦ ENNReal.ofReal (|g t| / a)
  rw [hset, hev.measure_preimage_equiv]
  simp_rw [strongMaximalGrowth_one]
  rw [hint]
  exact oneDimMaximal_weakType g ha

/-- The coefficient produced by comparing `log(4u)` with `(1 + log 4)(1 + log⁺ u)`. -/
@[expose]
def strongMaximalIterationFactor (n : ℕ) : ℝ := 2 * (1 + Real.log 4) ^ n

/-- Unfolding of `CKMA.strongMaximalIterationFactor`. -/
theorem strongMaximalIterationFactor_def (n : ℕ) :
    strongMaximalIterationFactor n = 2 * (1 + Real.log 4) ^ n :=
  rfl

/-- The iteration factor is positive. -/
theorem strongMaximalIterationFactor_pos (n : ℕ) : 0 < strongMaximalIterationFactor n := by
  unfold strongMaximalIterationFactor
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  positivity

/-- On `[1/2, 2u]` the logarithmic kernel integral is at most `(1 + log (4u))^k · 2 log (4u)`. -/
private theorem integral_bracket_le {k : ℕ} {u : ℝ} (hu : 1 / 4 < u) :
    ∫ s in (1 / 2 : ℝ)..(2 * u), (2 / s) * (1 + Real.posLog (2 * u / s)) ^ k ≤
      (1 + Real.log (4 * u)) ^ k * (2 * Real.log (4 * u)) := by
  have hle : (1 / 2 : ℝ) ≤ 2 * u := by linarith
  have hlog4u : 0 ≤ Real.log (4 * u) := Real.log_nonneg (by linarith)
  have hpos : ∀ s ∈ Icc (1 / 2 : ℝ) (2 * u), 0 < s := fun s hs ↦ by linarith [hs.1]
  have hcont : ContinuousOn (fun s : ℝ ↦ 2 / s) (Icc (1 / 2) (2 * u)) :=
    continuousOn_const.div continuousOn_id fun s hs ↦ (hpos s hs).ne'
  have hint_left : IntervalIntegrable
      (fun s ↦ (2 / s) * (1 + Real.posLog (2 * u / s)) ^ k) volume (1 / 2) (2 * u) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hle]
    have hdivc : ContinuousOn (fun s : ℝ ↦ 2 * u / s) (Icc (1 / 2) (2 * u)) :=
      continuousOn_const.div continuousOn_id fun s hs ↦ (hpos s hs).ne'
    exact hcont.mul ((continuousOn_const.add
      (Real.continuous_posLog.comp_continuousOn hdivc)).pow k)
  have hint_right : IntervalIntegrable (fun s ↦ (1 + Real.log (4 * u)) ^ k * (2 / s))
      volume (1 / 2) (2 * u) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hle]
    exact continuousOn_const.mul hcont
  have hinv : (∫ s in (1 / 2 : ℝ)..(2 * u), 2 / s) = 2 * Real.log (4 * u) := by
    have hdiv : (∫ s in (1 / 2 : ℝ)..(2 * u), 2 / s) =
        2 * ∫ s in (1 / 2 : ℝ)..(2 * u), s⁻¹ := by
      simp_rw [div_eq_mul_inv]
      exact intervalIntegral.integral_const_mul (2 : ℝ) (fun s ↦ s⁻¹)
    rw [hdiv, integral_inv_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
      (by linarith : 0 < 2 * u), show (2 * u) / (1 / 2 : ℝ) = 4 * u by ring]
  calc
    _ ≤ ∫ s in (1 / 2 : ℝ)..(2 * u), (1 + Real.log (4 * u)) ^ k * (2 / s) := by
      refine intervalIntegral.integral_mono_on hle hint_left hint_right fun s hs ↦ ?_
      have hs0 := hpos s hs
      have hmax : Real.posLog (2 * u / s) ≤ Real.log (4 * u) := by
        rw [Real.posLog_apply]
        exact max_le hlog4u (Real.log_le_log (div_pos (by linarith) hs0)
          (by rw [div_le_iff₀ hs0]; nlinarith [hs.1]))
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀
        (add_nonneg zero_le_one Real.posLog_nonneg) (by linarith) k) (by positivity)
    _ = (1 + Real.log (4 * u)) ^ k * (2 * Real.log (4 * u)) := by
      rw [intervalIntegral.integral_const_mul, hinv]

/-- For `u > 0`, `1 + log (4u) ≤ (1 + log 4)(1 + log⁺ u)`. -/
private theorem one_add_log_four_mul_le {u : ℝ} (hu : 0 < u) :
    1 + Real.log (4 * u) ≤ (1 + Real.log 4) * (1 + Real.posLog u) := by
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  rw [Real.log_mul (by norm_num) hu.ne']
  have hle : Real.log u ≤ Real.posLog u := by
    rw [Real.posLog_apply]
    exact le_max_right _ _
  nlinarith [Real.posLog_nonneg (x := u)]

/-- A layer-cake bracket of order `k` is bounded by the next power of `1 + log⁺`. -/
private theorem strongMaximalGrowth_bracket {k : ℕ} {u : ℝ} (hu : 0 ≤ u) :
    (1 + Real.posLog (2 * u)) ^ k +
      (if 2 * u ≤ (1 / 2 : ℝ) then (0 : ℝ) else
        ∫ s in (1 / 2 : ℝ)..(2 * u), (2 / s) *
          (1 + Real.posLog (2 * u / s)) ^ k) ≤
      strongMaximalIterationFactor (k + 1) * (1 + Real.posLog u) ^ (k + 1) := by
  have hfactor : (1 : ℝ) ≤ 1 + Real.log 4 := by
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 4)]
  have hlogu : (1 : ℝ) ≤ 1 + Real.posLog u := le_add_of_nonneg_right Real.posLog_nonneg
  rw [strongMaximalIterationFactor_def]
  split_ifs with hsmall
  · have hlog : Real.posLog (2 * u) = 0 :=
      (Real.posLog_eq_zero_iff _).2 (by rw [abs_of_nonneg (by positivity)]; linarith)
    rw [hlog, add_zero, add_zero, one_pow]
    have h1 := one_le_pow₀ (n := k + 1) hfactor
    have h2 := one_le_pow₀ (n := k + 1) hlogu
    nlinarith
  · have hu4 : 1 / 4 < u := by linarith [not_le.1 hsmall]
    have hu0 : 0 < u := by linarith
    set L := Real.log (4 * u)
    have hL : 0 ≤ L := Real.log_nonneg (by linarith)
    have hfirst : (1 + Real.posLog (2 * u)) ^ k ≤ (1 + L) ^ k :=
      pow_le_pow_left₀ (add_nonneg zero_le_one Real.posLog_nonneg) (by
        linarith [(Real.posLog_le_posLog (by linarith) (by linarith : 2 * u ≤ 4 * u)).trans
          (Real.posLog_eq_log (by rw [abs_of_pos (by linarith)]; linarith)).le]) k
    have hpowk : 0 ≤ (1 + L) ^ k := by positivity
    calc
      _ ≤ (1 + L) ^ k + (1 + L) ^ k * (2 * L) := add_le_add hfirst (integral_bracket_le hu4)
      _ ≤ 2 * (1 + L) ^ (k + 1) := by rw [pow_succ]; nlinarith
      _ ≤ 2 * ((1 + Real.log 4) * (1 + Real.posLog u)) ^ (k + 1) := by
        gcongr
        exact one_add_log_four_mul_le hu0
      _ = 2 * (1 + Real.log 4) ^ (k + 1) * (1 + Real.posLog u) ^ (k + 1) := by
        rw [mul_pow]; ring

/-- Half a scaled growth plus its logarithmic integral is at most
`strongMaximalIterationFactor n` times the next Orlicz growth. -/
theorem strongMaximalGrowth_scaled_kernel {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 ≤ u) :
    (1 / 2) * strongMaximalGrowth n (2 * u) +
      (if u ≤ (1 / 4 : ℝ) then (0 : ℝ) else
        ∫ s in (1 / 2 : ℝ)..(2 * u), strongMaximalGrowth n (2 * u / s)) ≤
      strongMaximalIterationFactor n * strongMaximalGrowth (n + 1) u := by
  have hk : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hbracket := strongMaximalGrowth_bracket (k := n - 1) hu
  simp only [strongMaximalGrowth_def, hk, Nat.add_sub_cancel] at hbracket ⊢
  by_cases hsmall : u ≤ (1 / 4 : ℝ)
  · have h2 : 2 * u ≤ (1 / 2 : ℝ) := by linarith
    simp only [hsmall, h2, ite_true, add_zero] at hbracket ⊢
    have hlog : Real.posLog (2 * u) = 0 :=
      (Real.posLog_eq_zero_iff _).2 (by rw [abs_of_nonneg (by positivity)]; linarith)
    simp only [hlog, add_zero, one_pow, mul_one] at hbracket ⊢
    have hmul := mul_le_mul_of_nonneg_left hbracket hu
    have hhalf : (1 / 2) * (2 * u) = u := by ring
    rw [hhalf]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  · have h2 : ¬ 2 * u ≤ (1 / 2 : ℝ) := by
      intro h
      exact hsmall (by linarith)
    simp only [hsmall, h2, ite_false] at hbracket ⊢
    have hu0 : 0 < u := lt_of_not_ge (by
      intro hu0
      exact hsmall (le_trans hu0 (by norm_num)))
    have hpull : (∫ s in (1 / 2 : ℝ)..(2 * u),
        (2 * u / s) * (1 + Real.posLog (2 * u / s)) ^ (n - 1)) =
        u * ∫ s in (1 / 2 : ℝ)..(2 * u),
          (2 / s) * (1 + Real.posLog (2 * u / s)) ^ (n - 1) := by
      have hfun : ∀ s, (2 * u / s) * (1 + Real.posLog (2 * u / s)) ^ (n - 1) =
          u * ((2 / s) * (1 + Real.posLog (2 * u / s)) ^ (n - 1)) := by
        intro s
        ring
      simp_rw [hfun]
      exact intervalIntegral.integral_const_mul u
        (fun s ↦ (2 / s) * (1 + Real.posLog (2 * u / s)) ^ (n - 1))
    have hhalf : (1 / 2) * ((2 * u) * (1 + Real.posLog (2 * u)) ^ (n - 1)) =
        u * (1 + Real.posLog (2 * u)) ^ (n - 1) := by ring
    rw [hhalf, hpull]
    calc
      u * (1 + Real.posLog (2 * u)) ^ (n - 1) +
          u * ∫ s in (1 / 2 : ℝ)..(2 * u),
            (2 / s) * (1 + Real.posLog (2 * u / s)) ^ (n - 1) =
          u * ((1 + Real.posLog (2 * u)) ^ (n - 1) +
            ∫ s in (1 / 2 : ℝ)..(2 * u),
              (2 / s) * (1 + Real.posLog (2 * u / s)) ^ (n - 1)) := by ring
      _ ≤ u * (strongMaximalIterationFactor n *
          (1 + Real.posLog u) ^ n) := by
        exact mul_le_mul_of_nonneg_left hbracket hu
      _ = strongMaximalIterationFactor n *
          (u * (1 + Real.posLog u) ^ n) := by ring

end CKMA
