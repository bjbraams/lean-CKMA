/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Strong maximal averages and rectangular differentiation

Axis-parallel rectangles with positive side lengths, their signed averages and the
positive strong maximal operator. Shrinking rectangles have unrestricted eccentricity.
The endpoint estimate uses `u(1+log⁺u)^(d-1)`; this local integrability class is differentiated
almost everywhere, whereas L¹ alone is insufficient in dimension at least two.
Measures, real logarithms and extended integrals use Mathlib. Source: GAPS 05.31.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory
open scoped BigOperators ENNReal

/-- A bounded open axis-parallel box with positive side lengths. -/
structure OpenRectangle (d : ℕ) where
  /-- Lower coordinates. -/
  lower : Fin d → ℝ
  /-- Upper coordinates. -/
  upper : Fin d → ℝ
  /-- Every side has positive length. -/
  lower_lt_upper : ∀ j, lower j < upper j

/-- The underlying open set of a rectangle. -/
def OpenRectangle.carrier {d : ℕ} (R : OpenRectangle d) : Set (Fin d → ℝ) :=
  {x | ∀ j, R.lower j < x j ∧ x j < R.upper j}

/-- Sum of side lengths, an equivalent fixed-dimensional measure of shrinking rectangles. -/
def OpenRectangle.totalWidth {d : ℕ} (R : OpenRectangle d) : ℝ :=
  ∑ j, (R.upper j - R.lower j)

/-- Signed average on a rectangle; used when local integrability is assumed. -/
def OpenRectangle.average {d : ℕ} (R : OpenRectangle d) (f : (Fin d → ℝ) → ℝ) : ℝ :=
  (volume R.carrier).toReal⁻¹ * ∫ y in R.carrier, f y

/-- The positive strong maximal operator, retaining infinite local integrals. -/
def strongMaximalFunction {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ≥0∞ :=
  ⨆ (R : OpenRectangle d) (_hx : x ∈ R.carrier),
    (∫⁻ y in R.carrier, ENNReal.ofReal |f y|) / volume R.carrier

/-- The endpoint Orlicz growth `u(1+log⁺u)^(d-1)` for nonnegative `u`. -/
def strongMaximalGrowth (d : ℕ) (u : ℝ) : ℝ :=
  u * (1 + max 0 (Real.log u)) ^ (d - 1)

/-- Local endpoint integrability, expressed on all compact subsets. -/
def IsLocallyLLog (d : ℕ) (f : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ K : Set (Fin d → ℝ), IsCompact K →
    IntegrableOn (fun x ↦ strongMaximalGrowth d |f x|) K

/-- All rectangles containing the point, with unrestricted eccentricity, recover its value. -/
def RectanglesDifferentiateAt {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ R : OpenRectangle d,
    x ∈ R.carrier → R.totalWidth < δ → |R.average f - f x| < ε

/-- **05.31**: the endpoint strong maximal bound. -/
theorem strongMaximal_endpoint {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : (Fin d → ℝ) → ℝ), Measurable f →
      ∀ a : ℝ, 0 < a → volume {x | ENNReal.ofReal a < strongMaximalFunction f x} ≤
        ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth d (|f x| / a)) := by
  sorry

/-- Rectangles differentiate the local `L(log⁺L)^(d-1)` class. -/
theorem ae_rectanglesDifferentiateAt {d : ℕ} (hd : 2 ≤ d)
    {f : (Fin d → ℝ) → ℝ} (hm : Measurable f) (hf : IsLocallyLLog d f) :
    ∀ᵐ x ∂volume, RectanglesDifferentiateAt f x := by
  sorry

/-- In dimension at least two the same basis does not differentiate all of `L¹`. -/
theorem exists_integrable_not_rectangularlyDifferentiable {d : ℕ} (hd : 2 ≤ d) :
    ∃ f : (Fin d → ℝ) → ℝ, Measurable f ∧ Integrable f volume ∧
      0 < volume {x | ¬ RectanglesDifferentiateAt f x} := by
  sorry

end CKMA
