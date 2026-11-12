/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Real.RectangularDifferentiation.CounterexampleSum
public import CKMA.Analysis.Real.RectangularDifferentiation.Differentiate

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

/-- **05.31**: the endpoint strong maximal bound. -/
theorem strongMaximal_endpoint {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : (Fin d → ℝ) → ℝ), Measurable f →
      ∀ a : ℝ, 0 < a → volume {x | ENNReal.ofReal a < strongMaximalFunction f x} ≤
        ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (strongMaximalGrowth d (|f x| / a)) := by
  exact strongMaximal_orlicz (show 1 ≤ d by omega)

/-- Rectangles differentiate the local `L(log⁺L)^(d-1)` class. -/
theorem ae_rectanglesDifferentiateAt {d : ℕ} (hd : 2 ≤ d)
    {f : (Fin d → ℝ) → ℝ} (hm : Measurable f) (hf : IsLocallyLLog d f) :
    ∀ᵐ x ∂volume, RectanglesDifferentiateAt f x := by
  exact ae_rectanglesDifferentiateAt_of_strongMaximal hd hm hf

/-- In dimension at least two the same basis does not differentiate all of `L¹`. -/
theorem exists_integrable_not_rectangularlyDifferentiable {d : ℕ} (hd : 2 ≤ d) :
    ∃ f : (Fin d → ℝ) → ℝ, Measurable f ∧ Integrable f volume ∧
      0 < volume {x | ¬ RectanglesDifferentiateAt f x} :=
  Bohr.exists_integrable_not_rectangularlyDifferentiable hd

end CKMA
