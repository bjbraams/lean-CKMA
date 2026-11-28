/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Wiener's Tauberian theorem on the real line

For `f ∈ L¹(ℝ)` the closed linear span of the translates of `f` is all of `L¹(ℝ)` if and only if
the Fourier transform of `f` vanishes nowhere. Translation acts on `L¹` equivalence classes
through Mathlib's measure-preserving composition map.
Source: GAPS 20.41.

## Main definitions

* `CKMA.lpTranslate`: translation of an `L¹(ℝ)` equivalence class.

## Main results

* `CKMA.coeFn_lpTranslate`: `lpTranslate f t` is a.e. `x ↦ f (x + t)`.
* `CKMA.wiener_tauberian_real`: Wiener's Tauberian theorem on `L¹(ℝ)`.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory FourierTransform
open scoped FourierTransform


/-- Translation `x ↦ f (x + t)` of an `L¹` equivalence class on the real line, through the
measure-preserving composition map `Lp.compMeasurePreserving`. -/
@[expose]
def lpTranslate (f : Lp ℂ 1 (volume : Measure ℝ)) (t : ℝ) : Lp ℂ 1 (volume : Measure ℝ) :=
  Lp.compMeasurePreserving (E := ℂ) (p := 1) (fun x : ℝ ↦ x + t)
    (measurePreserving_add_right (volume : Measure ℝ) t) f

/-- `lpTranslate f t` is almost everywhere the function `x ↦ f (x + t)`. -/
theorem coeFn_lpTranslate (f : Lp ℂ 1 (volume : Measure ℝ)) (t : ℝ) :
    lpTranslate f t =ᵐ[volume] fun x ↦ f (x + t) :=
  Lp.coeFn_compMeasurePreserving _ _

/-- **20.41**, Wiener Tauberian density on the real line. The Fourier transform is the L1
integral of an a.e. representative; the translation span is a closed submodule of L1. -/
theorem wiener_tauberian_real (f : Lp ℂ 1 (volume : Measure ℝ)) :
    (∀ ξ : ℝ, 𝓕 (fun x : ℝ ↦ f x) ξ ≠ 0) ↔
      (Submodule.span ℂ (Set.range (lpTranslate f))).topologicalClosure = ⊤ := by
  sorry


end CKMA
