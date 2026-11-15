/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Bundled Hilbert spaces over real or complex scalars

The carrier universe is independent of the scalar universe. A single bundle records a normed
additive group, a compatible inner product, and completeness.

## Main definitions

* `CKMA.HilbertSpaceModel`: bundled Hilbert space over a scalar field `𝕜` satisfying `[RCLike 𝕜]`.
* `CKMA.RealHilbertSpace`: abbreviation for `HilbertSpaceModel ℝ`.
* `CKMA.ComplexHilbertSpace`: abbreviation for `HilbertSpaceModel ℂ`.

## Main results

* Typeclass instances exporting `NormedAddCommGroup`, `InnerProductSpace`, and `CompleteSpace`
  on `H.carrier`.
-/

@[expose] public section

namespace CKMA

universe u

/-- A Hilbert-space carrier over real or complex scalars, with its compatible norm and
completeness. -/
structure HilbertSpaceModel (𝕜 : Type*) [RCLike 𝕜] where
  /-- Underlying carrier. -/
  carrier : Type u
  /-- Normed additive structure. -/
  [normedAddCommGroup : NormedAddCommGroup carrier]
  /-- Inner product inducing that norm. -/
  [innerProductSpace : InnerProductSpace 𝕜 carrier]
  /-- Hilbert completeness. -/
  [completeSpace : CompleteSpace carrier]

attribute [instance] HilbertSpaceModel.normedAddCommGroup HilbertSpaceModel.innerProductSpace
  HilbertSpaceModel.completeSpace

/-- A real Hilbert-space model with an explicitly chosen carrier universe. -/
abbrev RealHilbertSpace := HilbertSpaceModel.{u} ℝ

@[deprecated (since := "2026-11-15")] alias RealHilbertModel := RealHilbertSpace

/-- A complex Hilbert-space model with an explicitly chosen carrier universe. -/
abbrev ComplexHilbertSpace := HilbertSpaceModel.{u} ℂ

end CKMA
