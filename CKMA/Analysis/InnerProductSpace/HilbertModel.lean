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
-/

@[expose] public section

namespace CKMA

universe u

/-- A Hilbert-space carrier over real or complex scalars, with its compatible norm and completeness.
  -/
structure HilbertSpaceModel (𝕜 : Type*) [RCLike 𝕜] where
  /-- Underlying carrier. -/
  Carrier : Type u
  /-- Normed additive structure. -/
  [normedAddCommGroup : NormedAddCommGroup Carrier]
  /-- Inner product inducing that norm. -/
  [innerProductSpace : InnerProductSpace 𝕜 Carrier]
  /-- Hilbert completeness. -/
  [completeSpace : CompleteSpace Carrier]

attribute [instance] HilbertSpaceModel.normedAddCommGroup HilbertSpaceModel.innerProductSpace
  HilbertSpaceModel.completeSpace

end CKMA
