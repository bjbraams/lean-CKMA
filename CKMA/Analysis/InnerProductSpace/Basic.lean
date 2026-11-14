/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.InnerProductSpace.HilbertModel
public import CKMA.Analysis.InnerProductSpace.Frame
public import CKMA.Analysis.InnerProductSpace.L2FunctionFamilies

/-!
# Basic definitions for inner product and Hilbert spaces

This module re-exports the foundational Hilbert-space carrier models, abstract Bessel/frame
interfaces, and `L²` function family predicates used across analysis sections.

## Main definitions

* `CKMA.HilbertSpaceModel`, `CKMA.RealHilbertModel`, `CKMA.ComplexHilbertSpace`: bundled
  Hilbert spaces over `RCLike` scalars.
* `CKMA.IsBesselSequence`, `CKMA.IsFrame`, `CKMA.IsFrameWithBounds`: abstract Hilbert-space
  frame predicates.
* `CKMA.IsL2RieszSequence`, `CKMA.IsL2RieszBasis`, `CKMA.IsL2FrameFamily`: `L²` function
  family predicates.

## Main results

* Re-exports the basic frame and `L²` family equivalence lemmas from `Frame` and
  `L2FunctionFamilies`.

## Notation

Uses the standard Mathlib inner-product and `Lp` notations.
-/
