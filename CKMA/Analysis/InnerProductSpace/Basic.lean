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

This module re-exports `CKMA.Analysis.InnerProductSpace.HilbertModel`,
`CKMA.Analysis.InnerProductSpace.Frame`, and `CKMA.Analysis.InnerProductSpace.L2FunctionFamilies`:
bundled Hilbert spaces such as `CKMA.HilbertSpaceModel`, the frame predicates
`CKMA.IsBesselSequence` and `CKMA.IsFrame`, and `L²` family predicates such as
`CKMA.IsL2RieszBasis`, used across analysis sections. It introduces no declarations of its own.
-/
