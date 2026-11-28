/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Sobolev.Critical.Bounds
public import CKMA.Analysis.Sobolev.Critical.Integrability
public import CKMA.Analysis.Sobolev.Critical.Profile

/-!
# Critical Sobolev functions that are essentially unbounded

In dimension at least two, every nonempty open set contains an essentially unbounded
`W^{1,d}` function. This module re-exports the three parts of the construction: real
comparison bounds for the double logarithm (`CKMA.Analysis.Sobolev.Critical.Bounds`), the
regularized cut-off profile (`.Profile`) and its Euclidean integrability (`.Integrability`).
Weak derivatives reuse TauCeti, and Lebesgue norms use Mathlib. Source: GAPS 26.16.

## Main results

* `CKMA.exists_memSobolev_not_memLp_top` (in `.Integrability`): failure of the critical
  Sobolev embedding `W^{1,d}(Ω) ↪ L^∞(Ω)` in dimensions `d ≥ 2` (**26.16**).
-/
