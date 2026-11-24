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
`W^{1,d}` function. Real comparison bounds, the regularized profile, and Euclidean
integrability are `CKMA.Analysis.Sobolev.Critical.Bounds`, `.Profile` and `.Integrability`.
Weak derivatives reuse TauCeti, and Lebesgue norms use Mathlib.
Source: GAPS 26.16.

## Main definitions

* `CKMA.criticalSobolevProfile`: `Real.log (Real.log (e / ‖x‖))`, equal to `0` at the origin
  and for `‖x‖ ≥ e` because `Real.log` of a nonpositive number is `0`.

## Main results

* `CKMA.exists_memSobolev_not_memLp_top`: failure of the critical Sobolev embedding
  `W^{1,d}(Ω) ↪ L^∞(Ω)` in dimensions `d ≥ 2` (**26.16**).
-/

public section

noncomputable section

namespace CKMA

/-- Radial profile `Real.log (Real.log (e / ‖x‖))`.
`Real.log` of a nonpositive number is `0`, so the value is `0` at the origin and for
`‖x‖ ≥ e`. A smooth cutoff is still needed for compactly supported Sobolev functions. -/
@[expose]
def criticalSobolevProfile {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.log (Real.log (Real.exp 1 / ‖x‖))

end CKMA
