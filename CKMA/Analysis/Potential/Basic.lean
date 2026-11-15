/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Potential.Cutoff

/-!
# Basic potential-theory cutoff predicates

This module re-exports smooth compactly supported cutoff predicates used in potential theory
and Sobolev capacity estimates.

## Main definitions

* `CKMA.IsSmoothCompactCutoffFor`: predicate for smooth compactly supported test functions
  dominating the indicator of a set.

## Main results

* Re-exports the cutoff API from `CKMA.Analysis.Potential.Cutoff`.
-/
