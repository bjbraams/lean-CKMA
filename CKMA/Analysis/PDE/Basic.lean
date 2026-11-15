/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.PDE.Euclidean

/-!
# Basic Euclidean PDE definitions

This module re-exports the foundational Euclidean coordinate-space abbreviations, weak
derivative predicates, and differential operator conventions used across PDE, Sobolev, and
microlocal analysis.

## Main definitions

* `CKMA.EuclideanRealSpace`: abbreviation for `EuclideanSpace ℝ (Fin d)`.
* `CKMA.HasWeakFirstOrderPartials`, `CKMA.HasWeakGradient`: weak derivative predicates.
* `CKMA.IsUniformlyEllipticOn`, `CKMA.IsWeakSolutionElliptic`: elliptic PDE predicates.

## Main results

* Re-exports the foundational Euclidean PDE definitions from `CKMA.Analysis.PDE.Euclidean`.
-/
