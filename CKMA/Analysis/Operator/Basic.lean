/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Operator.TraceIdeals

/-!
# Basic operator-ideal interfaces

This module re-exports the foundational Schatten, Hilbert–Schmidt, and trace-class operator
definitions and basic API for use across sections.

## Main definitions

* `CKMA.schattenGauge`, `CKMA.IsSchattenClass`: Schatten-class singular-value gauge and
  membership predicate.
* `CKMA.IsTraceClassOperator`, `CKMA.hilbertTrace`: trace-class predicate and Hilbert trace.

## Main results

* Re-exports the trace-ideal API from `CKMA.Analysis.Operator.TraceIdeals`.

## Notation

No new notation is introduced in this module.
-/
