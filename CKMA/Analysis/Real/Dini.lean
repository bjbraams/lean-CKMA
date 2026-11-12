/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Real.Dini.Basic
public import CKMA.Analysis.Real.Dini.Assembly

/-!
# Dini derivatives and Denjoy–Young–Saks alternatives

The four one-sided upper and lower Dini derivatives take values in the extended real
line. Both left derivatives use the quotient `(f(x+h)-f(x))/h` with negative h.
Denjoy–Young–Saks assigns one of four mutually exclusive derivative patterns almost
everywhere to an arbitrary finite real function, without measurability assumptions.
Limits and extended-real operations use Mathlib. Source: GAPS 05.10.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory

/-- **05.10**: any finite real function has exactly one Dini type at almost every point.
No measurability or continuity assumption on the function is imposed. -/
theorem ae_existsUnique_diniType (f : ℝ → ℝ) :
    ∀ᵐ x ∂volume, ∃! i : Fin 4, HasDiniType f x i :=
  ae_diniType f

end CKMA
