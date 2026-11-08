/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Data.EReal.Operations
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.LiminfLimsup

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

open Filter Topology MeasureTheory

/-- The real difference quotient, embedded in the extended real line. -/
def extendedDifferenceQuotient (f : ℝ → ℝ) (x h : ℝ) : EReal :=
  ((f (x + h) - f x) / h : ℝ)

/-- Upper right Dini derivative, with positive increments tending to zero. -/
def upperRightDiniDerivative (f : ℝ → ℝ) (x : ℝ) : EReal :=
  limsup (extendedDifferenceQuotient f x) (𝓝[>] 0)

/-- Lower right Dini derivative. -/
def lowerRightDiniDerivative (f : ℝ → ℝ) (x : ℝ) : EReal :=
  liminf (extendedDifferenceQuotient f x) (𝓝[>] 0)

/-- Upper left Dini derivative, with negative increments increasing to zero. -/
def upperLeftDiniDerivative (f : ℝ → ℝ) (x : ℝ) : EReal :=
  limsup (extendedDifferenceQuotient f x) (𝓝[<] 0)

/-- Lower left Dini derivative. -/
def lowerLeftDiniDerivative (f : ℝ → ℝ) (x : ℝ) : EReal :=
  liminf (extendedDifferenceQuotient f x) (𝓝[<] 0)

/-- The four alternatives of Denjoy–Young–Saks, numbered from zero.
The left derivatives use the same quotient `(f(x+h)-f(x))/h` with `h<0`. -/
def HasDiniType (f : ℝ → ℝ) (x : ℝ) (i : Fin 4) : Prop :=
  match i.val with
  | 0 => ∃ a : ℝ, upperRightDiniDerivative f x = a ∧ lowerRightDiniDerivative f x = a ∧
      upperLeftDiniDerivative f x = a ∧ lowerLeftDiniDerivative f x = a
  | 1 => upperRightDiniDerivative f x = ⊤ ∧ upperLeftDiniDerivative f x = ⊤ ∧
      lowerRightDiniDerivative f x = ⊥ ∧ lowerLeftDiniDerivative f x = ⊥
  | 2 => upperRightDiniDerivative f x = ⊤ ∧ lowerLeftDiniDerivative f x = ⊥ ∧
      ∃ a : ℝ, lowerRightDiniDerivative f x = a ∧ upperLeftDiniDerivative f x = a
  | _ => upperLeftDiniDerivative f x = ⊤ ∧ lowerRightDiniDerivative f x = ⊥ ∧
      ∃ a : ℝ, lowerLeftDiniDerivative f x = a ∧ upperRightDiniDerivative f x = a

/-- **05.10**: any finite real function has exactly one Dini type at almost every point.
No measurability or continuity assumption on the function is imposed. -/
theorem ae_existsUnique_diniType (f : ℝ → ℝ) :
    ∀ᵐ x ∂volume, ∃! i : Fin 4, HasDiniType f x i := by
  sorry

end CKMA
