/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Order.LiminfLimsup
public import Mathlib.Data.EReal.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Dini derivatives

The four one-sided upper and lower Dini derivatives take values in the extended real
line. Both left derivatives use the quotient `(f(x + h) - f(x)) / h` with negative `h`.
Limits and extended-real operations use Mathlib. Source: GAPS 05.10.

## Main definitions

* `CKMA.extendedDifferenceQuotient`: real difference quotient in `EReal`.
* `CKMA.upperRightDiniDerivative`, `CKMA.lowerRightDiniDerivative`: right Dini derivatives.
* `CKMA.upperLeftDiniDerivative`, `CKMA.lowerLeftDiniDerivative`: left Dini derivatives.
* `CKMA.HasDiniType`: the four Denjoy–Young–Saks derivative patterns.

## Main results

* `CKMA.differenceQuotient_rev`: symmetry of the difference quotient.
* `CKMA.isBoundedUnder_le_extendedDifferenceQuotient`,
  `CKMA.isBoundedUnder_ge_extendedDifferenceQuotient`: `EReal` boundedness of the extended
  difference quotient under any filter.
-/

public section

noncomputable section

namespace CKMA

open Filter Topology

/-- The real difference quotient, embedded in the extended real line. -/
@[expose]
def extendedDifferenceQuotient (f : ℝ → ℝ) (x h : ℝ) : EReal :=
  ((f (x + h) - f x) / h : ℝ)

/-- Upper right Dini derivative, with positive increments tending to zero. -/
@[expose]
def upperRightDiniDerivative (f : ℝ → ℝ) (x : ℝ) : EReal :=
  limsup (extendedDifferenceQuotient f x) (𝓝[>] 0)

/-- Lower right Dini derivative. -/
@[expose]
def lowerRightDiniDerivative (f : ℝ → ℝ) (x : ℝ) : EReal :=
  liminf (extendedDifferenceQuotient f x) (𝓝[>] 0)

/-- Upper left Dini derivative, with negative increments increasing to zero. -/
@[expose]
def upperLeftDiniDerivative (f : ℝ → ℝ) (x : ℝ) : EReal :=
  limsup (extendedDifferenceQuotient f x) (𝓝[<] 0)

/-- Lower left Dini derivative. -/
@[expose]
def lowerLeftDiniDerivative (f : ℝ → ℝ) (x : ℝ) : EReal :=
  liminf (extendedDifferenceQuotient f x) (𝓝[<] 0)

/-- Reversing the increment leaves the difference quotient unchanged. -/
lemma differenceQuotient_rev (f : ℝ → ℝ) (a b : ℝ) :
    (f a - f b) / (a - b) = (f b - f a) / (b - a) := by
  rw [(neg_sub b a).symm, div_neg, ← neg_div, neg_sub]

/-- The extended difference quotient is bounded above in `EReal` under any filter. -/
lemma isBoundedUnder_le_extendedDifferenceQuotient (f : ℝ → ℝ) (x : ℝ) (l : Filter ℝ) :
    l.IsBoundedUnder (· ≤ ·) (extendedDifferenceQuotient f x) :=
  ⟨⊤, Eventually.of_forall fun _ => le_top⟩

/-- The extended difference quotient is bounded below in `EReal` under any filter. -/
lemma isBoundedUnder_ge_extendedDifferenceQuotient (f : ℝ → ℝ) (x : ℝ) (l : Filter ℝ) :
    l.IsBoundedUnder (· ≥ ·) (extendedDifferenceQuotient f x) :=
  ⟨⊥, Eventually.of_forall fun _ => bot_le⟩

@[deprecated (since := "2026-11-15")]
alias diniQuotient_bddAbove := isBoundedUnder_le_extendedDifferenceQuotient

@[deprecated (since := "2026-11-15")]
alias diniQuotient_bddBelow := isBoundedUnder_ge_extendedDifferenceQuotient

/-- The four alternatives of Denjoy–Young–Saks, numbered from zero.
The left derivatives use the same quotient `(f(x+h)-f(x))/h` with `h<0`. -/
@[expose]
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

end CKMA
