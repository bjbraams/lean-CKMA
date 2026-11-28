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
* `CKMA.DiniType`: the four Denjoy–Young–Saks alternatives, as named cases.
* `CKMA.HasDiniType`: the Dini derivatives of `f` at `x` follow a given alternative.

## Main results

* `CKMA.isBoundedUnder_le_extendedDifferenceQuotient`,
  `CKMA.isBoundedUnder_ge_extendedDifferenceQuotient`: `EReal` boundedness of the extended
  difference quotient under any filter.
* `CKMA.hasDiniType_finite_iff`, `CKMA.hasDiniType_infinite_iff`,
  `CKMA.hasDiniType_upperRightTop_iff`, `CKMA.hasDiniType_upperLeftTop_iff`: the four
  alternatives spelled out.
-/

public section

noncomputable section

namespace CKMA

open Filter Topology

/-- The real difference quotient, embedded in the extended real line. -/
@[expose]
def extendedDifferenceQuotient (f : ℝ → ℝ) (x h : ℝ) : EReal :=
  ((f (x + h) - f x) / h : ℝ)

/-- The extended difference quotient is the real quotient `(f (x + h) - f x) / h`. -/
lemma extendedDifferenceQuotient_def (f : ℝ → ℝ) (x h : ℝ) :
    extendedDifferenceQuotient f x h = ((f (x + h) - f x) / h : ℝ) :=
  rfl

/-- Upper right Dini derivative, with positive increments tending to zero. -/
@[expose]
def upperRightDiniDerivative (f : ℝ → ℝ) (x : ℝ) : EReal :=
  limsup (extendedDifferenceQuotient f x) (𝓝[>] 0)

/-- The upper right Dini derivative is the `limsup` of the quotient as `h → 0⁺`. -/
lemma upperRightDiniDerivative_def (f : ℝ → ℝ) (x : ℝ) :
    upperRightDiniDerivative f x = limsup (extendedDifferenceQuotient f x) (𝓝[>] 0) :=
  rfl

/-- Lower right Dini derivative. -/
@[expose]
def lowerRightDiniDerivative (f : ℝ → ℝ) (x : ℝ) : EReal :=
  liminf (extendedDifferenceQuotient f x) (𝓝[>] 0)

/-- The lower right Dini derivative is the `liminf` of the quotient as `h → 0⁺`. -/
lemma lowerRightDiniDerivative_def (f : ℝ → ℝ) (x : ℝ) :
    lowerRightDiniDerivative f x = liminf (extendedDifferenceQuotient f x) (𝓝[>] 0) :=
  rfl

/-- Upper left Dini derivative, with negative increments increasing to zero. -/
@[expose]
def upperLeftDiniDerivative (f : ℝ → ℝ) (x : ℝ) : EReal :=
  limsup (extendedDifferenceQuotient f x) (𝓝[<] 0)

/-- The upper left Dini derivative is the `limsup` of the quotient as `h → 0⁻`. -/
lemma upperLeftDiniDerivative_def (f : ℝ → ℝ) (x : ℝ) :
    upperLeftDiniDerivative f x = limsup (extendedDifferenceQuotient f x) (𝓝[<] 0) :=
  rfl

/-- Lower left Dini derivative. -/
@[expose]
def lowerLeftDiniDerivative (f : ℝ → ℝ) (x : ℝ) : EReal :=
  liminf (extendedDifferenceQuotient f x) (𝓝[<] 0)

/-- The lower left Dini derivative is the `liminf` of the quotient as `h → 0⁻`. -/
lemma lowerLeftDiniDerivative_def (f : ℝ → ℝ) (x : ℝ) :
    lowerLeftDiniDerivative f x = liminf (extendedDifferenceQuotient f x) (𝓝[<] 0) :=
  rfl

/-- The extended difference quotient is bounded above in `EReal` under any filter. -/
lemma isBoundedUnder_le_extendedDifferenceQuotient (f : ℝ → ℝ) (x : ℝ) (l : Filter ℝ) :
    l.IsBoundedUnder (· ≤ ·) (extendedDifferenceQuotient f x) :=
  ⟨⊤, Eventually.of_forall fun _ => le_top⟩

/-- The extended difference quotient is bounded below in `EReal` under any filter. -/
lemma isBoundedUnder_ge_extendedDifferenceQuotient (f : ℝ → ℝ) (x : ℝ) (l : Filter ℝ) :
    l.IsBoundedUnder (· ≥ ·) (extendedDifferenceQuotient f x) :=
  ⟨⊥, Eventually.of_forall fun _ => bot_le⟩

/-- The four alternatives of the Denjoy–Young–Saks theorem. -/
inductive DiniType : Type
  /-- All four Dini derivatives have a common finite value. -/
  | finite
  /-- Both upper Dini derivatives are `⊤` and both lower Dini derivatives are `⊥`. -/
  | infinite
  /-- The upper right derivative is `⊤`, the lower left derivative is `⊥`, and the lower right
  and upper left derivatives have a common finite value. -/
  | upperRightTop
  /-- The upper left derivative is `⊤`, the lower right derivative is `⊥`, and the lower left
  and upper right derivatives have a common finite value. -/
  | upperLeftTop
  deriving DecidableEq

/-- The Dini derivatives of `f` at `x` follow the alternative `t`. The left derivatives use the
same quotient `(f (x + h) - f x) / h` with `h < 0`. -/
@[expose]
def HasDiniType (f : ℝ → ℝ) (x : ℝ) : DiniType → Prop
  | .finite => ∃ a : ℝ, upperRightDiniDerivative f x = a ∧ lowerRightDiniDerivative f x = a ∧
      upperLeftDiniDerivative f x = a ∧ lowerLeftDiniDerivative f x = a
  | .infinite => upperRightDiniDerivative f x = ⊤ ∧ upperLeftDiniDerivative f x = ⊤ ∧
      lowerRightDiniDerivative f x = ⊥ ∧ lowerLeftDiniDerivative f x = ⊥
  | .upperRightTop => upperRightDiniDerivative f x = ⊤ ∧ lowerLeftDiniDerivative f x = ⊥ ∧
      ∃ a : ℝ, lowerRightDiniDerivative f x = a ∧ upperLeftDiniDerivative f x = a
  | .upperLeftTop => upperLeftDiniDerivative f x = ⊤ ∧ lowerRightDiniDerivative f x = ⊥ ∧
      ∃ a : ℝ, lowerLeftDiniDerivative f x = a ∧ upperRightDiniDerivative f x = a

/-- The finite alternative: all four Dini derivatives equal a common real number. -/
lemma hasDiniType_finite_iff {f : ℝ → ℝ} {x : ℝ} :
    HasDiniType f x .finite ↔ ∃ a : ℝ, upperRightDiniDerivative f x = a ∧
      lowerRightDiniDerivative f x = a ∧ upperLeftDiniDerivative f x = a ∧
      lowerLeftDiniDerivative f x = a :=
  Iff.rfl

/-- The infinite alternative: both upper derivatives are `⊤`, both lower ones `⊥`. -/
lemma hasDiniType_infinite_iff {f : ℝ → ℝ} {x : ℝ} :
    HasDiniType f x .infinite ↔ upperRightDiniDerivative f x = ⊤ ∧
      upperLeftDiniDerivative f x = ⊤ ∧ lowerRightDiniDerivative f x = ⊥ ∧
      lowerLeftDiniDerivative f x = ⊥ :=
  Iff.rfl

/-- The mixed alternative with upper right derivative `⊤` and lower left derivative `⊥`. -/
lemma hasDiniType_upperRightTop_iff {f : ℝ → ℝ} {x : ℝ} :
    HasDiniType f x .upperRightTop ↔ upperRightDiniDerivative f x = ⊤ ∧
      lowerLeftDiniDerivative f x = ⊥ ∧
      ∃ a : ℝ, lowerRightDiniDerivative f x = a ∧ upperLeftDiniDerivative f x = a :=
  Iff.rfl

/-- The mixed alternative with upper left derivative `⊤` and lower right derivative `⊥`. -/
lemma hasDiniType_upperLeftTop_iff {f : ℝ → ℝ} {x : ℝ} :
    HasDiniType f x .upperLeftTop ↔ upperLeftDiniDerivative f x = ⊤ ∧
      lowerRightDiniDerivative f x = ⊥ ∧
      ∃ a : ℝ, lowerLeftDiniDerivative f x = a ∧ upperRightDiniDerivative f x = a :=
  Iff.rfl

end CKMA
