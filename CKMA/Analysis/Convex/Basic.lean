/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Data.EReal.Basic

/-!
# Extended-real properness

Properness for an extended-real function means that no value is `-∞` and some value is finite.
The predicate does not use a norm, an inner product, or convexity.

## Main definitions

* `CKMA.IsProperERealFunction`: properness predicate for extended-real functions.

## Main results

* `CKMA.isProperERealFunction_iff`, `CKMA.IsProperERealFunction.intro`: the defining property and
  its introduction rule.
-/

public section

namespace CKMA

/-- Properness for extended-real convex analysis: no value is `-∞`, and some value is finite. -/
@[expose]
def IsProperERealFunction {E : Type*} (f : E → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ ∃ x, f x ≠ ⊤

/-- Defining property of `IsProperERealFunction`. -/
theorem isProperERealFunction_iff {E : Type*} {f : E → EReal} :
    IsProperERealFunction f ↔ (∀ x, f x ≠ ⊥) ∧ ∃ x, f x ≠ ⊤ := Iff.rfl

/-- A proper function takes no value `-∞`. -/
theorem IsProperERealFunction.ne_bot {E : Type*} {f : E → EReal} (hf : IsProperERealFunction f)
    (x : E) : f x ≠ ⊥ :=
  hf.1 x

/-- A proper function has a point of finite value. -/
theorem IsProperERealFunction.exists_ne_top {E : Type*} {f : E → EReal}
    (hf : IsProperERealFunction f) : ∃ x, f x ≠ ⊤ :=
  hf.2

/-- Introduction rule for `IsProperERealFunction`. -/
theorem IsProperERealFunction.intro {E : Type*} {f : E → EReal} (hbot : ∀ x, f x ≠ ⊥) {x : E}
    (hx : f x ≠ ⊤) : IsProperERealFunction f :=
  ⟨hbot, x, hx⟩

end CKMA
