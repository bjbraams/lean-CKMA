/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Data.EReal.Operations

/-!
# Extended-real properness

Properness for an extended-real function means that no value is `-∞` and some value is finite.
The predicate does not use a norm, an inner product, or convexity.
-/

@[expose] public section

namespace CKMA

/-- Properness for extended-real convex analysis: no value is `-∞`, and some value is finite. -/
def IsProperERealFunction {E : Type*} (f : E → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ ∃ x, f x ≠ ⊤

end CKMA
