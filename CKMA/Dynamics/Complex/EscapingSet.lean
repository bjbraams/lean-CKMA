/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic

/-!
# Escaping sets of transcendental entire functions (46.58)

The escaping set of `f : ℂ → ℂ` consists of the points whose orbit norms tend to infinity.
For a transcendental entire `f`, Eremenko's theorem says that the escaping set is nonempty and
that every component of its closure is unbounded.

## Main definitions

* `CKMA.complexEscapingSet`: points with `‖f^[n] z‖ → ∞`.
* `CKMA.IsTranscendentalEntire`: entire functions that are not polynomial functions.

## Main results

* `CKMA.eremenko_escaping`: Eremenko's theorem, the nonemptiness and unbounded-component clauses
  (**46.58**).
-/

public section

namespace CKMA

open Filter Polynomial

/-- The escaping set of a complex map, using divergence of the orbit norm. -/
@[expose]
def complexEscapingSet (f : ℂ → ℂ) : Set ℂ :=
  {z | Tendsto (fun n : ℕ ↦ ‖(f^[n]) z‖) atTop atTop}

/-- Membership in `complexEscapingSet`. -/
theorem mem_complexEscapingSet_iff {f : ℂ → ℂ} {z : ℂ} :
    z ∈ complexEscapingSet f ↔ Tendsto (fun n : ℕ ↦ ‖(f^[n]) z‖) atTop atTop := Iff.rfl

/-- Transcendental entire functions are entire and are not polynomial functions. -/
@[expose]
def IsTranscendentalEntire (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ ∀ p : ℂ[X], f ≠ fun z ↦ p.eval z

/-- Unfolding of `IsTranscendentalEntire`. -/
theorem isTranscendentalEntire_iff {f : ℂ → ℂ} :
    IsTranscendentalEntire f ↔ Differentiable ℂ f ∧ ∀ p : ℂ[X], f ≠ fun z ↦ p.eval z := Iff.rfl

/-- **46.58**, escaping-set clauses: nonemptiness and unbounded components of the closure.
The equality of its boundary with the nonnormality Julia set remains a separate interface. -/
theorem eremenko_escaping {f : ℂ → ℂ} (hf : IsTranscendentalEntire f) :
    (complexEscapingSet f).Nonempty ∧
      ∀ z ∈ closure (complexEscapingSet f),
        ¬ Bornology.IsBounded (connectedComponentIn (closure (complexEscapingSet f)) z) := by
  sorry

end CKMA
