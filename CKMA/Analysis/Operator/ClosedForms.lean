/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Closed semibounded forms and self-adjoint realizations

Sesquilinear forms are conjugate-linear in the first slot on an explicit submodule domain.
Closedness uses the shifted form norm, rather than the ambient Hilbert norm on that domain.
The associated-operator identity records the inclusion of the operator domain in the form domain.

The representation theorem preserves the lower bound and gives uniqueness. Friedrichs extension
is stated here through existence and its lower bound; KLMN controls symmetric perturbations
with relative form bound below one on the same domain. Sources: GAPS 22.19, 22.21, and 22.22.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A sesquilinear form on a specified submodule domain, conjugate-linear in the first slot. -/
abbrev DomainSesquilinearForm (D : Submodule ℂ H) := D →ₗ⋆[ℂ] D →ₗ[ℂ] ℂ

/-- The graph/form norm for the lower bound `q[x] ≥ -c‖x‖²`. -/
def formGraphNorm {D : Submodule ℂ H} (q : DomainSesquilinearForm D) (c : ℝ) (x : D) : ℝ :=
  Real.sqrt ((q x x).re + (c + 1) * ‖(x : H)‖ ^ 2)

/-- Completeness in the actual form norm, expressed by its Cauchy and convergence criteria.
This avoids silently imposing the original Hilbert norm on the form domain. -/
def IsCompleteFormDomain {D : Submodule ℂ H} (q : DomainSesquilinearForm D) (c : ℝ) : Prop :=
  ∀ u : ℕ → D,
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n → formGraphNorm q c (u m - u n) < ε) →
    ∃ x : D, Tendsto (fun n ↦ formGraphNorm q c (u n - x)) atTop (𝓝 0)

/-- A closed symmetric form with an explicit lower-semibound constant. -/
def IsClosedSemiboundedForm {D : Submodule ℂ H} (q : DomainSesquilinearForm D) (c : ℝ) : Prop :=
  0 ≤ c ∧ (∀ x y : D, q x y = star (q y x)) ∧
    (∀ x : D, -c * ‖(x : H)‖ ^ 2 ≤ (q x x).re) ∧ IsCompleteFormDomain q c

/-- The representation identity with all domain inclusions explicit. -/
def IsAssociatedFormOperator {D : Submodule ℂ H} (q : DomainSesquilinearForm D)
    (A : H →ₗ.[ℂ] H) : Prop :=
  ∃ h : A.domain ≤ D, ∀ x : A.domain, ∀ y : D,
    q y ⟨(x : H), h x.property⟩ = ⟪(y : H), A x⟫_ℂ

/-- **22.19**, the first representation theorem, including uniqueness and the same lower bound. -/
theorem existsUnique_formOperator {D : Submodule ℂ H} (hD : Dense (D : Set H))
    (q : DomainSesquilinearForm D) {c : ℝ} (hq : IsClosedSemiboundedForm q c) :
    ∃! A : H →ₗ.[ℂ] H, IsSelfAdjoint A ∧ IsAssociatedFormOperator q A ∧
      ∀ x : A.domain, -c * ‖(x : H)‖ ^ 2 ≤ (⟪(x : H), A x⟫_ℂ).re := by
  sorry

/-- **22.21**, the existence/lower-bound clause of Friedrichs extension.
The canonical form completion and its uniqueness characterization remain separate targets. -/
theorem exists_semibounded_selfAdjoint_extension (A : H →ₗ.[ℂ] H)
    (hA : A.IsFormalAdjoint A) (hd : Dense (A.domain : Set H)) {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ x : A.domain, -c * ‖(x : H)‖ ^ 2 ≤ (⟪(x : H), A x⟫_ℂ).re) :
    ∃ F : H →ₗ.[ℂ] H, IsSelfAdjoint F ∧ A ≤ F ∧
      ∀ x : F.domain, -c * ‖(x : H)‖ ^ 2 ≤ (⟪(x : H), F x⟫_ℂ).re := by
  sorry

/-- **22.22**, KLMN: a symmetric relative-form perturbation of bound below one preserves
closedness on the same domain and gives the explicit lower bound `-c`. -/
theorem klmn {D : Submodule ℂ H} (q b : DomainSesquilinearForm D)
    (hq : IsClosedSemiboundedForm q 0) (hb : ∀ x y : D, b x y = star (b y x))
    {a c : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hc : 0 ≤ c)
    (hbound : ∀ x : D, ‖b x x‖ ≤ a * (q x x).re + c * ‖(x : H)‖ ^ 2) :
    IsClosedSemiboundedForm (q + b) c := by
  sorry

end CKMA
