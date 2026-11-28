/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Closed semibounded forms and self-adjoint realizations

Sesquilinear forms are conjugate-linear in the first slot on an explicit submodule domain.
A lower bound is written `q[x] ≥ -c‖x‖²` with an arbitrary real `c`, so a positive lower bound
`q[x] ≥ m‖x‖²` is the case `c = -m`. Closedness is completeness in the shifted form norm
`(re q[x] + (c + 1)‖x‖²)^{1/2}`, which dominates the Hilbert norm under the lower bound.
The associated-operator identity records the inclusion of the operator domain in the form domain.

The representation theorem preserves the lower bound and gives uniqueness. The Friedrichs
extension is stated through existence and preservation of the lower bound; KLMN controls
symmetric perturbations with relative form bound below one on the same domain.
Sources: GAPS 22.19, 22.21, and 22.22.

## Main definitions

* `CKMA.DomainSesquilinearForm`: sesquilinear form on a submodule domain.
* `CKMA.formGraphNorm`: shifted graph norm of a semibounded sesquilinear form.
* `CKMA.IsCompleteFormDomain`: completeness of the form domain in `formGraphNorm`.
* `CKMA.IsClosedSemiboundedForm`: closed symmetric lower-semibounded sesquilinear form.
* `CKMA.IsAssociatedFormOperator`: operator associated with a sesquilinear form.

## Main results

* `CKMA.existsUnique_isSelfAdjoint_isAssociatedFormOperator`: first representation theorem for
  closed semibounded forms.
* `CKMA.exists_semibounded_selfAdjoint_extension`: Friedrichs extension of a semibounded operator.
* `CKMA.IsClosedSemiboundedForm.add`: the KLMN theorem for symmetric relative-form
  perturbations.
-/

public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped InnerProductSpace

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A sesquilinear form on a specified submodule domain, conjugate-linear in the first slot. -/
abbrev DomainSesquilinearForm (D : Submodule 𝕜 H) := D →ₗ⋆[𝕜] D →ₗ[𝕜] 𝕜

/-- The graph/form norm for the lower bound `q[x] ≥ -c‖x‖²`. -/
@[expose]
def formGraphNorm {D : Submodule 𝕜 H} (q : DomainSesquilinearForm D) (c : ℝ) (x : D) : ℝ :=
  Real.sqrt (RCLike.re (q x x) + (c + 1) * ‖(x : H)‖ ^ 2)

omit [CompleteSpace H] in
/-- The defining formula of `formGraphNorm`. -/
theorem formGraphNorm_def {D : Submodule 𝕜 H} (q : DomainSesquilinearForm D) (c : ℝ) (x : D) :
    formGraphNorm q c x = Real.sqrt (RCLike.re (q x x) + (c + 1) * ‖(x : H)‖ ^ 2) :=
  rfl

omit [CompleteSpace H] in
/-- The form norm is nonnegative. -/
theorem formGraphNorm_nonneg {D : Submodule 𝕜 H} (q : DomainSesquilinearForm D) (c : ℝ)
    (x : D) : 0 ≤ formGraphNorm q c x :=
  Real.sqrt_nonneg _

/-- Completeness in the form norm, expressed by its Cauchy and convergence criteria. -/
@[expose]
def IsCompleteFormDomain {D : Submodule 𝕜 H} (q : DomainSesquilinearForm D) (c : ℝ) : Prop :=
  ∀ u : ℕ → D,
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n → formGraphNorm q c (u m - u n) < ε) →
    ∃ x : D, Tendsto (fun n ↦ formGraphNorm q c (u n - x)) atTop (𝓝 0)

omit [CompleteSpace H] in
/-- The defining property of `IsCompleteFormDomain`. -/
theorem isCompleteFormDomain_iff {D : Submodule 𝕜 H} (q : DomainSesquilinearForm D) (c : ℝ) :
    IsCompleteFormDomain q c ↔ ∀ u : ℕ → D,
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
        formGraphNorm q c (u m - u n) < ε) →
      ∃ x : D, Tendsto (fun n ↦ formGraphNorm q c (u n - x)) atTop (𝓝 0) :=
  Iff.rfl

/-- A closed symmetric form with the lower bound `q[x] ≥ -c‖x‖²`, for an arbitrary real `c`. -/
@[expose]
def IsClosedSemiboundedForm {D : Submodule 𝕜 H} (q : DomainSesquilinearForm D) (c : ℝ) : Prop :=
  (∀ x y : D, q x y = star (q y x)) ∧
    (∀ x : D, -c * ‖(x : H)‖ ^ 2 ≤ RCLike.re (q x x)) ∧ IsCompleteFormDomain q c

omit [CompleteSpace H] in
/-- The defining property of `IsClosedSemiboundedForm`. -/
theorem isClosedSemiboundedForm_iff {D : Submodule 𝕜 H} (q : DomainSesquilinearForm D)
    (c : ℝ) : IsClosedSemiboundedForm q c ↔ (∀ x y : D, q x y = star (q y x)) ∧
      (∀ x : D, -c * ‖(x : H)‖ ^ 2 ≤ RCLike.re (q x x)) ∧ IsCompleteFormDomain q c :=
  Iff.rfl

omit [CompleteSpace H] in
/-- A closed semibounded form is Hermitian. -/
theorem IsClosedSemiboundedForm.symm {D : Submodule 𝕜 H} {q : DomainSesquilinearForm D}
    {c : ℝ} (hq : IsClosedSemiboundedForm q c) (x y : D) : q x y = star (q y x) :=
  hq.1 x y

omit [CompleteSpace H] in
/-- The lower bound of a closed semibounded form. -/
theorem IsClosedSemiboundedForm.lower_bound {D : Submodule 𝕜 H} {q : DomainSesquilinearForm D}
    {c : ℝ} (hq : IsClosedSemiboundedForm q c) (x : D) :
    -c * ‖(x : H)‖ ^ 2 ≤ RCLike.re (q x x) :=
  hq.2.1 x

omit [CompleteSpace H] in
/-- A closed semibounded form has a complete form domain. -/
theorem IsClosedSemiboundedForm.isCompleteFormDomain {D : Submodule 𝕜 H}
    {q : DomainSesquilinearForm D} {c : ℝ} (hq : IsClosedSemiboundedForm q c) :
    IsCompleteFormDomain q c :=
  hq.2.2

/-- The representation identity with all domain inclusions explicit. -/
@[expose]
def IsAssociatedFormOperator {D : Submodule 𝕜 H} (q : DomainSesquilinearForm D)
    (A : H →ₗ.[𝕜] H) : Prop :=
  ∃ h : A.domain ≤ D, ∀ x : A.domain, ∀ y : D,
    q y ⟨(x : H), h x.property⟩ = ⟪(y : H), A x⟫_𝕜

omit [CompleteSpace H] in
/-- The defining property of `IsAssociatedFormOperator`. -/
theorem isAssociatedFormOperator_iff {D : Submodule 𝕜 H} (q : DomainSesquilinearForm D)
    (A : H →ₗ.[𝕜] H) : IsAssociatedFormOperator q A ↔ ∃ h : A.domain ≤ D,
      ∀ x : A.domain, ∀ y : D, q y ⟨(x : H), h x.property⟩ = ⟪(y : H), A x⟫_𝕜 :=
  Iff.rfl

/-- **22.19**, the first representation theorem, including uniqueness and the same lower bound. -/
theorem existsUnique_isSelfAdjoint_isAssociatedFormOperator {D : Submodule 𝕜 H}
    (hD : Dense (D : Set H)) (q : DomainSesquilinearForm D) {c : ℝ}
    (hq : IsClosedSemiboundedForm q c) :
    ∃! A : H →ₗ.[𝕜] H, IsSelfAdjoint A ∧ IsAssociatedFormOperator q A ∧
      ∀ x : A.domain, -c * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪(x : H), A x⟫_𝕜 := by
  sorry

/-- **22.21**, the existence and lower-bound clause of the Friedrichs extension: a densely
defined symmetric operator with `⟪x, A x⟫ ≥ -c‖x‖²` has a self-adjoint extension with the same
lower bound, for every real `c`. -/
theorem exists_semibounded_selfAdjoint_extension (A : H →ₗ.[𝕜] H)
    (hA : A.IsFormalAdjoint A) (hd : Dense (A.domain : Set H)) {c : ℝ}
    (hb : ∀ x : A.domain, -c * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪(x : H), A x⟫_𝕜) :
    ∃ F : H →ₗ.[𝕜] H, IsSelfAdjoint F ∧ A ≤ F ∧
      ∀ x : F.domain, -c * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪(x : H), F x⟫_𝕜 := by
  sorry

omit [CompleteSpace H] in
/-- Under the lower bound `q[x] ≥ -c‖x‖²`, the square of the form norm is the shifted quadratic
value. -/
theorem formGraphNorm_sq {D : Submodule 𝕜 H} {q : DomainSesquilinearForm D} {c : ℝ}
    {x : D} (h : -c * ‖(x : H)‖ ^ 2 ≤ RCLike.re (q x x)) :
    formGraphNorm q c x ^ 2 = RCLike.re (q x x) + (c + 1) * ‖(x : H)‖ ^ 2 :=
  Real.sq_sqrt (by nlinarith [sq_nonneg ‖(x : H)‖])

omit [CompleteSpace H] in
/-- From `α a² ≤ b²` with `a, b ≥ 0` and `0 ≤ α` follows `√α a ≤ b`. -/
private lemma sqrt_mul_le_of_mul_sq_le {α a b : ℝ} (hα : 0 ≤ α) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : α * a ^ 2 ≤ b ^ 2) : Real.sqrt α * a ≤ b := by
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_mul hα, Real.sqrt_sq ha, Real.sqrt_sq hb] at this

omit [CompleteSpace H] in
/-- Completeness transfers between two form norms that are equivalent up to constants. -/
theorem IsCompleteFormDomain.of_sq_le {D : Submodule 𝕜 H} {q q' : DomainSesquilinearForm D}
    {c c' α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β)
    (hlow : ∀ x : D, α * formGraphNorm q c x ^ 2 ≤ formGraphNorm q' c' x ^ 2)
    (hup : ∀ x : D, formGraphNorm q' c' x ^ 2 ≤ β * formGraphNorm q c x ^ 2)
    (hq : IsCompleteFormDomain q c) : IsCompleteFormDomain q' c' := by
  have hsα : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have hle (x : D) : Real.sqrt α * formGraphNorm q c x ≤ formGraphNorm q' c' x :=
    sqrt_mul_le_of_mul_sq_le hα.le (formGraphNorm_nonneg _ _ _) (formGraphNorm_nonneg _ _ _)
      (hlow x)
  have hge (x : D) : formGraphNorm q' c' x ≤ Real.sqrt β * formGraphNorm q c x := by
    have h := Real.sqrt_le_sqrt (hup x)
    rwa [Real.sqrt_mul hβ, Real.sqrt_sq (formGraphNorm_nonneg _ _ _),
      Real.sqrt_sq (formGraphNorm_nonneg _ _ _)] at h
  intro u hu
  obtain ⟨x, hx⟩ := hq u fun ε hε ↦ by
    obtain ⟨N, hN⟩ := hu (Real.sqrt α * ε) (mul_pos hsα hε)
    exact ⟨N, fun m n hm hn ↦ lt_of_mul_lt_mul_left ((hle _).trans_lt (hN m n hm hn)) hsα.le⟩
  refine ⟨x, squeeze_zero (fun _ ↦ formGraphNorm_nonneg _ _ _) (fun n ↦ hge (u n - x)) ?_⟩
  simpa using hx.const_mul (Real.sqrt β)

omit [CompleteSpace H] in
/-- **22.22**, KLMN: a symmetric perturbation `b` with relative form bound
`|b[x]| ≤ a q[x] + c‖x‖²`, `0 ≤ a < 1`, of a closed form `q ≥ -c₀‖x‖²` is closed on the same
domain, with lower bound `q + b ≥ -((1 - a) c₀ + c)‖x‖²`. -/
theorem IsClosedSemiboundedForm.add {D : Submodule 𝕜 H} {q : DomainSesquilinearForm D} {c₀ : ℝ}
    (hq : IsClosedSemiboundedForm q c₀) (b : DomainSesquilinearForm D)
    (hb : ∀ x y : D, b x y = star (b y x)) {a c : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hbound : ∀ x : D, ‖b x x‖ ≤ a * RCLike.re (q x x) + c * ‖(x : H)‖ ^ 2) :
    IsClosedSemiboundedForm (q + b) ((1 - a) * c₀ + c) := by
  have hadd (x y : D) : (q + b) x y = q x y + b x y := by
    rw [LinearMap.add_apply, LinearMap.add_apply]
  have hre (x : D) : RCLike.re ((q + b) x x) = RCLike.re (q x x) + RCLike.re (b x x) := by
    rw [hadd x x, map_add]
  have hbre (x : D) := abs_le.mp ((RCLike.abs_re_le_norm (b x x)).trans (hbound x))
  have hsemi (x : D) :
      -((1 - a) * c₀ + c) * ‖(x : H)‖ ^ 2 ≤ RCLike.re ((q + b) x x) := by
    nlinarith [hre x, hbre x, hq.lower_bound x, mul_nonneg (sub_pos.mpr ha1).le
      (show 0 ≤ RCLike.re (q x x) + c₀ * ‖(x : H)‖ ^ 2 by linarith [hq.lower_bound x])]
  refine ⟨fun x y ↦ by rw [hadd x y, hadd y x, star_add, ← hq.symm x y, ← hb x y], hsemi, ?_⟩
  set β := 2 * c - 2 * a * c₀ + 1
  refine hq.isCompleteFormDomain.of_sq_le (α := min (1 - a) 1) (β := (1 + a) + |β|)
    (lt_min (sub_pos.mpr ha1) one_pos) (by positivity) (fun x ↦ ?_) (fun x ↦ ?_)
  all_goals
    have hX : 0 ≤ RCLike.re (q x x) + c₀ * ‖(x : H)‖ ^ 2 := by linarith [hq.lower_bound x]
    rw [formGraphNorm_sq (hq.lower_bound x), formGraphNorm_sq (hsemi x)]
  · nlinarith [hre x, hbre x, min_le_left (1 - a) 1, min_le_right (1 - a) 1,
      mul_le_mul_of_nonneg_right (min_le_left (1 - a) 1) hX,
      mul_le_mul_of_nonneg_right (min_le_right (1 - a) 1) (sq_nonneg ‖(x : H)‖)]
  · nlinarith [hre x, hbre x, mul_nonneg (abs_nonneg β) hX, mul_nonneg ha hX,
      mul_le_mul_of_nonneg_right (le_abs_self β) (sq_nonneg ‖(x : H)‖),
      mul_nonneg (abs_nonneg β) (sq_nonneg ‖(x : H)‖), mul_nonneg ha (sq_nonneg ‖(x : H)‖)]

end CKMA
