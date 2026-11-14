/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

import Mathlib.Tactic.Ring

/-!
# Closed semibounded forms and self-adjoint realizations

Sesquilinear forms are conjugate-linear in the first slot on an explicit submodule domain.
Closedness uses the shifted form norm, rather than the ambient Hilbert norm on that domain.
The associated-operator identity records the inclusion of the operator domain in the form domain.

The representation theorem preserves the lower bound and gives uniqueness. Friedrichs extension
is stated here through existence and its lower bound; KLMN controls symmetric perturbations
with relative form bound below one on the same domain. Sources: GAPS 22.19, 22.21, and 22.22.

## Main definitions

* `CKMA.DomainSesquilinearForm`: sesquilinear form on a submodule domain.
* `CKMA.formGraphNorm`: shifted graph norm of a semibounded sesquilinear form.
* `CKMA.IsCompleteFormDomain`: completeness of the form domain in `formGraphNorm`.
* `CKMA.IsClosedSemiboundedForm`: closed symmetric lower-semibounded sesquilinear form.
* `CKMA.IsAssociatedFormOperator`: operator associated with a sesquilinear form.

## Main results

* `CKMA.existsUnique_formOperator`: first representation theorem for closed semibounded forms.
* `CKMA.exists_semibounded_selfAdjoint_extension`: Friedrichs extension of a semibounded operator.
* `CKMA.klmn`: KLMN theorem for symmetric relative-form perturbations.

## Notation

* `⟪x, y⟫_𝕜`: inner product on a Hilbert space over `𝕜`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped InnerProductSpace

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A sesquilinear form on a specified submodule domain, conjugate-linear in the first slot. -/
abbrev DomainSesquilinearForm (D : Submodule 𝕜 H) := D →ₗ⋆[𝕜] D →ₗ[𝕜] 𝕜

/-- The graph/form norm for the lower bound `q[x] ≥ -c‖x‖²`. -/
def formGraphNorm {D : Submodule 𝕜 H} (q : DomainSesquilinearForm D) (c : ℝ) (x : D) : ℝ :=
  Real.sqrt (RCLike.re (q x x) + (c + 1) * ‖(x : H)‖ ^ 2)

/-- Completeness in the actual form norm, expressed by its Cauchy and convergence criteria.
This avoids silently imposing the original Hilbert norm on the form domain. -/
def IsCompleteFormDomain {D : Submodule 𝕜 H} (q : DomainSesquilinearForm D) (c : ℝ) : Prop :=
  ∀ u : ℕ → D,
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n → formGraphNorm q c (u m - u n) < ε) →
    ∃ x : D, Tendsto (fun n ↦ formGraphNorm q c (u n - x)) atTop (𝓝 0)

/-- A closed symmetric form with an explicit lower-semibound constant. -/
def IsClosedSemiboundedForm {D : Submodule 𝕜 H} (q : DomainSesquilinearForm D) (c : ℝ) : Prop :=
  0 ≤ c ∧ (∀ x y : D, q x y = star (q y x)) ∧
    (∀ x : D, -c * ‖(x : H)‖ ^ 2 ≤ RCLike.re (q x x)) ∧ IsCompleteFormDomain q c

/-- The representation identity with all domain inclusions explicit. -/
def IsAssociatedFormOperator {D : Submodule 𝕜 H} (q : DomainSesquilinearForm D)
    (A : H →ₗ.[𝕜] H) : Prop :=
  ∃ h : A.domain ≤ D, ∀ x : A.domain, ∀ y : D,
    q y ⟨(x : H), h x.property⟩ = ⟪(y : H), A x⟫_𝕜

/-- **22.19**, the first representation theorem, including uniqueness and the same lower bound. -/
theorem existsUnique_formOperator {D : Submodule 𝕜 H} (hD : Dense (D : Set H))
    (q : DomainSesquilinearForm D) {c : ℝ} (hq : IsClosedSemiboundedForm q c) :
    ∃! A : H →ₗ.[𝕜] H, IsSelfAdjoint A ∧ IsAssociatedFormOperator q A ∧
      ∀ x : A.domain, -c * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪(x : H), A x⟫_𝕜 := by
  sorry

/-- **22.21**, the existence/lower-bound clause of Friedrichs extension.
The canonical form completion and its uniqueness characterization remain separate targets. -/
theorem exists_semibounded_selfAdjoint_extension (A : H →ₗ.[𝕜] H)
    (hA : A.IsFormalAdjoint A) (hd : Dense (A.domain : Set H)) {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ x : A.domain, -c * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪(x : H), A x⟫_𝕜) :
    ∃ F : H →ₗ.[𝕜] H, IsSelfAdjoint F ∧ A ≤ F ∧
      ∀ x : F.domain, -c * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪(x : H), F x⟫_𝕜 := by
  sorry

omit [CompleteSpace H] in
/-- The square of a shifted form norm is the shifted quadratic value. -/
private lemma formGraphNorm_sq {D : Submodule 𝕜 H} (q : DomainSesquilinearForm D) (c : ℝ)
    (x : D) (h : 0 ≤ RCLike.re (q x x) + (c + 1) * ‖(x : H)‖ ^ 2) :
    formGraphNorm q c x ^ 2 = RCLike.re (q x x) + (c + 1) * ‖(x : H)‖ ^ 2 :=
  Real.sq_sqrt h

omit [CompleteSpace H] in
/-- **22.22**, KLMN: a symmetric relative-form perturbation of bound below one preserves
closedness on the same domain and gives the explicit lower bound `-c`. -/
theorem klmn {D : Submodule 𝕜 H} (q b : DomainSesquilinearForm D)
    (hq : IsClosedSemiboundedForm q 0) (hb : ∀ x y : D, b x y = star (b y x))
    {a c : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hc : 0 ≤ c)
    (hbound : ∀ x : D, ‖b x x‖ ≤ a * RCLike.re (q x x) + c * ‖(x : H)‖ ^ 2) :
    IsClosedSemiboundedForm (q + b) c := by
  obtain ⟨-, hq_symm, hq_lb, hq_complete⟩ := hq
  have hq_re (x : D) : 0 ≤ RCLike.re (q x x) := by
    simpa using hq_lb x
  -- Record the gap below one before any division by `1 - a`.
  have h1a : 0 < 1 - a := sub_pos.mpr ha1
  have hadd (x y : D) : (q + b) x y = q x y + b x y := by
    rw [LinearMap.add_apply, LinearMap.add_apply]
  have hsymm : ∀ x y : D, (q + b) x y = star ((q + b) y x) := by
    intro x y
    rw [hadd x y, hadd y x, star_add, ← hq_symm x y, ← hb x y]
  have hre_lower (x : D) :
      (1 - a) * RCLike.re (q x x) - c * ‖(x : H)‖ ^ 2 ≤ RCLike.re ((q + b) x x) := by
    have hbnd : -(a * RCLike.re (q x x) + c * ‖(x : H)‖ ^ 2) ≤ RCLike.re (b x x) := by
      refine (neg_le_neg (hbound x)).trans ?_
      exact (abs_le.mp (RCLike.abs_re_le_norm (b x x))).1
    calc
      (1 - a) * RCLike.re (q x x) - c * ‖(x : H)‖ ^ 2
          = RCLike.re (q x x) + -(a * RCLike.re (q x x) + c * ‖(x : H)‖ ^ 2) := by ring
      _ ≤ RCLike.re (q x x) + RCLike.re (b x x) := add_le_add_right hbnd _
      _ = RCLike.re ((q + b) x x) := by rw [hadd x x, map_add]
  have hsemi : ∀ x : D, -c * ‖(x : H)‖ ^ 2 ≤ RCLike.re ((q + b) x x) := by
    intro x
    refine le_trans ?_ (hre_lower x)
    rw [le_sub_iff_add_le]
    have hzero : -c * ‖(x : H)‖ ^ 2 + c * ‖(x : H)‖ ^ 2 = 0 := by ring
    rw [hzero]
    exact mul_nonneg h1a.le (hq_re x)
  have hq_nonneg (x : D) : 0 ≤ RCLike.re (q x x) + (0 + 1) * ‖(x : H)‖ ^ 2 := by
    have hshift : (0 + 1) * ‖(x : H)‖ ^ 2 = ‖(x : H)‖ ^ 2 := by ring
    rw [hshift]
    exact add_nonneg (hq_re x) (sq_nonneg ‖(x : H)‖)
  have hr_nonneg (x : D) :
      0 ≤ RCLike.re ((q + b) x x) + (c + 1) * ‖(x : H)‖ ^ 2 := by
    have hsum := add_le_add_left (hsemi x) ((c + 1) * ‖(x : H)‖ ^ 2)
    have heq : -c * ‖(x : H)‖ ^ 2 + (c + 1) * ‖(x : H)‖ ^ 2 = ‖(x : H)‖ ^ 2 := by ring
    rw [heq] at hsum
    exact (sq_nonneg ‖(x : H)‖).trans hsum
  -- `(1 - a)` times the unperturbed form square sits under the perturbed one.
  have hlow (x : D) :
      (1 - a) * formGraphNorm q 0 x ^ 2 ≤ formGraphNorm (q + b) c x ^ 2 := by
    rw [formGraphNorm_sq q 0 x (hq_nonneg x), formGraphNorm_sq (q + b) c x (hr_nonneg x)]
    have hcoeff : (1 - a) * ‖(x : H)‖ ^ 2 ≤ ‖(x : H)‖ ^ 2 := by
      calc
        (1 - a) * ‖(x : H)‖ ^ 2 ≤ 1 * ‖(x : H)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (sub_le_self 1 ha) (sq_nonneg ‖(x : H)‖)
        _ = ‖(x : H)‖ ^ 2 := one_mul _
    calc
      (1 - a) * (RCLike.re (q x x) + (0 + 1) * ‖(x : H)‖ ^ 2)
          = (1 - a) * RCLike.re (q x x) + (1 - a) * ‖(x : H)‖ ^ 2 := by ring
      _ ≤ (1 - a) * RCLike.re (q x x) + ‖(x : H)‖ ^ 2 := add_le_add_right hcoeff _
      _ = (1 - a) * RCLike.re (q x x) - c * ‖(x : H)‖ ^ 2 + (c + 1) * ‖(x : H)‖ ^ 2 := by ring
      _ ≤ RCLike.re ((q + b) x x) + (c + 1) * ‖(x : H)‖ ^ 2 :=
        add_le_add_left (hre_lower x) _
  have hre_upper (x : D) :
      RCLike.re ((q + b) x x) ≤ (1 + a) * RCLike.re (q x x) + c * ‖(x : H)‖ ^ 2 := by
    calc
      RCLike.re ((q + b) x x) = RCLike.re (q x x) + RCLike.re (b x x) := by
        rw [hadd x x, map_add]
      _ ≤ RCLike.re (q x x) + ‖b x x‖ := add_le_add_right (RCLike.re_le_norm (b x x)) _
      _ ≤ RCLike.re (q x x) + (a * RCLike.re (q x x) + c * ‖(x : H)‖ ^ 2) :=
        add_le_add_right (hbound x) _
      _ = (1 + a) * RCLike.re (q x x) + c * ‖(x : H)‖ ^ 2 := by ring
  -- `K` dominates both `1 + a` and `2c + 1`.
  let K : ℝ := (1 + a) + (2 * c + 1)
  have hKnonneg : 0 ≤ K := by
    change 0 ≤ (1 + a) + (2 * c + 1)
    exact add_nonneg (add_nonneg zero_le_one ha)
      (add_nonneg (mul_nonneg zero_le_two hc) zero_le_one)
  have hup (x : D) : formGraphNorm (q + b) c x ^ 2 ≤ K * formGraphNorm q 0 x ^ 2 := by
    rw [formGraphNorm_sq (q + b) c x (hr_nonneg x), formGraphNorm_sq q 0 x (hq_nonneg x)]
    have hleft : 1 + a ≤ K := by
      change 1 + a ≤ (1 + a) + (2 * c + 1)
      exact le_add_of_nonneg_right (add_nonneg (mul_nonneg zero_le_two hc) zero_le_one)
    have hright : 2 * c + 1 ≤ K := by
      change 2 * c + 1 ≤ (1 + a) + (2 * c + 1)
      exact le_add_of_nonneg_left (add_nonneg zero_le_one ha)
    calc
      RCLike.re ((q + b) x x) + (c + 1) * ‖(x : H)‖ ^ 2
          ≤ (1 + a) * RCLike.re (q x x) + c * ‖(x : H)‖ ^ 2 + (c + 1) * ‖(x : H)‖ ^ 2 :=
            add_le_add_left (hre_upper x) _
      _ = (1 + a) * RCLike.re (q x x) + (2 * c + 1) * ‖(x : H)‖ ^ 2 := by ring
      _ ≤ K * RCLike.re (q x x) + K * ‖(x : H)‖ ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_right hleft (hq_re x))
          (mul_le_mul_of_nonneg_right hright (sq_nonneg ‖(x : H)‖))
      _ = K * (RCLike.re (q x x) + (0 + 1) * ‖(x : H)‖ ^ 2) := by ring
  have hq_le_hr (x : D) :
      formGraphNorm q 0 x ≤ formGraphNorm (q + b) c x / Real.sqrt (1 - a) := by
    have hsq : formGraphNorm q 0 x ^ 2 ≤ formGraphNorm (q + b) c x ^ 2 / (1 - a) := by
      rw [le_div_iff₀' h1a]
      exact hlow x
    calc
      formGraphNorm q 0 x = Real.sqrt (formGraphNorm q 0 x ^ 2) :=
        (Real.sqrt_sq (Real.sqrt_nonneg _)).symm
      _ ≤ Real.sqrt (formGraphNorm (q + b) c x ^ 2 / (1 - a)) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (formGraphNorm (q + b) c x ^ 2) / Real.sqrt (1 - a) :=
        Real.sqrt_div (sq_nonneg _) (1 - a)
      _ = formGraphNorm (q + b) c x / Real.sqrt (1 - a) := by
        rw [Real.sqrt_sq (x := formGraphNorm (q + b) c x) (Real.sqrt_nonneg _)]
  have hr_le_hq (x : D) :
      formGraphNorm (q + b) c x ≤ Real.sqrt K * formGraphNorm q 0 x := by
    calc
      formGraphNorm (q + b) c x = Real.sqrt (formGraphNorm (q + b) c x ^ 2) :=
        (Real.sqrt_sq (Real.sqrt_nonneg _)).symm
      _ ≤ Real.sqrt (K * formGraphNorm q 0 x ^ 2) := Real.sqrt_le_sqrt (hup x)
      _ = Real.sqrt K * Real.sqrt (formGraphNorm q 0 x ^ 2) := Real.sqrt_mul hKnonneg _
      _ = Real.sqrt K * formGraphNorm q 0 x := by
        rw [Real.sqrt_sq (x := formGraphNorm q 0 x) (Real.sqrt_nonneg _)]
  -- Cauchy sequences and convergent sequences transfer across the equivalent form norms.
  have hcomplete : IsCompleteFormDomain (q + b) c := by
    intro u hu
    have hsqrt_pos : 0 < Real.sqrt (1 - a) := Real.sqrt_pos.mpr h1a
    have hu_q : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
        formGraphNorm q 0 (u m - u n) < ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hu (ε * Real.sqrt (1 - a)) (mul_pos hε hsqrt_pos)
      refine ⟨N, fun m n hm hn ↦ ?_⟩
      calc
        formGraphNorm q 0 (u m - u n)
            ≤ formGraphNorm (q + b) c (u m - u n) / Real.sqrt (1 - a) := hq_le_hr _
        _ < ε * Real.sqrt (1 - a) / Real.sqrt (1 - a) :=
          div_lt_div_of_pos_right (hN m n hm hn) hsqrt_pos
        _ = ε := mul_div_cancel_right₀ ε hsqrt_pos.ne'
    obtain ⟨x, hx⟩ := hq_complete u hu_q
    refine ⟨x, squeeze_zero (fun _ ↦ Real.sqrt_nonneg _) (fun n ↦ hr_le_hq (u n - x)) ?_⟩
    simpa [mul_zero] using Filter.Tendsto.const_mul (Real.sqrt K) hx
  exact ⟨hc, hsymm, hsemi, hcomplete⟩

end CKMA
