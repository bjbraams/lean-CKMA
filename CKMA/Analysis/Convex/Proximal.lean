/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.Convex.Subdifferential
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# Proximal points of extended-real convex functions

A proximal point is a finite minimizer of the Moreau quadratic objective on a real Hilbert
space. Proper lower semicontinuous convex functions have unique proximal points at positive
scales; the totalized proximal map selects these points whenever they exist.

The minimizer–resolvent bridge uses TauCeti's subdifferential, whose definition itself requires
a finite base value. Firm nonexpansiveness is stated directly on the proximal graph, independently
of a particular choice function. Its proof uses TauCeti's proved subgradient monotonicity
and finite-value supporting-inequality APIs. Source: GAPS 12.32.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped InnerProductSpace Topology
open Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Properness for extended-real convex analysis: no value is `-∞`, and some value is finite. -/
def IsProperERealFunction (f : H → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ ∃ x, f x ≠ ⊤

/-- Moreau's quadratic objective, with the extended-real value of `f` retained. -/
def proximalObjective (γ : ℝ) (f : H → EReal) (x y : H) : EReal :=
  f y + (‖x - y‖ ^ 2 / (2 * γ) : ℝ)

/-- A finite minimizer of the proximal objective. -/
def IsProximalPoint (γ : ℝ) (f : H → EReal) (x p : H) : Prop :=
  f p ≠ ⊥ ∧ f p ≠ ⊤ ∧ ∀ y, proximalObjective γ f x p ≤ proximalObjective γ f x y

/-- The proximal map, totalized by zero when no proximal point exists.
For proper l.s.c. convex functions and positive scales the fallback is never used. -/
def proximalMap (γ : ℝ) (f : H → EReal) (x : H) : H := by
  classical
  exact if h : ∃ p, IsProximalPoint γ f x p then Classical.choose h else 0

omit [InnerProductSpace ℝ H] in
/-- When a proximal point exists, the totalized map selects one. -/
theorem isProximalPoint_proximalMap {γ : ℝ} {f : H → EReal} {x : H}
    (h : ∃ p, IsProximalPoint γ f x p) : IsProximalPoint γ f x (proximalMap γ f x) := by
  classical
  simpa only [proximalMap, dite_eq_left h] using Classical.choose_spec h

/-- Expand the squared distance along a segment around its initial point. -/
private lemma proximal_norm_segment_sq (x p y : H) (t : ℝ) :
    ‖x - (p + t • (y - p))‖ ^ 2 =
      ‖x - p‖ ^ 2 - 2 * t * ⟪y - p, x - p⟫_ℝ + t ^ 2 * ‖y - p‖ ^ 2 := by
  have heq : x - (p + t • (y - p)) = (x - p) - t • (y - p) := by abel
  rw [heq, norm_sub_sq_real]
  simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [real_inner_comm (x - p) (y - p)]
  ring

omit [InnerProductSpace ℝ H] in
/-- A finite proximal minimizer rules out negative-infinite values everywhere. -/
theorem IsProximalPoint.apply_ne_bot {γ : ℝ} {f : H → EReal} {x p : H}
    (hp : IsProximalPoint γ f x p) (y : H) : f y ≠ ⊥ := by
  intro hy
  have h := hp.2.2 y
  simp only [proximalObjective, hy, EReal.bot_add, le_bot_iff, EReal.add_eq_bot_iff,
    EReal.coe_ne_bot, or_false] at h
  exact hp.1 h

/-- The subgradient optimality condition gives a proximal point, without a convexity assumption. -/
theorem isProximalPoint_of_mem_subdifferential {f : H → EReal} {γ : ℝ} (hγ : 0 < γ) (x p : H)
    (hp : γ⁻¹ • (x - p) ∈ TauCeti.subdifferential (innerₗ H) f p) :
    IsProximalPoint γ f x p := by
  refine ⟨TauCeti.ne_bot_of_mem_subdifferential (innerₗ H) hp,
    TauCeti.ne_top_of_mem_subdifferential (innerₗ H) hp, fun y => ?_⟩
  have heq : x - y = (x - p) - (y - p) := by abel
  have hquad : ‖x - p‖ ^ 2 / (2 * γ) ≤
      ⟪y - p, γ⁻¹ • (x - p)⟫_ℝ + ‖x - y‖ ^ 2 / (2 * γ) := by
    rw [heq, norm_sub_sq_real (x - p) (y - p), real_inner_smul_right,
      real_inner_comm (x - p) (y - p)]
    field_simp
    nlinarith [sq_nonneg ‖y - p‖]
  have hs := TauCeti.add_le_of_mem_subdifferential (innerₗ H) hp y
  change f p + (‖x - p‖ ^ 2 / (2 * γ) : ℝ) ≤
    f y + (‖x - y‖ ^ 2 / (2 * γ) : ℝ)
  calc
    _ ≤ f p + ((⟪y - p, γ⁻¹ • (x - p)⟫_ℝ +
        ‖x - y‖ ^ 2 / (2 * γ) : ℝ) : EReal) :=
      add_le_add (le_refl _) (EReal.coe_le_coe_iff.2 hquad)
    _ = (f p + (⟪y - p, γ⁻¹ • (x - p)⟫_ℝ : EReal)) +
        (‖x - y‖ ^ 2 / (2 * γ) : ℝ) := by rw [EReal.coe_add, add_assoc]
    _ ≤ _ := add_le_add hs (le_refl _)

/-- Convexity turns proximal minimality into the subgradient optimality condition. -/
theorem IsProximalPoint.mem_subdifferential {f : H → EReal}
    (hc : Convex ℝ {p : H × ℝ | f p.1 ≤ p.2}) {γ : ℝ} (hγ : 0 < γ) (x p : H)
    (hp : IsProximalPoint γ f x p) :
    γ⁻¹ • (x - p) ∈ TauCeti.subdifferential (innerₗ H) f p := by
  have hbot := hp.apply_ne_bot
  refine (TauCeti.mem_subdifferential_iff_forall_toReal_add_le
    (innerₗ H) hbot hp.2.1).2 fun y hyt => ?_
  change (f p).toReal + ⟪y - p, γ⁻¹ • (x - p)⟫_ℝ ≤ (f y).toReal
  rw [real_inner_smul_right]
  have hseg : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      (f p).toReal + γ⁻¹ * ⟪y - p, x - p⟫_ℝ ≤
        (f y).toReal + t / (2 * γ) * ‖y - p‖ ^ 2 := by
    intro t ht
    have heq : (1 - t) • p + t • y = p + t • (y - p) := by module
    have hz : f (p + t • (y - p)) ≤
        (((1 - t) * (f p).toReal + t * (f y).toReal : ℝ) : EReal) := by
      rw [← heq]
      simpa using hc (x := (p, (f p).toReal)) (y := (y, (f y).toReal))
        (by simp [EReal.coe_toReal hp.2.1 hp.1])
        (by simp [EReal.coe_toReal hyt (hbot y)])
        (by linarith [ht.2] : 0 ≤ 1 - t) ht.1.le (by ring)
    have hm := hp.2.2 (p + t • (y - p))
    change f p + (‖x - p‖ ^ 2 / (2 * γ) : ℝ) ≤
      f (p + t • (y - p)) + (‖x - (p + t • (y - p))‖ ^ 2 / (2 * γ) : ℝ) at hm
    have hbound := hm.trans (add_le_add hz (le_refl
      ((‖x - (p + t • (y - p))‖ ^ 2 / (2 * γ) : ℝ) : EReal)))
    conv_lhs at hbound => rw [← EReal.coe_toReal hp.2.1 hp.1]
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff, proximal_norm_segment_sq] at hbound
    field_simp [ne_of_gt hγ] at hbound ⊢
    apply (mul_le_mul_iff_right₀ ht.1).mp
    nlinarith only [hbound]
  have hlim : Tendsto (fun t : ℝ => (f y).toReal + t / (2 * γ) * ‖y - p‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (f y).toReal) := by
    have hc' : Continuous (fun t : ℝ => (f y).toReal + t / (2 * γ) * ‖y - p‖ ^ 2) := by
      fun_prop
    exact (hc'.tendsto' 0 _ (by simp)).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (Filter.eventually_of_mem (Ioo_mem_nhdsGT zero_lt_one) hseg)

/-- **12.32**: every proper l.s.c. convex function on a real Hilbert space has a unique
proximal point at every positive scale. No compactness assumption on strong sublevels is made. -/
theorem existsUnique_isProximalPoint [CompleteSpace H] {f : H → EReal}
    (hp : IsProperERealFunction f) (hl : LowerSemicontinuous f)
    (hc : Convex ℝ {p : H × ℝ | f p.1 ≤ p.2}) {γ : ℝ} (hγ : 0 < γ) (x : H) :
    ∃! p, IsProximalPoint γ f x p := by
  sorry

/-- The minimizer–resolvent bridge using TauCeti's existing extended-real subdifferential. -/
theorem isProximalPoint_iff_mem_subdifferential {f : H → EReal}
    (hc : Convex ℝ {p : H × ℝ | f p.1 ≤ p.2}) {γ : ℝ} (hγ : 0 < γ) (x p : H) :
    IsProximalPoint γ f x p ↔
      γ⁻¹ • (x - p) ∈ TauCeti.subdifferential (innerₗ H) f p := by
  exact ⟨IsProximalPoint.mem_subdifferential hc hγ x p,
    isProximalPoint_of_mem_subdifferential hγ x p⟩

/-- Firm nonexpansiveness, stated on the proximal graph so no choice of minimizers is needed. -/
theorem IsProximalPoint.norm_sub_sq_le_inner {f : H → EReal} {γ : ℝ} (hγ : 0 < γ)
    (hc : Convex ℝ {p : H × ℝ | f p.1 ≤ p.2}) {x y p q : H}
    (hp : IsProximalPoint γ f x p) (hq : IsProximalPoint γ f y q) :
    ‖p - q‖ ^ 2 ≤ ⟪x - y, p - q⟫_ℝ := by
  have hp' := IsProximalPoint.mem_subdifferential hc hγ x p hp
  have hq' := IsProximalPoint.mem_subdifferential hc hγ y q hq
  have hmon := TauCeti.apply_le_apply_of_mem_subdifferential (innerₗ H) hq' hp'
  change ⟪p - q, γ⁻¹ • (y - q)⟫_ℝ ≤ ⟪p - q, γ⁻¹ • (x - p)⟫_ℝ at hmon
  simp only [real_inner_smul_right] at hmon
  have hm := (mul_le_mul_iff_right₀ (inv_pos.mpr hγ)).mp hmon
  have heq : (x - p) - (y - q) = (x - y) - (p - q) := by abel
  rw [← sub_nonneg, ← inner_sub_right, heq, inner_sub_right,
    real_inner_self_eq_norm_sq, real_inner_comm (x - y) (p - q)] at hm
  linarith


/-- A convex extended-real function has at most one proximal point at a positive scale. -/
theorem IsProximalPoint.eq {f : H → EReal} {γ : ℝ} (hγ : 0 < γ)
    (hc : Convex ℝ {p : H × ℝ | f p.1 ≤ p.2}) {x p q : H}
    (hp : IsProximalPoint γ f x p) (hq : IsProximalPoint γ f x q) : p = q := by
  have h := hp.norm_sub_sq_le_inner hγ hc hq
  simp only [sub_self, inner_zero_left] at h
  have hn : ‖p - q‖ = 0 := sq_eq_zero_iff.mp (le_antisymm h (sq_nonneg _))
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

end CKMA
