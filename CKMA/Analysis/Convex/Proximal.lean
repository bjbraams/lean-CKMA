/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Convex.Basic
public import TauCeti.Analysis.Convex.Subdifferential
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import TauCeti.Analysis.Convex.FenchelMoreau
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Proximal points of extended-real convex functions

A proximal point is a finite minimizer of the Moreau quadratic objective on a real Hilbert
space. Proper lower semicontinuous convex functions have unique proximal points at positive
scales; the totalized proximal map selects these points whenever they exist.

The minimizer–resolvent bridge uses TauCeti's subdifferential, whose definition itself requires
a finite base value. Firm nonexpansiveness is stated directly on the proximal graph, independently
of a particular choice function. Its proof uses TauCeti's proved subgradient monotonicity
and finite-value supporting-inequality APIs. Existence uses TauCeti's continuous affine-minorant
theorem to bound the objective below; the Hilbert midpoint identity then makes a minimizing
sequence Cauchy. Source: GAPS 12.32.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped InnerProductSpace Topology
open Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

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

/-- The Hilbert midpoint identity for the squared distance from a fixed point. -/
private lemma proximal_midpoint_norm_sq (x u v : H) :
    ‖x - ((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v)‖ ^ 2 =
      (‖x - u‖ ^ 2 + ‖x - v‖ ^ 2) / 2 - ‖u - v‖ ^ 2 / 4 := by
  have hh := parallelogram_law_with_norm ℝ (x - u) (x - v)
  have hsum : (x - u) + (x - v) =
      (2 : ℝ) • (x - ((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v)) := by module
  have hsub : (x - u) - (x - v) = -(u - v) := by abel
  rw [hsum, hsub, norm_smul, norm_neg] at hh
  norm_num at hh
  nlinarith

/-- An affine minorant of a proper l.s.c. convex function bounds its proximal objective below. -/
private lemma exists_real_le_proximalObjective {f : H → EReal}
    (hp : IsProperERealFunction f) (hl : LowerSemicontinuous f)
    (hc : Convex ℝ {p : H × ℝ | f p.1 ≤ p.2}) {γ : ℝ} (hγ : 0 < γ) (x : H) :
    ∃ b : ℝ, ∀ y, (b : EReal) ≤ proximalObjective γ f x y := by
  obtain ⟨u, hut⟩ := hp.2
  obtain ⟨ℓ, c, hminor, -⟩ := TauCeti.exists_affine_le_of_lt hc hl hp.1
    (x₀ := u) (t := (f u).toReal - 1) (by
      rw [← EReal.coe_toReal hut (hp.1 u), EReal.coe_lt_coe_iff]
      simp)
  refine ⟨ℓ x + c - γ * ‖ℓ‖ ^ 2 / 2, fun y => ?_⟩
  have hlin : - (‖ℓ‖ * ‖x - y‖) ≤ ℓ y - ℓ x := by
    have hh := ℓ.le_opNorm (y - x)
    rw [Real.norm_eq_abs, map_sub, norm_sub_rev] at hh
    exact (abs_le.1 hh).1
  have hquad : ℓ x + c - γ * ‖ℓ‖ ^ 2 / 2 ≤
      ℓ y + c + ‖x - y‖ ^ 2 / (2 * γ) := by
    field_simp
    nlinarith [sq_nonneg (‖x - y‖ - γ * ‖ℓ‖),
      mul_le_mul_of_nonneg_left hlin hγ.le]
  calc
    _ ≤ ((ℓ y + c + ‖x - y‖ ^ 2 / (2 * γ) : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.2 hquad
    _ = (ℓ y + c : ℝ) + (‖x - y‖ ^ 2 / (2 * γ) : ℝ) := EReal.coe_add _ _
    _ ≤ _ := add_le_add (hminor y) (le_refl _)


/-- Near-minimizers of a convex proximal objective are close in the Hilbert norm. -/
private lemma proximalObjective_dist_sq_le {f : H → EReal}
    (hc : Convex ℝ {p : H × ℝ | f p.1 ≤ p.2}) (hbot : ∀ y, f y ≠ ⊥)
    {γ : ℝ} (hγ : 0 < γ) {x u v : H} {s δ ε : ℝ}
    (hfu : f u ≠ ⊤) (hfv : f v ≠ ⊤)
    (hu : (f u).toReal + ‖x - u‖ ^ 2 / (2 * γ) < s + δ)
    (hv : (f v).toReal + ‖x - v‖ ^ 2 / (2 * γ) < s + ε)
    (hs : ∀ y, (s : EReal) ≤ f y + (‖x - y‖ ^ 2 / (2 * γ) : ℝ)) :
    ‖u - v‖ ^ 2 ≤ 4 * γ * (δ + ε) := by
  let z := (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v
  have hz : f z ≤ (((1 / 2 : ℝ) * (f u).toReal +
      (1 / 2 : ℝ) * (f v).toReal : ℝ) : EReal) := by
    simpa [z] using hc (x := (u, (f u).toReal))
      (y := (v, (f v).toReal))
      (by simp [EReal.coe_toReal hfu (hbot _)])
      (by simp [EReal.coe_toReal hfv (hbot _)])
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hh : (s : EReal) ≤ f z + (‖x - z‖ ^ 2 / (2 * γ) : ℝ) := hs z
  have hh' := hh.trans (add_le_add hz (le_refl ((‖x - z‖ ^ 2 / (2 * γ) : ℝ) : EReal)))
  rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hh'
  change s ≤ 1 / 2 * (f u).toReal + 1 / 2 * (f v).toReal +
    ‖x - ((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v)‖ ^ 2 / (2 * γ) at hh'
  rw [proximal_midpoint_norm_sq] at hh'
  field_simp at hh' hu hv ⊢
  nlinarith

/-- **12.32**: every proper l.s.c. convex function on a real Hilbert space has a unique
proximal point at every positive scale. No compactness assumption on strong sublevels is made. -/
theorem existsUnique_isProximalPoint [CompleteSpace H] {f : H → EReal}
    (hp : IsProperERealFunction f) (hl : LowerSemicontinuous f)
    (hc : Convex ℝ {p : H × ℝ | f p.1 ≤ p.2}) {γ : ℝ} (hγ : 0 < γ) (x : H) :
    ∃! p, IsProximalPoint γ f x p := by
  classical
  let g := proximalObjective γ f x
  have hgl : LowerSemicontinuous g := by
    have hq : Continuous (fun y : H => ((‖x - y‖ ^ 2 / (2 * γ) : ℝ) : EReal)) :=
      continuous_coe_real_ereal.comp (by fun_prop)
    exact hl.add' hq.lowerSemicontinuous fun y =>
      EReal.continuousAt_add (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _))
  obtain ⟨b, hb⟩ := exists_real_le_proximalObjective hp hl hc hγ x
  obtain ⟨v, hv⟩ := hp.2
  have hgv : g v ≠ ⊤ := by
    dsimp [g, proximalObjective]
    rw [← EReal.coe_toReal hv (hp.1 v), ← EReal.coe_add]
    exact EReal.coe_ne_top _
  have hi_bot : (⨅ y, g y) ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot b) (le_iInf hb)
  have hi_top : (⨅ y, g y) ≠ ⊤ := ne_top_of_le_ne_top hgv (iInf_le g v)
  let s := (⨅ y, g y).toReal
  have hsi : (s : EReal) = ⨅ y, g y := EReal.coe_toReal hi_top hi_bot
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδpos (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδanti : Antitone δ := by
    intro n m hnm
    apply one_div_le_one_div_of_le (by positivity : 0 < (n : ℝ) + 1)
    exact_mod_cast Nat.add_le_add_right hnm 1
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hex (n : ℕ) : ∃ y, g y < ((s + δ n : ℝ) : EReal) := by
    apply iInf_lt_iff.1
    rw [← hsi, EReal.coe_lt_coe_iff]
    linarith [hδpos n]
  choose u hu using hex
  have hfinite (n : ℕ) : f (u n) ≠ ⊤ := by
    intro hh
    have hh' := hu n
    simp only [g, proximalObjective, hh, EReal.top_add_coe] at hh'
    exact not_lt_of_ge le_top hh'
  have hvals (n : ℕ) : (f (u n)).toReal + ‖x - u n‖ ^ 2 / (2 * γ) < s + δ n := by
    have hh := hu n
    change f (u n) + (‖x - u n‖ ^ 2 / (2 * γ) : ℝ) < ((s + δ n : ℝ) : EReal) at hh
    rw [← EReal.coe_toReal (hfinite n) (hp.1 _), ← EReal.coe_add,
      EReal.coe_lt_coe_iff] at hh
    exact hh
  have hdist (n m : ℕ) : ‖u n - u m‖ ^ 2 ≤ 4 * γ * (δ n + δ m) :=
    proximalObjective_dist_sq_le hc hp.1 hγ (hfinite n) (hfinite m) (hvals n) (hvals m)
      (fun y ↦ by rw [hsi]; exact iInf_le g y)
  have hboundlim : Tendsto (fun n => Real.sqrt (8 * γ * δ n)) atTop (𝓝 0) := by
    have hh : Tendsto (fun n => 8 * γ * δ n) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hδlim
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hh
  have hcu : CauchySeq u := by
    apply cauchySeq_of_le_tendsto_0 (fun n => Real.sqrt (8 * γ * δ n)) _ hboundlim
    intro n m N hNn hNm
    apply Real.le_sqrt_of_sq_le
    rw [dist_eq_norm]
    have hh := hdist n m
    have hn := mul_le_mul_of_nonneg_left (hδanti hNn) hγ.le
    have hm := mul_le_mul_of_nonneg_left (hδanti hNm) hγ.le
    nlinarith
  obtain ⟨p, hup⟩ := cauchySeq_tendsto_of_complete hcu
  have hple (n : ℕ) : g p ≤ ((s + δ n : ℝ) : EReal) := by
    apply (hgl.isClosed_preimage _).mem_of_tendsto hup
    filter_upwards [eventually_ge_atTop n] with m hm
    exact (hu m).le.trans (EReal.coe_le_coe_iff.2 (by linarith [hδanti hm]))
  have hmin : g p ≤ (s : EReal) := by
    have hh : Tendsto (fun n => ((s + δ n : ℝ) : EReal)) atTop (𝓝 (s : EReal)) := by
      apply continuous_coe_real_ereal.continuousAt.tendsto.comp
      simpa using tendsto_const_nhds.add hδlim
    exact ge_of_tendsto hh (Eventually.of_forall hple)
  have hpf : f p ≠ ⊤ := by
    intro hh
    simp [g, proximalObjective, hh] at hmin
  have hpmin : IsProximalPoint γ f x p := by
    refine ⟨hp.1 p, hpf, fun y => ?_⟩
    exact hmin.trans (by rw [hsi]; exact iInf_le g y)
  exact ⟨p, hpmin, fun q hq => hq.eq hγ hc hpmin⟩


end CKMA
