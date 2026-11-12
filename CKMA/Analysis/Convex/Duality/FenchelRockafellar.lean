/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Convex.Duality.Subdifferential
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic
public import TauCeti.Data.EReal.Operations

/-!
# Fenchel–Rockafellar dual attainment

The value function `y ↦ ⨅ x, f x + g (A x + y)` of a pair of proper convex extended-real
functions is convex. A continuity point of `g` on the range of `A` makes that value function
bounded above near `0`, so it has a subgradient there. The conjugate of the value function
splits as `f⋆(-A* u) + g⋆(u)`, and Fenchel–Young therefore produces a maximizer of the dual
objective. Lower semicontinuity and completeness are not used. Source: Borwein–Lewis,
*Convex Analysis and Nonlinear Optimization*, Theorem 3.3.5; GAPS 12.39.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped Topology
open Set ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A convex real epigraph bounds a convex combination by the combination of the
real representatives. -/
private lemma le_coe_of_convex_epigraph {G : Type*} [AddCommMonoid G] [Module ℝ G]
    {f : G → EReal} (hf : Convex ℝ {p : G × ℝ | f p.1 ≤ p.2})
    {x y : G} (hx : f x ≠ ⊤) (hy : f y ≠ ⊤) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    f (a • x + b • y) ≤ ((a * (f x).toReal + b * (f y).toReal : ℝ) : EReal) := by
  simpa using hf (x := (x, (f x).toReal)) (y := (y, (f y).toReal))
    (EReal.le_coe_toReal hx) (EReal.le_coe_toReal hy) ha hb hab

/-- Subtracting a real twice returns the original extended real. -/
private lemma sub_coe_sub_cancel (a : ℝ) (x : EReal) :
    (a : EReal) - ((a : EReal) - x) = x := by
  induction x with
  | bot => simp [sub_eq_add_neg]
  | top => simp [sub_eq_add_neg]
  | coe r =>
    rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_eq_coe_iff]
    ring

/-- Subtracting a real from an infimum is the supremum of the subtracted terms. -/
private lemma coe_sub_iInf {ι : Sort*} (f : ι → EReal) (a : ℝ) :
    (a : EReal) - ⨅ i, f i = ⨆ i, (a : EReal) - f i := by
  refine le_antisymm ?_ ?_
  · rw [EReal.coe_sub_le_comm]
    refine le_iInf fun i => ?_
    rw [EReal.coe_sub_le_comm]
    exact le_iSup (fun i => (a : EReal) - f i) i
  · refine iSup_le fun i => ?_
    rw [EReal.coe_sub_le_comm, sub_coe_sub_cancel]
    exact iInf_le _ i

/-- An extended real lying under every strictly larger real is at most that real. -/
private lemma le_coe_of_forall_pos_le_add {z : EReal} {c : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → z ≤ ((c + ε : ℝ) : EReal)) : z ≤ (c : EReal) := by
  induction z with
  | bot => exact bot_le
  | top =>
    exact (EReal.coe_ne_top (c + 1) (top_le_iff.mp (h 1 one_pos))).elim
  | coe t =>
    rw [EReal.coe_le_coe_iff]
    exact le_of_forall_pos_le_add fun ε hε => EReal.coe_le_coe_iff.mp (h ε hε)

/-- An extended real lying under every negative integer is `-∞`. -/
private lemma eq_bot_of_forall_neg_coe_le {z : EReal}
    (h : ∀ n : ℕ, z ≤ (-(n : ℝ) : EReal)) : z = ⊥ := by
  induction z with
  | bot => rfl
  | top => simpa using h 0
  | coe r =>
    have hlt : -r < ↑(⌊-r⌋₊ + 1) := by
      simpa using Nat.lt_floor_add_one (-r)
    have hle : r ≤ -↑(⌊-r⌋₊ + 1) := by
      simpa using (EReal.coe_le_coe_iff.mp (h (⌊-r⌋₊ + 1)))
    linarith

/-- Negation splits across a sum of finite extended reals. -/
private lemma neg_add_eq_of_finite {a b : EReal} (ha_top : a ≠ ⊤) (ha_bot : a ≠ ⊥)
    (hb_top : b ≠ ⊤) (hb_bot : b ≠ ⊥) : -(a + b) = -a + -b := by
  rw [← EReal.coe_toReal ha_top ha_bot, ← EReal.coe_toReal hb_top hb_bot]
  simp only [← EReal.coe_add, ← EReal.coe_neg, EReal.coe_eq_coe_iff]
  ring

/-- The marginal of a primal pair, `y ↦ ⨅ x, f x + g (A x + y)`. -/
def marginalValue (f : E → EReal) (g : F → EReal) (A : E →L[ℝ] F) (y : F) : EReal :=
  ⨅ x, f x + g (A x + y)

/-- The marginal of two convex extended-real functions has convex real epigraph. -/
theorem convex_epigraph_marginalValue {f : E → EReal} {g : F → EReal}
    (A : E →L[ℝ] F) (hfbot : ∀ x, f x ≠ ⊥) (hgbot : ∀ z, g z ≠ ⊥)
    (hcf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hcg : Convex ℝ {p : F × ℝ | g p.1 ≤ p.2}) :
    Convex ℝ {p : F × ℝ | marginalValue f g A p.1 ≤ p.2} := by
  intro p1 hp1 p2 hp2 a b ha hb hab
  set y1 : F := p1.1
  set y2 : F := p2.1
  set r1 : ℝ := p1.2
  set r2 : ℝ := p2.2
  change marginalValue f g A y1 ≤ (r1 : EReal) at hp1
  change marginalValue f g A y2 ≤ (r2 : EReal) at hp2
  refine le_coe_of_forall_pos_le_add fun ε hε => ?_
  have hlt1 : marginalValue f g A y1 < ((r1 + ε : ℝ) : EReal) :=
    lt_of_le_of_lt hp1 (EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right r1 hε))
  have hlt2 : marginalValue f g A y2 < ((r2 + ε : ℝ) : EReal) :=
    lt_of_le_of_lt hp2 (EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right r2 hε))
  obtain ⟨x1, hx1⟩ := iInf_lt_iff.mp hlt1
  obtain ⟨x2, hx2⟩ := iInf_lt_iff.mp hlt2
  have hsum1_bot : f x1 + g (A x1 + y1) ≠ ⊥ := by
    simp [hfbot, hgbot]
  have hsum2_bot : f x2 + g (A x2 + y2) ≠ ⊥ := by
    simp [hfbot, hgbot]
  have hf1 : f x1 ≠ ⊤ := by
    intro h
    rw [h, EReal.top_add_of_ne_bot (hgbot _)] at hx1
    exact not_top_lt hx1
  have hg1 : g (A x1 + y1) ≠ ⊤ := by
    intro h
    rw [h, EReal.add_top_of_ne_bot (hfbot _)] at hx1
    exact not_top_lt hx1
  have hf2 : f x2 ≠ ⊤ := by
    intro h
    rw [h, EReal.top_add_of_ne_bot (hgbot _)] at hx2
    exact not_top_lt hx2
  have hg2 : g (A x2 + y2) ≠ ⊤ := by
    intro h
    rw [h, EReal.add_top_of_ne_bot (hfbot _)] at hx2
    exact not_top_lt hx2
  have hsum1 : (f x1 + g (A x1 + y1)).toReal < r1 + ε := by
    rw [← EReal.coe_lt_coe_iff, EReal.coe_toReal (ne_top_of_lt hx1) hsum1_bot]
    exact hx1
  have hsum2 : (f x2 + g (A x2 + y2)).toReal < r2 + ε := by
    rw [← EReal.coe_lt_coe_iff, EReal.coe_toReal (ne_top_of_lt hx2) hsum2_bot]
    exact hx2
  set z1 : F := A x1 + y1
  set z2 : F := A x2 + y2
  have hfmid := le_coe_of_convex_epigraph hcf hf1 hf2 ha hb hab
  have hgmid := le_coe_of_convex_epigraph hcg hg1 hg2 ha hb hab
  set xm : E := a • x1 + b • x2
  set zm : F := a • z1 + b • z2
  have hxm_top : f xm ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hfmid
  have hzm_top : g zm ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hgmid
  have hf_toReal : (f xm).toReal ≤ a * (f x1).toReal + b * (f x2).toReal := by
    rw [← EReal.coe_toReal hxm_top (hfbot xm), EReal.coe_le_coe_iff] at hfmid
    exact hfmid
  have hg_toReal : (g zm).toReal ≤ a * (g z1).toReal + b * (g z2).toReal := by
    rw [← EReal.coe_toReal hzm_top (hgbot zm), EReal.coe_le_coe_iff] at hgmid
    exact hgmid
  have hAy : A xm + (a • y1 + b • y2) = zm := by
    simp only [xm, zm, z1, z2, map_add, map_smul, smul_add]
    abel
  have hsum_le : f xm + g zm ≤
      ((a * (f x1 + g z1).toReal + b * (f x2 + g z2).toReal : ℝ) : EReal) := by
    rw [← EReal.coe_toReal hxm_top (hfbot xm), ← EReal.coe_toReal hzm_top (hgbot zm),
      ← EReal.coe_add, EReal.coe_le_coe_iff]
    calc
      (f xm).toReal + (g zm).toReal
          ≤ (a * (f x1).toReal + b * (f x2).toReal) +
            (a * (g z1).toReal + b * (g z2).toReal) :=
            add_le_add hf_toReal hg_toReal
      _ = a * ((f x1).toReal + (g z1).toReal) +
            b * ((f x2).toReal + (g z2).toReal) := by ring
      _ = a * (f x1 + g z1).toReal + b * (f x2 + g z2).toReal := by
            rw [EReal.toReal_add hf1 (hfbot x1) hg1 (hgbot z1),
              EReal.toReal_add hf2 (hfbot x2) hg2 (hgbot z2)]
  have hcomb : a * (f x1 + g z1).toReal + b * (f x2 + g z2).toReal ≤
      a * r1 + b * r2 + ε := by
    have hs1 : (f x1 + g z1).toReal ≤ r1 + ε := le_of_lt hsum1
    have hs2 : (f x2 + g z2).toReal ≤ r2 + ε := le_of_lt hsum2
    calc
      a * (f x1 + g z1).toReal + b * (f x2 + g z2).toReal
          ≤ a * (r1 + ε) + b * (r2 + ε) := by
            gcongr
      _ = a * r1 + b * r2 + ε := by
            have hmul : a * (r1 + ε) + b * (r2 + ε) =
              a * r1 + b * r2 + (a + b) * ε := by ring
            rw [hmul, hab, one_mul]
  calc
    marginalValue f g A (a • y1 + b • y2)
        ≤ f xm + g (A xm + (a • y1 + b • y2)) := iInf_le _ xm
    _ = f xm + g zm := by rw [hAy]
    _ ≤ ((a * (f x1 + g z1).toReal + b * (f x2 + g z2).toReal : ℝ) : EReal) := hsum_le
    _ ≤ ((a * r1 + b * r2 + ε : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr hcomb

/-- Continuity of `g` at `A x₀`, with both values finite, bounds the marginal near `0`. -/
theorem exists_boundedAbove_marginalValue {f : E → EReal} {g : F → EReal}
    (A : E →L[ℝ] F) {x₀ : E} (hf0 : f x₀ ≠ ⊤) (hg0 : g (A x₀) ≠ ⊤)
    (hfbot : ∀ x, f x ≠ ⊥) (hgbot : ∀ z, g z ≠ ⊥) (hcont : ContinuousAt g (A x₀)) :
    ∃ U ∈ 𝓝 (0 : F), ∃ M : ℝ, ∀ y ∈ U, marginalValue f g A y ≤ (M : EReal) := by
  obtain ⟨V, hV, N, hN⟩ :=
    exists_boundedAbove_of_continuousAt hcont hg0 (hgbot (A x₀))
  have hmap : Continuous fun y : F => A x₀ + y := continuous_const.add continuous_id
  have hpre : (fun y : F => A x₀ + y) ⁻¹' V ∈ 𝓝 (0 : F) :=
    hmap.continuousAt.preimage_mem_nhds (by simpa using hV)
  refine ⟨_, hpre, (f x₀).toReal + N, fun y hy => ?_⟩
  have hgle : g (A x₀ + y) ≤ (N : EReal) := hN _ hy
  calc
    marginalValue f g A y ≤ f x₀ + g (A x₀ + y) := iInf_le _ x₀
    _ ≤ ↑((f x₀).toReal) + ↑N :=
      add_le_add ((EReal.coe_toReal hf0 (hfbot x₀)).symm).le hgle
    _ = ↑((f x₀).toReal + N) := by rw [EReal.coe_add]

/-- A marginal that is not `-∞` at `0` and is bounded above nearby is nowhere `-∞`. -/
theorem marginalValue_ne_bot {f : E → EReal} {g : F → EReal} (A : E →L[ℝ] F)
    (hconv : Convex ℝ {p : F × ℝ | marginalValue f g A p.1 ≤ p.2})
    (hfin : marginalValue f g A 0 ≠ ⊥)
    (hbd : ∃ U ∈ 𝓝 (0 : F), ∃ M : ℝ, ∀ y ∈ U,
      marginalValue f g A y ≤ (M : EReal))
    (y1 : F) : marginalValue f g A y1 ≠ ⊥ := by
  intro hbot1
  obtain ⟨U, hU, M, hM⟩ := hbd
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  by_cases hy0 : y1 = 0
  · exact hfin (by simpa [hy0] using hbot1)
  have hnorm : 0 < ‖y1‖ := norm_pos_iff.mpr hy0
  set δ : ℝ := min (1 / 2) (ε / (2 * (‖y1‖ + 1)))
  have hδ0 : 0 < δ := by
    have hquot : 0 < ε / (2 * (‖y1‖ + 1)) := by positivity
    exact lt_min (by norm_num) hquot
  set t : ℝ := 1 - δ
  have ht0 : 0 < t := by
    have hδle : δ ≤ 1 / 2 := min_le_left _ _
    linarith
  have ht1 : t < 1 := by linarith
  set z : F := ((t - 1) / t) • y1
  have hz_lt : ‖z‖ < ε := by
    have hcoef : |(t - 1) / t| = δ / t := by
      have hsub : t - 1 = -δ := by ring
      rw [hsub, abs_div, abs_neg, abs_of_pos hδ0, abs_of_pos ht0]
    have hhalf : (1 : ℝ) / 2 ≤ t := by
      have hδle : δ ≤ 1 / 2 := min_le_left _ _
      linarith
    have hdiv : δ / t ≤ 2 * δ := by
      rw [div_le_iff₀ ht0]
      nlinarith
    have htwo : 2 * δ ≤ ε / (‖y1‖ + 1) := by
      have hmin : δ ≤ ε / (2 * (‖y1‖ + 1)) := min_le_right _ _
      calc
        2 * δ ≤ 2 * (ε / (2 * (‖y1‖ + 1))) := by gcongr
        _ = ε / (‖y1‖ + 1) := by field_simp
    have hprod : δ / t * ‖y1‖ ≤ ε * ‖y1‖ / (‖y1‖ + 1) := by
      calc
        δ / t * ‖y1‖ ≤ (2 * δ) * ‖y1‖ :=
          mul_le_mul_of_nonneg_right hdiv (norm_nonneg _)
        _ ≤ (ε / (‖y1‖ + 1)) * ‖y1‖ :=
          mul_le_mul_of_nonneg_right htwo (norm_nonneg _)
        _ = ε * ‖y1‖ / (‖y1‖ + 1) := by ring
    have hstrict : ε * ‖y1‖ / (‖y1‖ + 1) < ε := by
      have hden : 0 < ‖y1‖ + 1 := by positivity
      rw [div_lt_iff₀ hden]
      nlinarith
    rw [norm_smul, Real.norm_eq_abs, hcoef]
    exact hprod.trans_lt hstrict
  have hzU : z ∈ U := hball (Metric.mem_ball.mpr (by simpa [dist_zero_right] using hz_lt))
  have hzero : (1 - t) • y1 + t • z = 0 := by
    have hmul : t * ((t - 1) / t) = t - 1 := by field_simp
    have hsum : (1 - t) + (t - 1) = 0 := by ring
    simp [z, smul_smul, hmul, ← add_smul, hsum]
  have hle_r (r : ℝ) :
      marginalValue f g A 0 ≤ (((1 - t) * r + t * M : ℝ) : EReal) := by
    have ha : 0 ≤ 1 - t := by linarith
    have hmem := hconv (x := (y1, r)) (y := (z, M))
      (by simp [hbot1]) (hM z hzU) ha ht0.le (by ring)
    simpa [hzero] using hmem
  have hall : ∀ n : ℕ, marginalValue f g A 0 ≤ (-(n : ℝ) : EReal) := by
    intro n
    set r0 : ℝ := (-(n : ℝ) - t * M) / (1 - t) - 1
    have hr0 : (1 - t) * r0 + t * M ≤ -(n : ℝ) := by
      simp only [r0]
      field_simp
      linarith
    exact (hle_r r0).trans (EReal.coe_le_coe_iff.mpr hr0)
  exact hfin (eq_bot_of_forall_neg_coe_le hall)

/-- With both summands finite, the marginal integrand is the sum of the conjugate integrands. -/
private lemma marginal_term_eq {f : E → EReal} {g : F → EReal} (A : E →L[ℝ] F)
    (u : StrongDual ℝ F) {x : E} {z : F} (hfx : f x ≠ ⊤) (hfxb : f x ≠ ⊥)
    (hgz : g z ≠ ⊤) (hgzb : g z ≠ ⊥) :
    let y : F := z - A x
    (u y : EReal) - (f x + g (A x + y)) =
      (((-u).comp A) x : ℝ) - f x + ((u z : ℝ) - g z) := by
  intro y
  have hyz : A x + y = z := by simp [y]
  rw [hyz, ← EReal.coe_toReal hfx hfxb, ← EReal.coe_toReal hgz hgzb, ← EReal.coe_add,
    ← EReal.coe_sub]
  rw [show (u y : ℝ) = u z - u (A x) by simp [y, map_sub]]
  rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add, EReal.coe_eq_coe_iff]
  simp only [comp_apply, neg_apply]
  ring

/-- Each marginal integrand is at most `f⋆(-A* u) + g⋆(u)`. -/
private lemma marginal_term_le {f : E → EReal} {g : F → EReal} (A : E →L[ℝ] F)
    (hfbot : ∀ x, f x ≠ ⊥) (hgbot : ∀ z, g z ≠ ⊥) (u : StrongDual ℝ F) (x : E) (y : F) :
    (u y : EReal) - (f x + g (A x + y)) ≤
      TauCeti.fenchelConjugate (topDualPairing ℝ E).flip f ((-u).comp A) +
        TauCeti.fenchelConjugate (topDualPairing ℝ F).flip g u := by
  set z : F := A x + y
  by_cases hfx : f x = ⊤
  · rw [hfx, EReal.top_add_of_ne_bot (hgbot z)]
    simp
  by_cases hgz : g z = ⊤
  · rw [hgz, EReal.add_top_of_ne_bot (hfbot x)]
    simp
  have hrepr := marginal_term_eq A u hfx (hfbot x) hgz (hgbot z)
  have hrewrite :
      (u y : EReal) - (f x + g z) =
        (((-u).comp A) x : ℝ) - f x + ((u z : ℝ) - g z) := by
    simpa [z, show z - A x = y by simp [z]] using hrepr
  rw [hrewrite]
  exact add_le_add
    (TauCeti.sub_le_fenchelConjugate (topDualPairing ℝ E).flip f x ((-u).comp A))
    (TauCeti.sub_le_fenchelConjugate (topDualPairing ℝ F).flip g z u)

/-- An extended real that dominates every real number is `⊤`. -/
private lemma eq_top_of_forall_coe_le {z : EReal}
    (h : ∀ M : ℝ, (M : EReal) ≤ z) : z = ⊤ := by
  induction z with
  | top => rfl
  | bot => exact (EReal.coe_ne_bot 0 (le_bot_iff.mp (h 0))).elim
  | coe r =>
    have h1 : r + 1 ≤ r := EReal.coe_le_coe_iff.mp (h (r + 1))
    linarith

/-- A real bounded by every strictly smaller real lies under the extended real. -/
private lemma le_of_forall_pos_sub_coe_le {z : EReal} {c : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ((c - ε : ℝ) : EReal) ≤ z) : (c : EReal) ≤ z := by
  induction z with
  | top => exact le_top
  | bot => exact (EReal.coe_ne_bot (c - 1) (le_bot_iff.mp (h 1 one_pos))).elim
  | coe t =>
    rw [EReal.coe_le_coe_iff]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hε' : c - ε ≤ t := EReal.coe_le_coe_iff.mp (h ε hε)
    linarith

/-- One joint conjugate integrand lies under the conjugate of the marginal. -/
private lemma marginal_pair_le {f : E → EReal} {g : F → EReal} (A : E →L[ℝ] F)
    (hfbot : ∀ x, f x ≠ ⊥) (hgbot : ∀ z, g z ≠ ⊥) (u : StrongDual ℝ F)
    {x : E} {z : F} (hfx : f x ≠ ⊤) (hgz : g z ≠ ⊤) :
    (((-u).comp A) x : ℝ) - f x + ((u z : ℝ) - g z) ≤
      TauCeti.fenchelConjugate (topDualPairing ℝ F).flip
        (marginalValue f g A) u := by
  have hrepr := marginal_term_eq A u hfx (hfbot x) hgz (hgbot z)
  have hrepr' :
      (u (z - A x) : EReal) - (f x + g (A x + (z - A x))) =
        (((-u).comp A) x : ℝ) - f x + ((u z : ℝ) - g z) := hrepr
  have hanti :
      (u (z - A x) : EReal) - (f x + g (A x + (z - A x))) ≤
        (u (z - A x) : EReal) - marginalValue f g A (z - A x) := by
    rw [EReal.coe_sub_le_comm, sub_coe_sub_cancel]
    simpa [marginalValue] using
      iInf_le (fun x' : E => f x' + g (A x' + (z - A x))) x
  have hphi := TauCeti.sub_le_fenchelConjugate (topDualPairing ℝ F).flip
    (marginalValue f g A) (z - A x) u
  rw [LinearMap.flip_apply, topDualPairing_apply] at hphi
  exact hrepr'.symm.trans_le (hanti.trans hphi)

/-- If `f⋆(-A* u) = ⊤`, the marginal conjugate is `⊤`. -/
private lemma marginal_conjugate_top_of_f_top {f : E → EReal} {g : F → EReal}
    (A : E →L[ℝ] F) (hfbot : ∀ x, f x ≠ ⊥) (hgbot : ∀ z, g z ≠ ⊥)
    (hg_dom : ∃ z, g z ≠ ⊤) (u : StrongDual ℝ F)
    (hFt : TauCeti.fenchelConjugate (topDualPairing ℝ E).flip f ((-u).comp A) = ⊤) :
    TauCeti.fenchelConjugate (topDualPairing ℝ F).flip (marginalValue f g A) u = ⊤ := by
  refine eq_top_of_forall_coe_le fun M => ?_
  obtain ⟨z₀, hz₀⟩ := hg_dom
  set q : ℝ := u z₀ - (g z₀).toReal with hqdef
  have hq : (u z₀ : EReal) - g z₀ = (q : EReal) := by
    rw [hqdef, ← EReal.coe_toReal hz₀ (hgbot z₀), ← EReal.coe_sub, EReal.toReal_coe]
  have hlt : ((M - q : ℝ) : EReal) <
      TauCeti.fenchelConjugate (topDualPairing ℝ E).flip f ((-u).comp A) := by
    rw [hFt]
    exact lt_top_iff_ne_top.mpr (EReal.coe_ne_top (M - q))
  rw [TauCeti.fenchelConjugate_apply] at hlt
  obtain ⟨x, hx⟩ := lt_iSup_iff.mp hlt
  rw [LinearMap.flip_apply, topDualPairing_apply] at hx
  have hfx : f x ≠ ⊤ := by
    intro hfx
    rw [hfx, EReal.sub_top] at hx
    exact not_lt_bot hx
  have hpair := marginal_pair_le A hfbot hgbot u hfx hz₀
  have hgt : (M : EReal) <
      (((-u).comp A) x : ℝ) - f x + ((u z₀ : ℝ) - g z₀) := by
    rw [hq]
    have hstep := EReal.add_lt_add_right_coe hx q
    have hreal : (M - q) + q = M := by ring
    rw [← EReal.coe_add, hreal] at hstep
    exact hstep
  exact hgt.le.trans hpair

/-- If `g⋆(u) = ⊤`, the marginal conjugate is `⊤`. -/
private lemma marginal_conjugate_top_of_g_top {f : E → EReal} {g : F → EReal}
    (A : E →L[ℝ] F) (hfbot : ∀ x, f x ≠ ⊥) (hgbot : ∀ z, g z ≠ ⊥)
    (hf_dom : ∃ x, f x ≠ ⊤) (u : StrongDual ℝ F)
    (hGt : TauCeti.fenchelConjugate (topDualPairing ℝ F).flip g u = ⊤) :
    TauCeti.fenchelConjugate (topDualPairing ℝ F).flip (marginalValue f g A) u = ⊤ := by
  refine eq_top_of_forall_coe_le fun M => ?_
  obtain ⟨x₀, hx₀⟩ := hf_dom
  set p : ℝ := ((-u).comp A) x₀ - (f x₀).toReal with hpdef
  have hp : (((-u).comp A) x₀ : ℝ) - f x₀ = (p : EReal) := by
    rw [hpdef, ← EReal.coe_toReal hx₀ (hfbot x₀), ← EReal.coe_sub, EReal.toReal_coe]
  have hlt : ((M - p : ℝ) : EReal) <
      TauCeti.fenchelConjugate (topDualPairing ℝ F).flip g u := by
    rw [hGt]
    exact lt_top_iff_ne_top.mpr (EReal.coe_ne_top (M - p))
  rw [TauCeti.fenchelConjugate_apply] at hlt
  obtain ⟨z, hz⟩ := lt_iSup_iff.mp hlt
  rw [LinearMap.flip_apply, topDualPairing_apply] at hz
  have hgz : g z ≠ ⊤ := by
    intro hgz
    rw [hgz, EReal.sub_top] at hz
    exact not_lt_bot hz
  have hpair := marginal_pair_le A hfbot hgbot u hx₀ hgz
  have hgt : (M : EReal) <
      (((-u).comp A) x₀ : ℝ) - f x₀ + ((u z : ℝ) - g z) := by
    rw [hp]
    have hstep := EReal.add_lt_add_left_coe hz p
    have hreal : p + (M - p) = M := by ring
    rw [← EReal.coe_add, hreal] at hstep
    exact hstep
  exact hgt.le.trans hpair

/-- With both conjugates finite, their sum lies under the marginal conjugate. -/
private lemma marginal_conjugate_ge_add {f : E → EReal} {g : F → EReal}
    (A : E →L[ℝ] F) (hfbot : ∀ x, f x ≠ ⊥) (hgbot : ∀ z, g z ≠ ⊥)
    (hf_dom : ∃ x, f x ≠ ⊤) (hg_dom : ∃ z, g z ≠ ⊤) (u : StrongDual ℝ F)
    (hFtop : TauCeti.fenchelConjugate (topDualPairing ℝ E).flip f ((-u).comp A) ≠ ⊤)
    (hGtop : TauCeti.fenchelConjugate (topDualPairing ℝ F).flip g u ≠ ⊤) :
    TauCeti.fenchelConjugate (topDualPairing ℝ E).flip f ((-u).comp A) +
        TauCeti.fenchelConjugate (topDualPairing ℝ F).flip g u ≤
      TauCeti.fenchelConjugate (topDualPairing ℝ F).flip (marginalValue f g A) u := by
  obtain ⟨x₀, hx₀⟩ := hf_dom
  obtain ⟨z₀, hz₀⟩ := hg_dom
  have hFbot :=
    TauCeti.fenchelConjugate_ne_bot (topDualPairing ℝ E).flip hx₀ ((-u).comp A)
  have hGbot := TauCeti.fenchelConjugate_ne_bot (topDualPairing ℝ F).flip hz₀ u
  set c : ℝ :=
    (TauCeti.fenchelConjugate (topDualPairing ℝ E).flip f ((-u).comp A)).toReal
  set d : ℝ := (TauCeti.fenchelConjugate (topDualPairing ℝ F).flip g u).toReal
  have hc : TauCeti.fenchelConjugate (topDualPairing ℝ E).flip f ((-u).comp A) = ↑c :=
    (EReal.coe_toReal hFtop hFbot).symm
  have hd : TauCeti.fenchelConjugate (topDualPairing ℝ F).flip g u = ↑d :=
    (EReal.coe_toReal hGtop hGbot).symm
  have hcd :
      TauCeti.fenchelConjugate (topDualPairing ℝ E).flip f ((-u).comp A) +
        TauCeti.fenchelConjugate (topDualPairing ℝ F).flip g u = ↑(c + d) := by
    rw [hc, hd, ← EReal.coe_add]
  rw [hcd]
  refine le_of_forall_pos_sub_coe_le fun ε hε => ?_
  have hε2 : 0 < ε / 2 := by positivity
  have hltF : ((c - ε / 2 : ℝ) : EReal) <
      TauCeti.fenchelConjugate (topDualPairing ℝ E).flip f ((-u).comp A) := by
    rw [hc]
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  have hltG : ((d - ε / 2 : ℝ) : EReal) <
      TauCeti.fenchelConjugate (topDualPairing ℝ F).flip g u := by
    rw [hd]
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  rw [TauCeti.fenchelConjugate_apply] at hltF hltG
  obtain ⟨x, hx⟩ := lt_iSup_iff.mp hltF
  obtain ⟨z, hz⟩ := lt_iSup_iff.mp hltG
  rw [LinearMap.flip_apply, topDualPairing_apply] at hx hz
  have hfx : f x ≠ ⊤ := by
    intro hfx
    rw [hfx, EReal.sub_top] at hx
    exact not_lt_bot hx
  have hgz : g z ≠ ⊤ := by
    intro hgz
    rw [hgz, EReal.sub_top] at hz
    exact not_lt_bot hz
  have hpair := marginal_pair_le A hfbot hgbot u hfx hgz
  have hgt : ((c + d - ε : ℝ) : EReal) <
      (((-u).comp A) x : ℝ) - f x + ((u z : ℝ) - g z) := by
    have hadd := EReal.add_lt_add hx hz
    have hreal : (c - ε / 2) + (d - ε / 2) = c + d - ε := by ring
    rw [← EReal.coe_add, hreal] at hadd
    exact hadd
  exact hgt.le.trans hpair

/-- The conjugate of the marginal splits into the two Fenchel conjugates. -/
theorem fenchelConjugate_marginalValue {f : E → EReal} {g : F → EReal}
    (A : E →L[ℝ] F) (hfbot : ∀ x, f x ≠ ⊥) (hgbot : ∀ z, g z ≠ ⊥)
    (hf_dom : ∃ x, f x ≠ ⊤) (hg_dom : ∃ z, g z ≠ ⊤) (u : StrongDual ℝ F) :
    TauCeti.fenchelConjugate (topDualPairing ℝ F).flip (marginalValue f g A) u =
      TauCeti.fenchelConjugate (topDualPairing ℝ E).flip f ((-u).comp A) +
        TauCeti.fenchelConjugate (topDualPairing ℝ F).flip g u := by
  refine le_antisymm ?_ ?_
  · rw [TauCeti.fenchelConjugate_apply]
    refine iSup_le fun y => ?_
    rw [LinearMap.flip_apply, topDualPairing_apply, marginalValue]
    rw [coe_sub_iInf (fun x => f x + g (A x + y)) (u y)]
    refine iSup_le fun x => ?_
    exact marginal_term_le A hfbot hgbot u x y
  · by_cases hGt : TauCeti.fenchelConjugate (topDualPairing ℝ F).flip g u = ⊤
    · have hFbot :
          TauCeti.fenchelConjugate (topDualPairing ℝ E).flip f ((-u).comp A) ≠ ⊥ := by
        obtain ⟨x₀, hx₀⟩ := hf_dom
        exact TauCeti.fenchelConjugate_ne_bot (topDualPairing ℝ E).flip hx₀ _
      rw [marginal_conjugate_top_of_g_top A hfbot hgbot hf_dom u hGt, hGt,
        EReal.add_top_of_ne_bot hFbot]
    · by_cases hFt :
          TauCeti.fenchelConjugate (topDualPairing ℝ E).flip f ((-u).comp A) = ⊤
      · have hGbot : TauCeti.fenchelConjugate (topDualPairing ℝ F).flip g u ≠ ⊥ := by
          obtain ⟨z₀, hz₀⟩ := hg_dom
          exact TauCeti.fenchelConjugate_ne_bot (topDualPairing ℝ F).flip hz₀ _
        rw [marginal_conjugate_top_of_f_top A hfbot hgbot hg_dom u hFt, hFt,
          EReal.top_add_of_ne_bot hGbot]
      · exact marginal_conjugate_ge_add A hfbot hgbot hf_dom hg_dom u hFt hGt

/-- Every dual value lies under the primal marginal at `0`. -/
theorem fenchelDual_le_marginalValue {f : E → EReal} {g : F → EReal}
    (A : E →L[ℝ] F) (hfbot : ∀ x, f x ≠ ⊥) (hgbot : ∀ z, g z ≠ ⊥)
    (hf_dom : ∃ x, f x ≠ ⊤) (hg_dom : ∃ z, g z ≠ ⊤) (v : StrongDual ℝ F) :
    -TauCeti.fenchelConjugate (topDualPairing ℝ E).flip f ((-v).comp A) -
        TauCeti.fenchelConjugate (topDualPairing ℝ F).flip g v ≤
      marginalValue f g A 0 := by
  refine le_iInf fun x => ?_
  rw [add_zero]
  obtain ⟨x₁, hx₁⟩ := hf_dom
  obtain ⟨z₁, hz₁⟩ := hg_dom
  have hFbot :=
    TauCeti.fenchelConjugate_ne_bot (topDualPairing ℝ E).flip hx₁ ((-v).comp A)
  have hGbot := TauCeti.fenchelConjugate_ne_bot (topDualPairing ℝ F).flip hz₁ v
  by_cases hGt : TauCeti.fenchelConjugate (topDualPairing ℝ F).flip g v = ⊤
  · rw [hGt, EReal.sub_top]
    exact bot_le
  · by_cases hFt :
        TauCeti.fenchelConjugate (topDualPairing ℝ E).flip f ((-v).comp A) = ⊤
    · rw [hFt, EReal.neg_top, EReal.bot_sub]
      exact bot_le
    · by_cases hfx : f x = ⊤
      · rw [hfx, EReal.top_add_of_ne_bot (hgbot (A x))]
        exact le_top
      · by_cases hgx : g (A x) = ⊤
        · rw [hgx, EReal.add_top_of_ne_bot (hfbot x)]
          exact le_top
        · have hYF := TauCeti.le_add_fenchelConjugate (topDualPairing ℝ E).flip
            (hfbot x) hFbot
          have hYG := TauCeti.le_add_fenchelConjugate (topDualPairing ℝ F).flip
            (hgbot (A x)) hGbot
          rw [LinearMap.flip_apply, topDualPairing_apply, comp_apply, neg_apply] at hYF
          rw [LinearMap.flip_apply, topDualPairing_apply] at hYG
          have hFreal := (EReal.coe_toReal hFt hFbot).symm
          have hGreal := (EReal.coe_toReal hGt hGbot).symm
          have hfreal := (EReal.coe_toReal hfx (hfbot x)).symm
          have hgreal := (EReal.coe_toReal hgx (hgbot (A x))).symm
          rw [hfreal, hFreal, ← EReal.coe_add, EReal.coe_le_coe_iff] at hYF
          rw [hgreal, hGreal, ← EReal.coe_add, EReal.coe_le_coe_iff] at hYG
          rw [hFreal, hGreal, hfreal, hgreal, ← EReal.coe_neg, ← EReal.coe_sub,
            ← EReal.coe_add, EReal.coe_le_coe_iff]
          linarith

/-- **12.39**: continuity of `g` at a common finite point gives a dual maximizer. -/
theorem exists_fenchelDual_maximizer_of_qual {f : E → EReal} {g : F → EReal}
    (A : E →L[ℝ] F) (hf : IsProperERealFunction f) (hg : IsProperERealFunction g)
    (hcf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hcg : Convex ℝ {p : F × ℝ | g p.1 ≤ p.2}) {x₀ : E}
    (hfin : f x₀ ≠ ⊤ ∧ g (A x₀) ≠ ⊤) (hcont : ContinuousAt g (A x₀))
    (hval : marginalValue f g A 0 ≠ ⊥ ∧ marginalValue f g A 0 ≠ ⊤) :
    ∃ u : StrongDual ℝ F,
      marginalValue f g A 0 =
        -TauCeti.fenchelConjugate (topDualPairing ℝ E).flip f ((-u).comp A) -
          TauCeti.fenchelConjugate (topDualPairing ℝ F).flip g u ∧
        ∀ v : StrongDual ℝ F,
          -TauCeti.fenchelConjugate (topDualPairing ℝ E).flip f ((-v).comp A) -
              TauCeti.fenchelConjugate (topDualPairing ℝ F).flip g v ≤
            -TauCeti.fenchelConjugate (topDualPairing ℝ E).flip f ((-u).comp A) -
              TauCeti.fenchelConjugate (topDualPairing ℝ F).flip g u := by
  have hfbot : ∀ x, f x ≠ ⊥ := hf.1
  have hgbot : ∀ z, g z ≠ ⊥ := hg.1
  obtain ⟨x₁, hx₁⟩ := hf.2
  obtain ⟨z₁, hz₁⟩ := hg.2
  have hconv := convex_epigraph_marginalValue A hfbot hgbot hcf hcg
  have hbd :=
    exists_boundedAbove_marginalValue A hfin.1 hfin.2 hfbot hgbot hcont
  have hne : ∀ y, marginalValue f g A y ≠ ⊥ :=
    fun y => marginalValue_ne_bot A hconv hval.1 hbd y
  obtain ⟨u, hu⟩ := exists_mem_subdifferential_of_boundedAbove hconv hne hval.2 hbd
  have heq :=
    (TauCeti.mem_subdifferential_iff_add_fenchelConjugate_eq
      (topDualPairing ℝ F).flip).1 hu
  rw [LinearMap.flip_apply, topDualPairing_apply, map_zero,
    fenchelConjugate_marginalValue A hfbot hgbot ⟨x₁, hx₁⟩ ⟨z₁, hz₁⟩ u] at heq
  have hFbot :=
    TauCeti.fenchelConjugate_ne_bot (topDualPairing ℝ E).flip hx₁ ((-u).comp A)
  have hGbot := TauCeti.fenchelConjugate_ne_bot (topDualPairing ℝ F).flip hz₁ u
  set starF :=
    TauCeti.fenchelConjugate (topDualPairing ℝ E).flip f ((-u).comp A) with hstarF
  set starG := TauCeti.fenchelConjugate (topDualPairing ℝ F).flip g u with hstarG
  have hFtop : starF ≠ ⊤ := by
    intro htop
    rw [htop, EReal.top_add_of_ne_bot hGbot, EReal.add_top_of_ne_bot hval.1] at heq
    exact EReal.zero_ne_top heq.symm
  have hGtop : starG ≠ ⊤ := by
    intro htop
    rw [htop, EReal.add_top_of_ne_bot hFbot, EReal.add_top_of_ne_bot hval.1] at heq
    exact EReal.zero_ne_top heq.symm
  have hs_top : starF + starG ≠ ⊤ := EReal.add_ne_top hFtop hGtop
  have hs_bot : starF + starG ≠ ⊥ := EReal.add_ne_bot_iff.mpr ⟨hFbot, hGbot⟩
  have hφ : marginalValue f g A 0 = ↑((marginalValue f g A 0).toReal) :=
    (EReal.coe_toReal hval.2 hval.1).symm
  have hs : starF + starG = ↑((starF + starG).toReal) :=
    (EReal.coe_toReal hs_top hs_bot).symm
  have hreal :
      (marginalValue f g A 0).toReal + (starF + starG).toReal = 0 := by
    rw [hφ, hs, ← EReal.coe_add, EReal.coe_eq_coe_iff] at heq
    exact heq
  have hsplit : -(starF + starG) = -starF - starG := by
    rw [neg_add_eq_of_finite hFtop hFbot hGtop hGbot, sub_eq_add_neg]
  have hval_eq : marginalValue f g A 0 = -starF - starG := by
    rw [← hsplit, hφ, hs, ← EReal.coe_neg, EReal.coe_eq_coe_iff]
    linarith
  refine ⟨u, ?_, fun v => ?_⟩
  · simpa only [hstarF, hstarG] using hval_eq
  · have hv :=
      fenchelDual_le_marginalValue A hfbot hgbot ⟨x₁, hx₁⟩ ⟨z₁, hz₁⟩ v
    rw [hval_eq] at hv
    simpa only [hstarF, hstarG] using hv

end CKMA
