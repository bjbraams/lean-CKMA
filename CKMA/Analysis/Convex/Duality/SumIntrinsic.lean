/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Convex.Basic
public import TauCeti.Analysis.Convex.Subdifferential
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import CKMA.Analysis.Convex.Duality.Sum
import Mathlib.Analysis.Convex.Continuous
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic

/-!
# The subdifferential sum rule under a relative-interior qualification

In a finite-dimensional normed space, if the intrinsic (relative) interiors of the finite
domains of two proper convex functions meet, then `∂(f + g)(x) = ∂f(x) + ∂g(x)` at every `x`.

The proof reduces to the continuity form of the sum rule. Let `V_f` and `V_g` be the directions
of the affine spans of the domains, and fix linear projections `P_f`, `P_g` onto them. Near
the common relative-interior point the functions `a ↦ f (x + P_f a)` and `a ↦ g (x + P_g a)` are
finite and continuous, since a convex function is continuous on the relative interior of its
domain. Adding the indicator of `V_f ⊓ V_g` recovers `a ↦ f (x + a) + g (x + a)`, so the
continuity form of the rule, applied twice, splits a subgradient of the sum. The part coming
from the indicator vanishes on `V_f ⊓ V_g`, hence splits into functionals vanishing on `V_f`
and on `V_g`, which are absorbed into the subgradients of `f` and `g`. Lower semicontinuity is
not used. Source: Rockafellar, *Convex Analysis*, Theorem 23.8; GAPS 12.21.

## Main results

* `CKMA.subdifferential_add_eq_of_intrinsicInterior`: the finite-dimensional sum rule under the
  relative-interior qualification (GAPS 12.21).
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped Pointwise Topology
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The epigraph convexity condition, evaluated at two points of the epigraph. -/
private lemma le_of_convex_epigraph {f : E → EReal}
    (hcf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) {y z : E} {r s a b : ℝ}
    (hy : f y ≤ r) (hz : f z ≤ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    f (a • y + b • z) ≤ ((a * r + b * s : ℝ) : EReal) :=
  hcf (show (y, r) ∈ {p : E × ℝ | f p.1 ≤ p.2} from hy)
    (show (z, s) ∈ {p : E × ℝ | f p.1 ≤ p.2} from hz) ha hb hab

/-- A sum of two extended reals, neither `⊥`, bounded by a real is a sum of two reals. -/
private lemma exists_coe_of_add_le {u v : EReal} {r : ℝ} (hu : u ≠ ⊥) (hv : v ≠ ⊥)
    (h : u + v ≤ r) : ∃ s t : ℝ, u = s ∧ v = t ∧ s + t ≤ r := by
  induction u using EReal.rec with
  | bot => exact absurd rfl hu
  | top => simp [EReal.top_add_of_ne_bot hv] at h
  | coe s =>
    induction v using EReal.rec with
    | bot => exact absurd rfl hv
    | top => simp at h
    | coe t => exact ⟨s, t, rfl, rfl, by exact_mod_cast h⟩

/-- Precomposition with an affine map `a ↦ x + P a` preserves convexity of the epigraph. -/
private lemma convex_epigraph_comp {f : E → EReal}
    (hcf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (x : E) (P : E →L[ℝ] E) :
    Convex ℝ {p : E × ℝ | f (x + P p.1) ≤ p.2} := by
  intro p hp q hq a b ha hb hab
  have h := le_of_convex_epigraph hcf (y := x + P p.1) (z := x + P q.1) hp hq ha hb hab
  have harg : x + P (a • p.1 + b • q.1) = a • (x + P p.1) + b • (x + P q.1) := by
    rw [map_add, map_smul, map_smul]
    nth_rewrite 1 [← one_smul ℝ x, ← hab]
    module
  show f (x + P (a • p.1 + b • q.1)) ≤ ((a * p.2 + b * q.2 : ℝ) : EReal)
  rw [harg]
  exact h

/-- The sum of two functions that never take the value `⊥` and have convex epigraphs has a
convex epigraph. -/
private lemma convex_epigraph_add {f g : E → EReal} (hf : ∀ y, f y ≠ ⊥) (hg : ∀ y, g y ≠ ⊥)
    (hcf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hcg : Convex ℝ {p : E × ℝ | g p.1 ≤ p.2}) :
    Convex ℝ {p : E × ℝ | f p.1 + g p.1 ≤ p.2} := by
  intro p hp q hq a b ha hb hab
  obtain ⟨s₁, t₁, hs₁, ht₁, h₁⟩ := exists_coe_of_add_le (hf _) (hg _) hp
  obtain ⟨s₂, t₂, hs₂, ht₂, h₂⟩ := exists_coe_of_add_le (hf _) (hg _) hq
  have hF := le_of_convex_epigraph hcf hs₁.le hs₂.le ha hb hab
  have hG := le_of_convex_epigraph hcg (r := p.2 - s₁) (s := q.2 - s₂)
    (ht₁.trans_le (EReal.coe_le_coe_iff.mpr (by linarith)))
    (ht₂.trans_le (EReal.coe_le_coe_iff.mpr (by linarith))) ha hb hab
  show f (a • p.1 + b • q.1) + g (a • p.1 + b • q.1) ≤ ((a * p.2 + b * q.2 : ℝ) : EReal)
  refine (add_le_add hF hG).trans_eq ?_
  rw [← EReal.coe_add]
  congr 1
  ring

/-- Indicator of a submodule in the extended-real sense: `0` on `W` and `⊤` off `W`. -/
private def subspaceIndicator (W : Submodule ℝ E) : E → EReal :=
  ((W : Set E)ᶜ).indicator fun _ => ⊤

private lemma subspaceIndicator_of_mem {W : Submodule ℝ E} {a : E} (ha : a ∈ W) :
    subspaceIndicator W a = 0 :=
  indicator_of_notMem (show a ∉ ((W : Set E)ᶜ) from fun h => h ha) _

private lemma subspaceIndicator_of_notMem {W : Submodule ℝ E} {a : E} (ha : a ∉ W) :
    subspaceIndicator W a = ⊤ :=
  indicator_of_mem ha _

private lemma subspaceIndicator_ne_bot (W : Submodule ℝ E) (a : E) :
    subspaceIndicator W a ≠ ⊥ := by
  by_cases ha : a ∈ W
  · rw [subspaceIndicator_of_mem ha]
    exact EReal.zero_ne_bot
  · rw [subspaceIndicator_of_notMem ha]
    exact top_ne_bot

private lemma convex_epigraph_subspaceIndicator (W : Submodule ℝ E) :
    Convex ℝ {p : E × ℝ | subspaceIndicator W p.1 ≤ p.2} := by
  have hmem : ∀ {a : E} {r : ℝ}, subspaceIndicator W a ≤ r → a ∈ W ∧ 0 ≤ r := by
    intro a r h
    by_cases ha : a ∈ W
    · rw [subspaceIndicator_of_mem ha] at h
      exact ⟨ha, EReal.coe_nonneg.mp h⟩
    · rw [subspaceIndicator_of_notMem ha, top_le_iff] at h
      exact absurd h (EReal.coe_ne_top r)
  intro p hp q hq a b ha hb hab
  obtain ⟨hp1, hp2⟩ := hmem hp
  obtain ⟨hq1, hq2⟩ := hmem hq
  show subspaceIndicator W (a • p.1 + b • q.1) ≤ ((a * p.2 + b * q.2 : ℝ) : EReal)
  rw [subspaceIndicator_of_mem (W.add_mem (W.smul_mem a hp1) (W.smul_mem b hq1))]
  exact EReal.coe_nonneg.mpr (by positivity)

/-- A subgradient at `0` of the indicator of `W` vanishes on `W`. -/
private lemma eq_zero_of_mem_subdifferential_subspaceIndicator {W : Submodule ℝ E}
    {β : StrongDual ℝ E}
    (hβ : β ∈ TauCeti.subdifferential (topDualPairing ℝ E).flip (subspaceIndicator W) 0)
    {a : E} (ha : a ∈ W) : β a = 0 := by
  have hle : ∀ b ∈ W, β b ≤ 0 := fun b hb => by
    have h := TauCeti.add_le_of_mem_subdifferential _ hβ b
    rw [subspaceIndicator_of_mem W.zero_mem, subspaceIndicator_of_mem hb, zero_add,
      sub_zero] at h
    simpa using h
  have h1 := hle a ha
  have h2 := hle (-a) (W.neg_mem ha)
  rw [map_neg] at h2
  linarith

/-- A functional vanishing on `V ⊓ W` splits as a sum of functionals vanishing on `V` and on
`W`, in finite dimensions. -/
private lemma exists_add_of_forall_mem_inf [FiniteDimensional ℝ E] {V W : Submodule ℝ E}
    {β : StrongDual ℝ E} (hβ : ∀ a ∈ V ⊓ W, β a = 0) :
    ∃ ν μ : StrongDual ℝ E, (∀ a ∈ V, ν a = 0) ∧ (∀ a ∈ W, μ a = 0) ∧ β = ν + μ := by
  have hmem : (β : E →ₗ[ℝ] ℝ) ∈ (V ⊓ W).dualAnnihilator :=
    (Submodule.mem_dualAnnihilator _).mpr fun a ha => hβ a ha
  rw [Subspace.dualAnnihilator_inf_eq, Submodule.mem_sup] at hmem
  obtain ⟨ν, hν, μ, hμ, hsum⟩ := hmem
  refine ⟨LinearMap.toContinuousLinearMap ν, LinearMap.toContinuousLinearMap μ,
    fun a ha => ?_, fun a ha => ?_, ?_⟩
  · simpa using (Submodule.mem_dualAnnihilator _).mp hν a ha
  · simpa using (Submodule.mem_dualAnnihilator _).mp hμ a ha
  · ext a
    simpa using (LinearMap.congr_fun hsum a).symm

/-- A continuous linear projection onto a submodule of a finite-dimensional space. -/
private lemma exists_projection [FiniteDimensional ℝ E] (V : Submodule ℝ E) :
    ∃ P : E →L[ℝ] E, (∀ a, P a ∈ V) ∧ ∀ v ∈ V, P v = v := by
  obtain ⟨W, hW⟩ := V.exists_isCompl
  refine ⟨LinearMap.toContinuousLinearMap (V.projection W hW), fun a => ?_, fun v hv => ?_⟩
  · simp
  · rw [LinearMap.coe_toContinuousLinearMap']
    exact congrArg Subtype.val (Submodule.projectionOnto_apply_left hW ⟨v, hv⟩)

/-- Points of the finite domain lie in `x + V`, where `V` is the direction of its affine span. -/
private lemma sub_mem_direction {f : E → EReal} {x y : E} (hx : f x ≠ ⊤) (hy : f y ≠ ⊤) :
    y - x ∈ (affineSpan ℝ {z | f z ≠ ⊤}).direction := by
  rw [← vsub_eq_sub]
  exact AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ hy) (subset_affineSpan ℝ _ hx)

/-- Off `x + V` the function is `⊤`. -/
private lemma eq_top_of_notMem_direction {f : E → EReal} {x a : E} (hx : f x ≠ ⊤)
    (ha : a ∉ (affineSpan ℝ {z | f z ≠ ⊤}).direction) : f (x + a) = ⊤ := by
  by_contra h
  exact ha (by simpa using sub_mem_direction hx h)

/-- Near a relative-interior point `x₀` of the domain, `a ↦ f (x + P a)` is a continuous real
function, for a projection `P` onto the direction `V` of the affine span and `x` in the
domain. -/
private lemma exists_continuousAt_comp_projection [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : ∀ y, f y ≠ ⊥) (hcf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) {x x₀ : E}
    (hx : f x ≠ ⊤) (hx₀ : x₀ ∈ intrinsicInterior ℝ {y | f y ≠ ⊤}) {P : E →L[ℝ] E}
    (hPV : ∀ a, P a ∈ (affineSpan ℝ {y | f y ≠ ⊤}).direction)
    (hPid : ∀ v ∈ (affineSpan ℝ {y | f y ≠ ⊤}).direction, P v = v) :
    ∃ φ : E → ℝ, ContinuousAt φ (x₀ - x) ∧
      (fun a => f (x + P a)) =ᶠ[𝓝 (x₀ - x)] fun a => (φ a : EReal) := by
  set D : Set E := {y | f y ≠ ⊤} with hDdef
  have hφ : ConvexOn ℝ D fun y => (f y).toReal := by
    have hle : ∀ {y z : E} {a b : ℝ}, y ∈ D → z ∈ D → 0 ≤ a → 0 ≤ b → a + b = 1 →
        f (a • y + b • z) ≤ ((a * (f y).toReal + b * (f z).toReal : ℝ) : EReal) :=
      fun hy hz ha hb hab =>
        le_of_convex_epigraph hcf (EReal.le_coe_toReal hy) (EReal.le_coe_toReal hz) ha hb hab
    refine ⟨fun y hy z hz a b ha hb hab => ?_, fun y hy z hz a b ha hb hab => ?_⟩
    · exact ne_top_of_le_ne_top (EReal.coe_ne_top _) (hle hy hz ha hb hab)
    · exact (EReal.toReal_le_toReal (hle hy hz ha hb hab) (hf _) (EReal.coe_ne_top _)).trans_eq
        (EReal.toReal_coe _)
  have hcont := hφ.continuousOn_intrinsicInterior
  have hxA : x ∈ affineSpan ℝ D := subset_affineSpan ℝ D hx
  have hι0 : x + P (x₀ - x) = x₀ := by
    rw [hPid _ (sub_mem_direction hx (intrinsicInterior_subset hx₀)), add_sub_cancel]
  have hmem : ∀ a, x + P a ∈ affineSpan ℝ D := fun a => by
    simpa [vadd_eq_add, add_comm] using AffineSubspace.vadd_mem_of_mem_direction (hPV a) hxA
  obtain ⟨y, hy, hyx⟩ := mem_intrinsicInterior.1 hx₀
  let κ : E → affineSpan ℝ D := fun a => ⟨x + P a, hmem a⟩
  have hκ : Continuous κ := (continuous_const.add P.continuous).subtype_mk _
  have hκ0 : κ (x₀ - x) = y := Subtype.ext (by simp only [κ, hι0, hyx])
  have hev : ∀ᶠ a in 𝓝 (x₀ - x), x + P a ∈ intrinsicInterior ℝ D := by
    have h : κ ⁻¹' interior ((↑) ⁻¹' D) ∈ 𝓝 (x₀ - x) :=
      hκ.continuousAt.preimage_mem_nhds (by rw [hκ0]; exact isOpen_interior.mem_nhds hy)
    filter_upwards [h] with a ha
    exact ⟨κ a, ha, rfl⟩
  refine ⟨fun a => (f (x + P a)).toReal, ?_, ?_⟩
  · have h1 : Tendsto (fun a => x + P a) (𝓝 (x₀ - x)) (𝓝[intrinsicInterior ℝ D] x₀) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, hev⟩
      have h : Tendsto (fun a => x + P a) (𝓝 (x₀ - x)) (𝓝 (x + P (x₀ - x))) :=
        (continuous_const.add P.continuous).tendsto _
      rwa [hι0] at h
    have h2 := (hcont x₀ hx₀).tendsto
    unfold ContinuousAt
    simp only [hι0]
    exact h2.comp h1
  · filter_upwards [hev] with a ha
    exact (EReal.coe_toReal (intrinsicInterior_subset ha) (hf _)).symm

/-- A subgradient at `0` of `a ↦ f (x + P a)`, corrected by a functional vanishing on the
direction `V` of the affine span of the domain, is a subgradient of `f` at `x`. -/
private lemma add_mem_subdifferential_of_projection {f : E → EReal} (hf : ∀ y, f y ≠ ⊥)
    {x : E} (hx : f x ≠ ⊤) {P : E →L[ℝ] E}
    (hPid : ∀ v ∈ (affineSpan ℝ {y | f y ≠ ⊤}).direction, P v = v) {α ν : StrongDual ℝ E}
    (hα : α ∈ TauCeti.subdifferential (topDualPairing ℝ E).flip (fun a => f (x + P a)) 0)
    (hν : ∀ v ∈ (affineSpan ℝ {y | f y ≠ ⊤}).direction, ν v = 0) :
    α + ν ∈ TauCeti.subdifferential (topDualPairing ℝ E).flip f x := by
  rw [TauCeti.mem_subdifferential_iff]
  refine ⟨hf x, hx, fun y => ?_⟩
  by_cases hy : f y = ⊤
  · rw [hy]
    exact le_top
  have hv := sub_mem_direction hx hy
  have h := TauCeti.add_le_of_mem_subdifferential _ hα (y - x)
  simp only [LinearMap.flip_apply, topDualPairing_apply, map_zero, add_zero, sub_zero,
    hPid _ hv, add_sub_cancel] at h
  simpa only [LinearMap.flip_apply, topDualPairing_apply, add_apply,
    hν _ hv, add_zero] using h

/-- The hard inclusion of the relative-interior sum rule. -/
private lemma subset_subdifferential_add_of_intrinsicInterior [FiniteDimensional ℝ E]
    {f g : E → EReal} (hf : IsProperERealFunction f) (hg : IsProperERealFunction g)
    (hcf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hcg : Convex ℝ {p : E × ℝ | g p.1 ≤ p.2})
    (hri : (intrinsicInterior ℝ {y | f y ≠ ⊤} ∩ intrinsicInterior ℝ {y | g y ≠ ⊤}).Nonempty)
    (x : E) :
    TauCeti.subdifferential (topDualPairing ℝ E).flip (fun y => f y + g y) x ⊆
      TauCeti.subdifferential (topDualPairing ℝ E).flip f x +
        TauCeti.subdifferential (topDualPairing ℝ E).flip g x := by
  intro ξ hξ
  let B := (topDualPairing ℝ E).flip
  have hsum_top := TauCeti.ne_top_of_mem_subdifferential B hξ
  have hfx : f x ≠ ⊤ := fun h => hsum_top (by rw [h, EReal.top_add_of_ne_bot (hg.1 x)])
  have hgx : g x ≠ ⊤ := fun h => hsum_top (by rw [h, EReal.add_top_of_ne_bot (hf.1 x)])
  obtain ⟨x₀, hx₀f, hx₀g⟩ := hri
  set Vf := (affineSpan ℝ {y | f y ≠ ⊤}).direction with hVf
  set Vg := (affineSpan ℝ {y | g y ≠ ⊤}).direction with hVg
  obtain ⟨Pf, hPfV, hPfid⟩ := exists_projection Vf
  obtain ⟨Pg, hPgV, hPgid⟩ := exists_projection Vg
  have hzf : x₀ - x ∈ Vf := sub_mem_direction hfx (intrinsicInterior_subset hx₀f)
  have hzg : x₀ - x ∈ Vg := sub_mem_direction hgx (intrinsicInterior_subset hx₀g)
  obtain ⟨φf, hφf, heqf⟩ := exists_continuousAt_comp_projection hf.1 hcf hfx hx₀f hPfV hPfid
  obtain ⟨φg, hφg, heqg⟩ := exists_continuousAt_comp_projection hg.1 hcg hgx hx₀g hPgV hPgid
  set F : E → EReal := fun a => f (x + Pf a) with hF
  set G : E → EReal := fun a => g (x + Pg a) with hG
  set H : E → EReal := subspaceIndicator (Vf ⊓ Vg) with hH
  have hFbot : ∀ a, F a ≠ ⊥ := fun a => hf.1 _
  have hGbot : ∀ a, G a ≠ ⊥ := fun a => hg.1 _
  have hF0 : F 0 = f x := by simp [hF]
  have hG0 : G 0 = g x := by simp [hG]
  have hFz : F (x₀ - x) ≠ ⊤ := by
    simpa [hF, hPfid _ hzf] using intrinsicInterior_subset hx₀f
  have hGz : G (x₀ - x) ≠ ⊤ := by
    simpa [hG, hPgid _ hzg] using intrinsicInterior_subset hx₀g
  have hHz : H (x₀ - x) = 0 := subspaceIndicator_of_mem ⟨hzf, hzg⟩
  have hcontG : ContinuousAt G (x₀ - x) :=
    (continuous_coe_real_ereal.continuousAt.comp hφg).congr heqg.symm
  have hcontFG : ContinuousAt (fun a => F a + G a) (x₀ - x) := by
    refine (continuous_coe_real_ereal.continuousAt.comp (hφf.add hφg)).congr ?_
    filter_upwards [heqf, heqg] with a h1 h2
    simp only [Function.comp_apply, Pi.add_apply, EReal.coe_add]
    rw [← h1, ← h2]
  have hHFG : (fun a => H a + (F a + G a)) = fun a => f (x + a) + g (x + a) := by
    funext a
    by_cases ha : a ∈ Vf ⊓ Vg
    · rw [hH, subspaceIndicator_of_mem ha, zero_add, hF, hG]
      simp only [hPfid a ha.1, hPgid a ha.2]
    · rw [hH, subspaceIndicator_of_notMem ha,
        EReal.top_add_of_ne_bot (EReal.add_ne_bot_iff.mpr ⟨hFbot a, hGbot a⟩)]
      rcases not_and_or.mp (Submodule.mem_inf.not.mp ha) with haf | hag
      · rw [eq_top_of_notMem_direction hfx haf, EReal.top_add_of_ne_bot (hg.1 _)]
      · rw [eq_top_of_notMem_direction hgx hag, EReal.add_top_of_ne_bot (hf.1 _)]
  have hξ' : ξ ∈ TauCeti.subdifferential B (fun a => H a + (F a + G a)) 0 := by
    rw [hHFG, TauCeti.mem_subdifferential_iff]
    obtain ⟨h1, h2, h3⟩ := (TauCeti.mem_subdifferential_iff _).mp hξ
    refine ⟨by simpa using h1, by simpa using h2, fun a => ?_⟩
    simpa [B] using h3 (x + a)
  have hHprop : IsProperERealFunction H :=
    ⟨subspaceIndicator_ne_bot _, x₀ - x, by rw [hHz]; exact EReal.zero_ne_top⟩
  have hFGprop : IsProperERealFunction fun a => F a + G a :=
    ⟨fun a => EReal.add_ne_bot_iff.mpr ⟨hFbot a, hGbot a⟩, x₀ - x, EReal.add_ne_top hFz hGz⟩
  have hFcv : Convex ℝ {p : E × ℝ | F p.1 ≤ p.2} := convex_epigraph_comp hcf x Pf
  have hGcv : Convex ℝ {p : E × ℝ | G p.1 ≤ p.2} := convex_epigraph_comp hcg x Pg
  rw [subdifferential_add_eq hHprop hFGprop (convex_epigraph_subspaceIndicator _)
    (convex_epigraph_add hFbot hGbot hFcv hGcv)
    ⟨by rw [hHz]; exact EReal.zero_ne_top, EReal.add_ne_top hFz hGz⟩ hcontFG 0] at hξ'
  obtain ⟨β, hβ, α, hα, rfl⟩ := Set.mem_add.mp hξ'
  rw [subdifferential_add_eq ⟨hFbot, 0, by rw [hF0]; exact hfx⟩
    ⟨hGbot, 0, by rw [hG0]; exact hgx⟩ hFcv hGcv ⟨hFz, hGz⟩ hcontG 0] at hα
  obtain ⟨α₁, hα₁, α₂, hα₂, rfl⟩ := Set.mem_add.mp hα
  obtain ⟨νf, νg, hνf, hνg, hβeq⟩ := exists_add_of_forall_mem_inf (V := Vf) (W := Vg)
    fun a ha => eq_zero_of_mem_subdifferential_subspaceIndicator hβ ha
  refine Set.mem_add.mpr ⟨α₁ + νf, add_mem_subdifferential_of_projection hf.1 hfx hPfid hα₁ hνf,
    α₂ + νg, add_mem_subdifferential_of_projection hg.1 hgx hPgid hα₂ hνg, ?_⟩
  rw [hβeq]
  abel

/-- **12.21**: in finite dimensions, if the relative interiors of the finite domains of two
proper convex functions meet, then `∂(f + g)(x) = ∂f(x) + ∂g(x)` at every `x`. Lower
semicontinuity is not needed. -/
theorem subdifferential_add_eq_of_intrinsicInterior [FiniteDimensional ℝ E] {f g : E → EReal}
    (hf : IsProperERealFunction f) (hg : IsProperERealFunction g)
    (hcf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hcg : Convex ℝ {p : E × ℝ | g p.1 ≤ p.2})
    (hri : (intrinsicInterior ℝ {y | f y ≠ ⊤} ∩ intrinsicInterior ℝ {y | g y ≠ ⊤}).Nonempty)
    (x : E) :
    TauCeti.subdifferential (topDualPairing ℝ E).flip (fun y => f y + g y) x =
      TauCeti.subdifferential (topDualPairing ℝ E).flip f x +
        TauCeti.subdifferential (topDualPairing ℝ E).flip g x :=
  le_antisymm (subset_subdifferential_add_of_intrinsicInterior hf hg hcf hcg hri x)
    (subdifferential_add_subset x)

end CKMA
