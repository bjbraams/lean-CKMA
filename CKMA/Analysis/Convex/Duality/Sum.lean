/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Convex.Duality.FenchelRockafellar

/-!
# The subdifferential sum rule

A continuity point in the intersection of the finite domains gives the Banach-space rule
`∂(f + g)(x) = ∂f(x) + ∂g(x)`. One inclusion is the sum of the supporting inequalities. The
other tilts `f` by the candidate subgradient, so that `x` minimizes the tilted sum, and reads
the splitting off the Fenchel–Rockafellar dual maximizer at the identity. Lower semicontinuity
and completeness are not used. Source: Borwein–Lewis, *Convex Analysis and Nonlinear
Optimization*, Theorem 4.1.6; GAPS 12.21.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped Pointwise
open Set ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Reassociate two extended reals and two real summands. -/
private lemma add_real_reassoc (a b : EReal) (p q : ℝ) :
    a + b + ((p + q : ℝ) : EReal) =
      (a + (p : EReal)) + (b + (q : EReal)) := by
  rw [EReal.coe_add, add_assoc, add_left_comm b (p : EReal), ← add_assoc]

/-- Subgradients of the summands add to a subgradient of the sum. -/
private lemma subdifferential_add_subset {f g : E → EReal} (x : E) :
    TauCeti.subdifferential (topDualPairing ℝ E).flip f x +
        TauCeti.subdifferential (topDualPairing ℝ E).flip g x ⊆
      TauCeti.subdifferential (topDualPairing ℝ E).flip (fun y => f y + g y) x := by
  intro ξ hξ
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_add.mp hξ
  let B := (topDualPairing ℝ E).flip
  have hfu := TauCeti.ne_top_of_mem_subdifferential B hu
  have hgu := TauCeti.ne_top_of_mem_subdifferential B hv
  have hfbot := TauCeti.ne_bot_of_mem_subdifferential B hu
  have hgbot := TauCeti.ne_bot_of_mem_subdifferential B hv
  rw [TauCeti.mem_subdifferential_iff]
  refine ⟨EReal.add_ne_bot_iff.mpr ⟨hfbot, hgbot⟩, EReal.add_ne_top hfu hgu, fun y => ?_⟩
  have h1 := TauCeti.add_le_of_mem_subdifferential B hu y
  have h2 := TauCeti.add_le_of_mem_subdifferential B hv y
  simp only [B, LinearMap.flip_apply, topDualPairing_apply] at h1 h2
  have hgoal :
      (f x + g x) + ((u + v) (y - x) : EReal) =
        (f x + (u (y - x) : EReal)) + (g x + (v (y - x) : EReal)) := by
    rw [add_apply]
    exact add_real_reassoc (f x) (g x) (u (y - x)) (v (y - x))
  calc
    (f x + g x) + ((u + v) (y - x) : EReal)
        = (f x + (u (y - x) : EReal)) + (g x + (v (y - x) : EReal)) := hgoal
    _ ≤ f y + g y := add_le_add h1 h2

/-- A subgradient of a qualified sum splits as a sum of subgradients. -/
private lemma subset_subdifferential_add {f g : E → EReal}
    (hf : IsProperERealFunction f) (hg : IsProperERealFunction g)
    (hcf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hcg : Convex ℝ {p : E × ℝ | g p.1 ≤ p.2})
    {x₀ : E} (hfin : f x₀ ≠ ⊤ ∧ g x₀ ≠ ⊤) (hcont : ContinuousAt g x₀) (x : E) :
    TauCeti.subdifferential (topDualPairing ℝ E).flip (fun y => f y + g y) x ⊆
      TauCeti.subdifferential (topDualPairing ℝ E).flip f x +
        TauCeti.subdifferential (topDualPairing ℝ E).flip g x := by
  intro ξ hξ
  let B := (topDualPairing ℝ E).flip
  have hsum_top := TauCeti.ne_top_of_mem_subdifferential B hξ
  have hfx : f x ≠ ⊤ := by
    intro h
    exact hsum_top (by rw [h, EReal.top_add_of_ne_bot (hg.1 x)])
  have hgx : g x ≠ ⊤ := by
    intro h
    exact hsum_top (by rw [h, EReal.add_top_of_ne_bot (hf.1 x)])
  let fTilt : E → EReal := fun z => f z + ((B z (-ξ) + 0 : ℝ) : EReal)
  have htilt (z : E) : fTilt z = f z + ((-ξ) z : EReal) := by
    simp [fTilt, B, LinearMap.flip_apply, topDualPairing_apply, add_zero]
  have hmin (y : E) : fTilt x + g x ≤ fTilt y + g y := by
    have hsub := TauCeti.add_le_of_mem_subdifferential B hξ y
    simp only [B, LinearMap.flip_apply, topDualPairing_apply] at hsub
    have hlin :
        ((ξ (y - x) : ℝ) : EReal) + ((-ξ) y : EReal) = ((-ξ) x : EReal) := by
      simp only [map_sub, neg_apply]
      rw [← EReal.coe_add, EReal.coe_eq_coe_iff]
      ring
    have hsub' := add_le_add_left hsub (((-ξ) y : ℝ) : EReal)
    rw [add_assoc, hlin] at hsub'
    have hre (z : E) : f z + g z + ((-ξ) z : EReal) = fTilt z + g z := by
      rw [htilt z, add_assoc, add_comm (g z), ← add_assoc]
    rw [← hre x, ← hre y]
    exact hsub'
  have hmarg :
      marginalValue fTilt g (ContinuousLinearMap.id ℝ E) 0 = fTilt x + g x := by
    rw [marginalValue]
    simp only [id_apply, add_zero]
    exact le_antisymm (iInf_le _ x) (le_iInf hmin)
  have htilt_ne_top {z : E} (hz : f z ≠ ⊤) : fTilt z ≠ ⊤ := by
    rw [htilt]
    exact EReal.add_ne_top hz (EReal.coe_ne_top _)
  have htilt_ne_bot (z : E) : fTilt z ≠ ⊥ := by
    rw [htilt]
    exact EReal.add_ne_bot_iff.mpr ⟨hf.1 z, EReal.coe_ne_bot _⟩
  have hproper : IsProperERealFunction fTilt :=
    ⟨htilt_ne_bot, x₀, htilt_ne_top hfin.1⟩
  have hconv : Convex ℝ {p : E × ℝ | fTilt p.1 ≤ p.2} := by
    simpa [fTilt, add_zero] using
      (TauCeti.convex_epigraph_add_affine_iff B (-ξ) (0 : ℝ)).2 hcf
  have hx_top : fTilt x + g x ≠ ⊤ :=
    EReal.add_ne_top (htilt_ne_top hfx) hgx
  have hx_bot : fTilt x + g x ≠ ⊥ :=
    EReal.add_ne_bot_iff.mpr ⟨htilt_ne_bot x, hg.1 x⟩
  obtain ⟨u, hu, -⟩ := exists_fenchelDual_maximizer_of_qual
    (ContinuousLinearMap.id ℝ E) hproper hg hconv hcg
    ⟨htilt_ne_top hfin.1, by simpa [id_apply] using hfin.2⟩
    (by simpa [id_apply] using hcont)
    ⟨by rw [hmarg]; exact hx_bot, by rw [hmarg]; exact hx_top⟩
  rw [hmarg, comp_id] at hu
  set S := TauCeti.fenchelConjugate B fTilt (-u) with hSdef
  set T := TauCeti.fenchelConjugate B g u with hTdef
  have hS_bot : S ≠ ⊥ :=
    TauCeti.fenchelConjugate_ne_bot B (htilt_ne_top hfx) (-u)
  have hT_bot : T ≠ ⊥ := TauCeti.fenchelConjugate_ne_bot B hgx u
  have hS_top : S ≠ ⊤ := by
    intro htop
    rw [htop, EReal.neg_top, EReal.bot_sub] at hu
    exact hx_bot hu
  have hT_top : T ≠ ⊤ := by
    intro htop
    rw [htop, EReal.sub_top] at hu
    exact hx_bot hu
  have hsum_real :
      (fTilt x).toReal + (g x).toReal = -(S.toReal + T.toReal) := by
    have hfreal := (EReal.coe_toReal (htilt_ne_top hfx) (htilt_ne_bot x)).symm
    have hgreal := (EReal.coe_toReal hgx (hg.1 x)).symm
    have hSreal := (EReal.coe_toReal hS_top hS_bot).symm
    have hTreal := (EReal.coe_toReal hT_top hT_bot).symm
    rw [hfreal, hgreal, hSreal, hTreal, ← EReal.coe_add, ← EReal.coe_neg,
      ← EReal.coe_sub, EReal.coe_eq_coe_iff] at hu
    linarith
  have hYF := TauCeti.le_add_fenchelConjugate B (htilt_ne_bot x) hS_bot
  have hYG := TauCeti.le_add_fenchelConjugate B (hg.1 x) hT_bot
  have hB (z : E) (w : StrongDual ℝ E) : (B z w : ℝ) = w z := by
    simp [B, LinearMap.flip_apply, topDualPairing_apply]
  rw [hB, ← hSdef, neg_apply] at hYF
  rw [hB, ← hTdef] at hYG
  rw [← EReal.coe_toReal (htilt_ne_top hfx) (htilt_ne_bot x),
    ← EReal.coe_toReal hS_top hS_bot, ← EReal.coe_add, EReal.coe_le_coe_iff] at hYF
  rw [← EReal.coe_toReal hgx (hg.1 x), ← EReal.coe_toReal hT_top hT_bot,
    ← EReal.coe_add, EReal.coe_le_coe_iff] at hYG
  have hYF_eq : -(u x) = (fTilt x).toReal + S.toReal := by
    linarith [hYF, hYG, hsum_real]
  have hYG_eq : u x = (g x).toReal + T.toReal := by
    linarith [hYF, hYG, hsum_real]
  have htilt_eq : fTilt x + S = ((-u) x : EReal) := by
    rw [← EReal.coe_toReal (htilt_ne_top hfx) (htilt_ne_bot x),
      ← EReal.coe_toReal hS_top hS_bot, ← EReal.coe_add, neg_apply,
      EReal.coe_eq_coe_iff]
    linarith [hYF_eq]
  have hg_eq : g x + T = (u x : EReal) := by
    rw [← EReal.coe_toReal hgx (hg.1 x), ← EReal.coe_toReal hT_top hT_bot,
      ← EReal.coe_add, EReal.coe_eq_coe_iff]
    linarith [hYG_eq]
  have hsub_tilt : -u ∈ TauCeti.subdifferential B fTilt x :=
    (TauCeti.mem_subdifferential_iff_add_fenchelConjugate_eq B).2
      (by simpa [hSdef, B, LinearMap.flip_apply, topDualPairing_apply] using htilt_eq)
  have hsub_f : -u - (-ξ) ∈ TauCeti.subdifferential B f x :=
    (TauCeti.mem_subdifferential_add_affine_iff B (-ξ) (0 : ℝ)).1 hsub_tilt
  have hsub_g : u ∈ TauCeti.subdifferential B g x :=
    (TauCeti.mem_subdifferential_iff_add_fenchelConjugate_eq B).2
      (by simpa [hTdef, B, LinearMap.flip_apply, topDualPairing_apply] using hg_eq)
  rw [Set.mem_add]
  refine ⟨-u - (-ξ), hsub_f, u, hsub_g, ?_⟩
  abel

/-- **12.21**: continuity of one summand at a common finite point gives the sum rule. -/
theorem subdifferential_add_eq {f g : E → EReal}
    (hf : IsProperERealFunction f) (hg : IsProperERealFunction g)
    (hcf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hcg : Convex ℝ {p : E × ℝ | g p.1 ≤ p.2})
    {x₀ : E} (hfin : f x₀ ≠ ⊤ ∧ g x₀ ≠ ⊤) (hcont : ContinuousAt g x₀) (x : E) :
    TauCeti.subdifferential (topDualPairing ℝ E).flip (fun y => f y + g y) x =
      TauCeti.subdifferential (topDualPairing ℝ E).flip f x +
        TauCeti.subdifferential (topDualPairing ℝ E).flip g x := by
  apply le_antisymm
  · exact subset_subdifferential_add hf hg hcf hcg hfin hcont x
  · exact subdifferential_add_subset x

end CKMA
