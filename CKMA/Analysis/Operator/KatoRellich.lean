/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.KatoRellich

/-!
# Cores of relatively bounded self-adjoint perturbations

The Kato–Rellich perturbation acts on an explicit linear partial-map domain. TauCeti's convention
is `‖Bx‖ ≤ a‖x‖ + b‖Ax‖`, so the coefficient restricted below one is `b`. Every core of the
unperturbed self-adjoint operator remains a core after perturbation, and restriction to such a
core is essentially self-adjoint. The closure corollary uses TauCeti's self-adjoint perturbation
theorem together with the core identity. Source: GAPS 22.32.
-/

@[expose] public section

noncomputable section

namespace CKMA

open LinearPMap

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Product distance of graph points of `A + B`, controlled by the graph distance of `A`.
The constants `a` and `b` are nonnegative, so the factor `a + 1 + b` is at least one. -/
private theorem dist_add_graph_le_of_isRelativelyBounded {A B : H →ₗ.[𝕜] H} {a b : ℝ}
    (hAB : B.IsRelativelyBounded A a b) (ha : 0 ≤ a) (hb : 0 ≤ b) (x y : (A + B).domain) :
    dist ((x : H), (A + B) x) ((y : H), (A + B) y) ≤
      (a + 1 + b) *
        dist ((x : H), A ⟨(x : H), hAB.domain_add ▸ x.2⟩)
          ((y : H), A ⟨(y : H), hAB.domain_add ▸ y.2⟩) := by
  let xA : A.domain := ⟨(x : H), hAB.domain_add ▸ x.2⟩
  let yA : A.domain := ⟨(y : H), hAB.domain_add ▸ y.2⟩
  let xB : B.domain := ⟨(x : H), hAB.domain_le xA.2⟩
  let yB : B.domain := ⟨(y : H), hAB.domain_le yA.2⟩
  have hEq : (⟨xA - yA, hAB.domain_le (xA - yA).2⟩ : B.domain) = xB - yB := by
    apply Subtype.ext
    rfl
  have hB : ‖B xB - B yB‖ ≤ a * ‖(x : H) - (y : H)‖ + b * ‖A xA - A yA‖ := by
    rw [← B.map_sub xB yB, ← hEq, ← A.map_sub xA yA]
    exact hAB.norm_apply_le (xA - yA)
  have hdiff : (A + B) x - (A + B) y = (A xA - A yA) + (B xB - B yB) := by
    rw [add_apply A B x, add_apply A B y]
    abel
  have hL : dist ((x : H), (A + B) x) ((y : H), (A + B) y) =
      max ‖(x : H) - (y : H)‖ ‖(A + B) x - (A + B) y‖ := by
    rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm]
  have hR : dist ((x : H), A xA) ((y : H), A yA) =
      max ‖(x : H) - (y : H)‖ ‖A xA - A yA‖ := by
    rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm]
  rw [hL, hR, hdiff]
  change max ‖(x : H) - (y : H)‖ ‖(A xA - A yA) + (B xB - B yB)‖ ≤
    (a + 1 + b) * max ‖(x : H) - (y : H)‖ ‖A xA - A yA‖
  let dx : ℝ := ‖(x : H) - (y : H)‖
  let dA : ℝ := ‖A xA - A yA‖
  let dS : ℝ := ‖(A xA - A yA) + (B xB - B yB)‖
  change max dx dS ≤ (a + 1 + b) * max dx dA
  have hdS : dS ≤ a * dx + (1 + b) * dA := by
    have hsum_le : dS ≤ ‖A xA - A yA‖ + ‖B xB - B yB‖ := by
      simpa [dS] using norm_add_le (A xA - A yA) (B xB - B yB)
    have hrec : ‖A xA - A yA‖ + ‖B xB - B yB‖ ≤ dA + (a * dx + b * dA) := by
      have hB' : ‖B xB - B yB‖ ≤ a * dx + b * dA := by simpa [dx, dA] using hB
      simpa [dA] using add_le_add_left hB' ‖A xA - A yA‖
    calc dS ≤ ‖A xA - A yA‖ + ‖B xB - B yB‖ := hsum_le
      _ ≤ dA + (a * dx + b * dA) := hrec
      _ = a * dx + (1 + b) * dA := by ring
  have hdx0 : 0 ≤ dx := norm_nonneg ((x : H) - (y : H))
  have hmax : 0 ≤ max dx dA := le_trans hdx0 (le_max_left _ _)
  have hdx : dx ≤ (a + 1 + b) * max dx dA := by
    calc dx ≤ max dx dA := le_max_left _ _
      _ ≤ (a + 1 + b) * max dx dA := le_mul_of_one_le_left hmax (by linarith)
  have hlin : a * dx + (1 + b) * dA ≤ (a + 1 + b) * max dx dA := by
    have h1 : a * dx ≤ a * max dx dA := mul_le_mul_of_nonneg_left (le_max_left _ _) ha
    have h2 : (1 + b) * dA ≤ (1 + b) * max dx dA :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)
    calc a * dx + (1 + b) * dA ≤ a * max dx dA + (1 + b) * max dx dA := add_le_add h1 h2
      _ = (a + 1 + b) * max dx dA := by ring
  calc max dx dS ≤ max dx (a * dx + (1 + b) * dA) := max_le_max le_rfl hdS
    _ ≤ (a + 1 + b) * max dx dA := max_le hdx hlin

/-- **22.32**: every core of `A` is a core of its Kato–Rellich perturbation.
TauCeti uses `‖Bx‖ ≤ a‖x‖ + b‖Ax‖`, so `b`, rather than `a`, must be less than one. -/
theorem hasCore_add_of_isRelativelyBounded {A B : H →ₗ.[𝕜] H}
    (hA : IsSelfAdjoint A) (hB : B.IsFormalAdjoint B) {a b : ℝ}
    (hAB : B.IsRelativelyBounded A a b) (hb : b < 1) {D : Submodule 𝕜 H}
    (hD : A.HasCore D) : (A + B).HasCore D := by
  -- Self-adjointness supplies the closedness that turns graph density into `HasCore`.
  have hsum : IsSelfAdjoint (A + B) := hA.add_of_isRelativelyBounded hB hAB hb
  -- Nonnegative constants, as in TauCeti's `IsSelfAdjoint.add_of_isRelativelyBounded`.
  let a' : ℝ := max a 0
  let b' : ℝ := max b 0
  have ha' : 0 ≤ a' := le_max_right a 0
  have hb' : 0 ≤ b' := le_max_right b 0
  have hAB' : B.IsRelativelyBounded A a' b' :=
    hAB.mono (le_max_left a 0) (le_max_left b 0)
  have hdom : D ≤ (A + B).domain := hD.le_domain.trans (le_of_eq hAB.domain_add.symm)
  refine ⟨hdom, ?_⟩
  apply eq_of_eq_graph
  have hgraph : ((A + B).domRestrict D).graph.topologicalClosure = (A + B).graph := by
    refine le_antisymm ?_ ?_
    · rw [← hsum.isClosed.submodule_topologicalClosure_eq]
      exact Submodule.topologicalClosure_mono (le_graph_of_le domRestrict_le)
    intro p hp
    obtain ⟨x, hx1, hx2⟩ := (mem_graph_iff (A + B)).mp hp
    have hp_eq : p = ((x : H), (A + B) x) := Prod.ext hx1.symm hx2.symm
    rw [hp_eq]
    change ((x : H), (A + B) x) ∈ closure (((A + B).domRestrict D).graph : Set (H × H))
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hCpos : 0 < a' + 1 + b' := by linarith
    let δ : ℝ := ε / (a' + 1 + b')
    have hδ : 0 < δ := div_pos hε hCpos
    let xA : A.domain := ⟨(x : H), hAB'.domain_add ▸ x.2⟩
    have hcore : ((x : H), A xA) ∈ closure (((A.domRestrict D).graph : Set (H × H))) := by
      change ((x : H), A xA) ∈ (A.domRestrict D).graph.topologicalClosure
      have hclA : (A.domRestrict D).IsClosable :=
        hA.isClosed.isClosable.leIsClosable domRestrict_le
      rw [hclA.graph_closure_eq_closure_graph, hD.closure_eq]
      exact mem_graph _ xA
    rw [Metric.mem_closure_iff] at hcore
    obtain ⟨q, hq, hdist⟩ := hcore δ hδ
    obtain ⟨y, hy1, hy2⟩ := (mem_graph_iff (A.domRestrict D)).mp hq
    have hyA : (y : H) ∈ A.domain := y.2.2
    have hyD : (y : H) ∈ D := y.2.1
    have hyB : (y : H) ∈ B.domain := hAB.domain_le hyA
    let yDom : (A + B).domain := ⟨(y : H), ⟨hyA, hyB⟩⟩
    let yRes : ((A + B).domRestrict D).domain := ⟨(y : H), ⟨hyD, yDom.2⟩⟩
    refine ⟨((yRes : H), (A + B).domRestrict D yRes), mem_graph _ yRes, ?_⟩
    have hpoint : ((yRes : H), (A + B).domRestrict D yRes) =
        ((yDom : H), (A + B) yDom) := by
      apply Prod.ext
      · rfl
      · exact domRestrict_apply rfl
    rw [hpoint]
    have hdistA : dist ((x : H), A ⟨(x : H), hAB'.domain_add ▸ x.2⟩)
        ((yDom : H), A ⟨(yDom : H), hAB'.domain_add ▸ yDom.2⟩) < δ := by
      have hAy : (A.domRestrict D) y = A ⟨(y : H), hyA⟩ := domRestrict_apply rfl
      have hAy' : A ⟨(y : H), hyA⟩ = A ⟨(yDom : H), hAB'.domain_add ▸ yDom.2⟩ := by
        congr 1
      have hq_eq : q = ((yDom : H), A ⟨(yDom : H), hAB'.domain_add ▸ yDom.2⟩) := by
        refine Prod.ext hy1.symm ?_
        rw [← hAy', ← hAy]
        exact hy2.symm
      simpa [hq_eq, xA] using hdist
    have hlip := dist_add_graph_le_of_isRelativelyBounded hAB' ha' hb' x yDom
    calc dist ((x : H), (A + B) x) ((yDom : H), (A + B) yDom) ≤
          (a' + 1 + b') * dist ((x : H), A ⟨(x : H), hAB'.domain_add ▸ x.2⟩)
            ((yDom : H), A ⟨(yDom : H), hAB'.domain_add ▸ yDom.2⟩) := hlip
      _ < (a' + 1 + b') * δ := mul_lt_mul_of_pos_left hdistA hCpos
      _ = ε := mul_div_cancel₀ ε hCpos.ne'
  have hcl : ((A + B).domRestrict D).IsClosable := ⟨A + B, hgraph⟩
  rw [← hcl.graph_closure_eq_closure_graph]
  exact hgraph

/-- The restriction to any original core is essentially self-adjoint. -/
theorem isSelfAdjoint_closure_domRestrict_add {A B : H →ₗ.[𝕜] H}
    (hA : IsSelfAdjoint A) (hB : B.IsFormalAdjoint B) {a b : ℝ}
    (hAB : B.IsRelativelyBounded A a b) (hb : b < 1) {D : Submodule 𝕜 H}
    (hD : A.HasCore D) : IsSelfAdjoint ((A + B).domRestrict D).closure := by
  rw [(hasCore_add_of_isRelativelyBounded hA hB hAB hb hD).closure_eq]
  exact hA.add_of_isRelativelyBounded hB hAB hb

end CKMA
