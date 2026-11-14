/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Convex.Uniform
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Analysis.Normed.Module.Basic

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.AlgebraicTopology.Sphere.Contractible

/-!
# Fixed points beyond contraction mappings

Brouwer and Schauder concern continuous maps of nonempty convex sets; Schauder assumes a
closed domain and relatively compact total image rather than boundedness of the domain.
Kakutani–Fan–Glicksberg allows upper hemicontinuous multifunctions with nonempty closed convex
values inside a compact convex set in a locally convex Hausdorff space.

The Browder–Göhde–Kirk statement uses uniform convexity and a nonexpansive map on a closed
bounded convex set; compactness of the map is not required. Sources: GAPS 35.12, 35.13, 35.15, and
35.21.

## Main definitions

* None (all statements use Mathlib's `Continuous`, `UpperHemicontinuousOn`, and `LipschitzWith`).

## Main results

* `CKMA.exists_fixedPoint_brouwer`: Brouwer's fixed-point theorem on a compact convex subset of a
  finite-dimensional real normed space (**35.12**).
* `CKMA.exists_fixedPoint_schauder`: Schauder's fixed-point theorem with relatively compact total
  image on a closed convex set (**35.13**).
* `CKMA.exists_fixedPoint_kakutani`: Kakutani–Fan–Glicksberg fixed-point theorem for compact convex
  subsets of locally convex spaces (**35.15**).
* `CKMA.exists_fixedPoint_nonexpansive`: Browder–Göhde–Kirk fixed-point theorem for nonexpansive
  maps on uniformly convex Banach spaces (**35.21**).

## Notation

* Standard real inner-product and norm notation from Mathlib.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology Bornology
open scoped InnerProductSpace

section Brouwer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Larger nonnegative root of the quadratic that sends `u` through `u + d` to the unit sphere. -/
private theorem rayScale_spec {u d : E} (hd : d ≠ 0) (hu : ‖u‖ ≤ 1) :
    let a := ‖d‖ ^ 2
    let b := 2 * ⟪u, d⟫_ℝ
    let c := ‖u‖ ^ 2 - 1
    let s := Real.sqrt (discrim a b c)
    let t := (-b + s) / (2 * a)
    0 ≤ t ∧ ‖u + t • d‖ = 1 ∧ (‖u + d‖ = 1 → t = 1) := by
  intro a b c s t
  have ha : 0 < a := by
    dsimp only [a]
    exact pow_pos (norm_pos_iff.mpr hd) 2
  have hc : c ≤ 0 := by
    dsimp only [c]
    have hsq : ‖u‖ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (norm_nonneg u) hu 2
    linarith
  have hdisc : 0 ≤ discrim a b c := by
    have h4a : 0 ≤ 4 * a := by positivity
    have hnegc : 0 ≤ -c := neg_nonneg.mpr hc
    simp only [discrim]
    nlinarith [sq_nonneg b, mul_nonneg h4a hnegc]
  have hs : discrim a b c = s * s := by
    simpa [s, pow_two] using (Real.sq_sqrt hdisc).symm
  have htquad : a * (t * t) + b * t + c = 0 :=
    (quadratic_eq_zero_iff ha.ne' hs t).2 (Or.inl rfl)
  have ht0 : 0 ≤ t := by
    have hble : b ^ 2 ≤ discrim a b c := by
      simp only [discrim]
      nlinarith [mul_nonneg (show 0 ≤ 4 * a by positivity) (neg_nonneg.mpr hc)]
    have hsabs : |b| ≤ s := by
      calc
        |b| = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
        _ ≤ Real.sqrt (discrim a b c) := Real.sqrt_le_sqrt hble
        _ = s := rfl
    have hnum : 0 ≤ -b + s := by
      have hbs : b ≤ s := (le_abs_self b).trans hsabs
      linarith
    exact div_nonneg hnum (mul_pos two_pos ha).le
  have hsq : ‖u + t • d‖ ^ 2 = 1 := by
    have hinner : ⟪u, t • d⟫_ℝ = t * ⟪u, d⟫_ℝ := inner_smul_right u d t
    have hsmul : ‖t • d‖ ^ 2 = t ^ 2 * ‖d‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    calc
      ‖u + t • d‖ ^ 2
          = ‖u‖ ^ 2 + 2 * ⟪u, t • d⟫_ℝ + ‖t • d‖ ^ 2 := norm_add_sq_real u (t • d)
      _ = ‖u‖ ^ 2 + 2 * (t * ⟪u, d⟫_ℝ) + t ^ 2 * ‖d‖ ^ 2 := by rw [hinner, hsmul]
      _ = 1 + (a * (t * t) + b * t + c) := by
        simp only [a, b, c, sq]
        ring
      _ = 1 := by rw [htquad, add_zero]
  have hnorm : ‖u + t • d‖ = 1 := by
    have hfactor :
        (‖u + t • d‖ - 1) * (‖u + t • d‖ + 1) = 0 := by nlinarith [hsq]
    rcases mul_eq_zero.mp hfactor with h | h
    · linarith
    · linarith [norm_nonneg (u + t • d)]
  refine ⟨ht0, hnorm, ?_⟩
  intro hball
  have hone : a * (1 * 1) + b * 1 + c = 0 := by
    have hsq1 : ‖u + d‖ ^ 2 = ‖u‖ ^ 2 + 2 * ⟪u, d⟫_ℝ + ‖d‖ ^ 2 := norm_add_sq_real u d
    have hsqball : ‖u + d‖ ^ 2 = 1 := by rw [hball, one_pow]
    simp only [a, b, c] at hsq1 ⊢
    nlinarith [hsq1, hsqball]
  rcases (quadratic_eq_zero_iff ha.ne' hs 1).1 hone with ht | ht
  · simpa [t] using ht.symm
  · have hs2 : s ^ 2 = b ^ 2 - 4 * a * c := by
      simpa [discrim, pow_two] using hs.symm
    have hprod : ((-b + s) / (2 * a)) * ((-b - s) / (2 * a)) = c / a := by
      rw [div_mul_div_comm]
      have hnum : (-b + s) * (-b - s) = 4 * a * c := by nlinarith [hs2]
      have hden : (2 * a) * (2 * a) = 4 * a * a := by ring
      rw [hnum, hden]
      field_simp [ha.ne']
    have hcle : c / a ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc ha.le
    have htprod : t = c / a := by
      dsimp only [t]
      have hprod' := hprod
      rw [← ht, mul_one] at hprod'
      exact hprod'
    have htzero : t = 0 := by nlinarith [ht0, htprod, hcle]
    have hsEq : s = b := by
      have hdiv : (-b + s) / (2 * a) = 0 := by simpa [t] using htzero
      have hsum : -b + s = 0 :=
        (div_eq_zero_iff.mp hdiv).resolve_right (mul_pos two_pos ha).ne'
      linarith
    have hb0 : 0 ≤ b := by linarith [Real.sqrt_nonneg (discrim a b c), hsEq]
    have honeNeg : (1 : ℝ) = -b / a := by
      have hrewrite : (-b - s) / (2 * a) = -b / a := by
        rw [hsEq]
        field_simp [ha.ne']
        ring
      linarith [ht, hrewrite]
    linarith [div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb0) ha.le, honeNeg]

/-- A continuous retract of a contractible space is contractible. -/
private theorem contractibleSpace_of_retraction {A X : Type*} [TopologicalSpace A]
    [TopologicalSpace X] (i : C(A, X)) (r : C(X, A)) (h : r.comp i = .id A)
    [ContractibleSpace X] : ContractibleSpace A := by
  rw [contractible_iff_id_nullhomotopic, ← h]
  have hnull : ((r.comp ((ContinuousMap.id X).comp i))).Nullhomotopic :=
    ((id_nullhomotopic X).comp_left i).comp_right r
  simpa [ContinuousMap.id_comp] using hnull

/-- The Euclidean unit sphere in positive dimension does not retract from the closed ball. -/
private theorem no_retraction_unitBall {n : ℕ} (hn : n ≠ 0)
    (r : C(↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1),
      ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)))
    (hr : r.comp (ContinuousMap.inclusion (Metric.sphere_subset_closedBall
      (x := (0 : EuclideanSpace ℝ (Fin n))) (ε := 1))) = .id _) : False := by
  let i : C(↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
      ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    ContinuousMap.inclusion (Metric.sphere_subset_closedBall
      (x := (0 : EuclideanSpace ℝ (Fin n))) (ε := 1))
  have : ContractibleSpace (↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    Metric.contractibleSpace_closedBall (x := 0) (r := 1) zero_le_one
  have hsphere : ContractibleSpace (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
    contractibleSpace_of_retraction i r hr
  have hnt : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    (Module.finrank_pos_iff (R := ℝ)).mp <| by
      rw [finrank_euclideanSpace_fin]
      exact Nat.pos_of_ne_zero hn
  exact TauCeti.not_contractibleSpace_sphere (E := EuclideanSpace ℝ (Fin n)) hsphere

/-- Brouwer's fixed-point theorem on the Euclidean closed unit ball. -/
private theorem exists_fixedPoint_unitBall {n : ℕ}
    (f : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) →
      ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
    (hf : Continuous f) :
    ∃ x, f x = x := by
  cases n with
  | zero =>
    have hsub : Subsingleton (EuclideanSpace ℝ (Fin 0)) :=
      Module.finrank_zero_iff.mp (by rw [finrank_euclideanSpace_fin])
    exact ⟨⟨0, by simp⟩, Subtype.ext (hsub.elim _ _)⟩
  | succ n =>
    by_contra hfree
    let Euc := EuclideanSpace ℝ (Fin (n + 1))
    let Ball := ↥(Metric.closedBall (0 : Euc) 1)
    let Sph := ↥(Metric.sphere (0 : Euc) 1)
    let shift : Ball → Euc := fun x => (x : Euc) - (f x : Euc)
    have hshift : Continuous shift :=
      continuous_subtype_val.sub (continuous_subtype_val.comp hf)
    have hshift0 : ∀ x, shift x ≠ 0 := by
      intro x hx
      have hx' : (x : Euc) - (f x : Euc) = 0 := by simpa [shift] using hx
      exact hfree ⟨x, Subtype.ext (sub_eq_zero.mp hx').symm⟩
    let scale : Ball → ℝ := fun x =>
      let d := shift x
      let u := (f x : Euc)
      let a := ‖d‖ ^ 2
      let b := 2 * ⟪u, d⟫_ℝ
      let c := ‖u‖ ^ 2 - 1
      (-b + Real.sqrt (discrim a b c)) / (2 * a)
    have hscale : Continuous scale := by
      have hden : Continuous fun x : Ball => 2 * ‖shift x‖ ^ 2 := by fun_prop
      have hden0 : ∀ x : Ball, 2 * ‖shift x‖ ^ 2 ≠ 0 := by
        intro x
        have hpos : 0 < ‖shift x‖ := norm_pos_iff.mpr (hshift0 x)
        positivity
      have hnum : Continuous fun x : Ball =>
          -(2 * ⟪(f x : Euc), shift x⟫_ℝ) +
            Real.sqrt ((2 * ⟪(f x : Euc), shift x⟫_ℝ) ^ 2 -
              4 * (‖shift x‖ ^ 2) * (‖(f x : Euc)‖ ^ 2 - 1)) := by
        fun_prop
      simpa [scale, discrim] using hnum.div₀ hden hden0
    let retr : Ball → Euc := fun x => (f x : Euc) + scale x • shift x
    have hretr : Continuous retr := by fun_prop
    have hnormLe : ∀ x : Ball, ‖(f x : Euc)‖ ≤ 1 := by
      intro x
      rw [← sub_zero (f x : Euc), ← mem_closedBall_iff_norm]
      exact (f x).2
    have hsph : ∀ x, retr x ∈ Metric.sphere (0 : Euc) 1 := by
      intro x
      rw [mem_sphere_iff_norm, sub_zero]
      simpa [retr, scale, shift] using
        (rayScale_spec (u := (f x : Euc)) (d := shift x) (hshift0 x) (hnormLe x)).2.1
    let rC : C(Ball, Sph) := ⟨fun x => ⟨retr x, hsph x⟩, hretr.subtype_mk hsph⟩
    have hr : rC.comp (ContinuousMap.inclusion
        (Metric.sphere_subset_closedBall (x := (0 : Euc)) (ε := 1))) = .id _ := by
      apply ContinuousMap.ext
      intro s
      apply Subtype.ext
      have hsphere : (s : Euc) ∈ Metric.sphere (0 : Euc) 1 := s.2
      have hx : ‖(s : Euc)‖ = 1 := by
        rw [← sub_zero (s : Euc), ← mem_sphere_iff_norm]
        exact hsphere
      let x : Ball := ⟨(s : Euc), Metric.sphere_subset_closedBall hsphere⟩
      have hscale1 : scale x = 1 := by
        have ht := (rayScale_spec (u := (f x : Euc)) (d := shift x) (hshift0 x)
          (hnormLe x)).2.2
        have hsum : ‖(f x : Euc) + shift x‖ = 1 := by
          have hcancel : (f x : Euc) + shift x = (s : Euc) := by simp [shift, x]
          rw [hcancel]
          exact hx
        simpa [scale, shift] using ht hsum
      change retr x = (s : Euc)
      simp only [retr, hscale1, shift]
      rw [one_smul]
      abel
    exact no_retraction_unitBall (n := n + 1) (Nat.succ_ne_zero n) rC hr

/-- A nonempty compact convex set with nonempty interior, in a finite-dimensional real space,
has the fixed-point property for continuous self-maps. -/
theorem exists_fixedPoint_of_interior {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {C : Set E} (hne : C.Nonempty)
    (hcomp : IsCompact C) (hconv : Convex ℝ C) (hinter : (interior C).Nonempty)
    (T : C → C) (hT : Continuous T) : ∃ x, T x = x := by
  by_cases h0 : Module.finrank ℝ E = 0
  · have hsub : Subsingleton E := Module.finrank_zero_iff.mp h0
    have hsubC : Subsingleton C := ⟨fun a b => Subtype.ext (Subsingleton.elim (a : E) (b : E))⟩
    obtain ⟨x, hx⟩ := hne
    exact ⟨⟨x, hx⟩, Subsingleton.elim _ _⟩
  · let n := Module.finrank ℝ E
    let Euc := EuclideanSpace ℝ (Fin n)
    have hn : n ≠ 0 := h0
    let Φ : E ≃L[ℝ] Euc :=
      ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_euclideanSpace_fin])
    let C' : Set Euc := Φ '' C
    have hconv' : Convex ℝ C' := hconv.linear_image Φ.toLinearMap
    have hcomp' : IsCompact C' := hcomp.image Φ.continuous
    have hclosed' : IsClosed C' := hcomp'.isClosed
    have hbd' : IsBounded C' := hcomp'.isBounded
    have hcoe : (Φ.toHomeomorph : E → Euc) = Φ := ContinuousLinearEquiv.coe_toHomeomorph Φ
    have hinter' : (interior C').Nonempty := by
      rw [show C' = Φ.toHomeomorph '' C by simp [C', hcoe], ← Φ.toHomeomorph.image_interior]
      exact hinter.image Φ.toHomeomorph
    obtain ⟨g, -, hg, -⟩ :=
      exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv' hinter' hbd'
    have hcl : closure C' = C' := hclosed'.closure_eq
    rw [hcl] at hg
    have hC' : Φ.toHomeomorph '' C = C' := by simp [C', hcoe]
    let e1 : C ≃ₜ C' := (Φ.toHomeomorph.image C).trans (Homeomorph.setCongr hC')
    let e2 : C' ≃ₜ g '' C' := g.image C'
    let e3 : g '' C' ≃ₜ ↥(Metric.closedBall (0 : Euc) 1) := Homeomorph.setCongr hg
    let e : C ≃ₜ ↥(Metric.closedBall (0 : Euc) 1) := e1.trans (e2.trans e3)
    let S : ↥(Metric.closedBall (0 : Euc) 1) → ↥(Metric.closedBall (0 : Euc) 1) :=
      fun y => e (T (e.symm y))
    have hS : Continuous S := e.continuous.comp (hT.comp e.symm.continuous)
    obtain ⟨y, hy⟩ := exists_fixedPoint_unitBall S hS
    refine ⟨e.symm y, ?_⟩
    apply e.injective
    simpa [S] using hy

end Brouwer

/-- **35.12**: Brouwer's theorem on a compact convex subset of a finite-dimensional real space. -/
theorem exists_fixedPoint_brouwer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {C : Set E} (hne : C.Nonempty) (hC : IsCompact C)
    (hc : Convex ℝ C) (T : C → C) (hT : Continuous T) : ∃ x : C, T x = x := by
  obtain ⟨x0, hx0⟩ := hne
  by_cases hbot : vectorSpan ℝ C = ⊥
  · have hsub : C.Subsingleton := (vectorSpan_eq_bot_iff_subsingleton ℝ).1 hbot
    have hsubC : Subsingleton C := ⟨fun a b => Subtype.ext (hsub a.2 b.2)⟩
    exact ⟨⟨x0, hx0⟩, Subsingleton.elim _ _⟩
  · let F := vectorSpan ℝ C
    have : FiniteDimensional ℝ F := inferInstance
    let C0 : Set F := {v | x0 + (v : E) ∈ C}
    have h0 : (0 : F) ∈ C0 := by simp [C0, hx0]
    have hne0 : C0.Nonempty := ⟨0, h0⟩
    have hconv0 : Convex ℝ C0 := by
      intro v hv w hw a b ha hb hab
      have hvC : x0 + (v : E) ∈ C := hv
      have hwC : x0 + (w : E) ∈ C := hw
      have hlin : x0 + (a • (v : E) + b • (w : E)) =
          a • (x0 + (v : E)) + b • (x0 + (w : E)) := by
        have hsum : a • x0 + b • x0 = x0 := by rw [← add_smul, hab, one_smul]
        calc
          x0 + (a • (v : E) + b • (w : E))
              = a • x0 + b • x0 + (a • (v : E) + b • (w : E)) := by rw [hsum]
          _ = a • (x0 + (v : E)) + b • (x0 + (w : E)) := by
            simp only [smul_add]
            abel
      have hmem : x0 + (a • (v : E) + b • (w : E)) ∈ C := by
        rw [hlin]
        exact hc hvC hwC ha hb hab
      simpa [C0, AddSubmonoid.coe_add, Submodule.coe_smul] using hmem
    have hspan0 : vectorSpan ℝ C0 = ⊤ := by
      rw [vectorSpan_eq_span_vsub_set_right ℝ h0]
      have hzero : (· -ᵥ (0 : F)) '' C0 = C0 := by
        ext v
        simp [vsub_eq_sub]
      rw [hzero]
      refine (LinearMap.map_injective (Submodule.ker_subtype F)) ?_
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
      have him : F.subtype '' C0 = (· -ᵥ x0) '' C := by
        ext y
        constructor
        · rintro ⟨v, hv, rfl⟩
          refine ⟨x0 + (v : E), hv, ?_⟩
          simp [vsub_eq_sub]
        · rintro ⟨y, hy, rfl⟩
          refine ⟨⟨y - x0, vsub_mem_vectorSpan ℝ hy hx0⟩, ?_, ?_⟩
          · simpa [C0] using hy
          · simp [vsub_eq_sub]
      rw [him, ← vectorSpan_eq_span_vsub_set_right ℝ hx0]
    have haff : affineSpan ℝ C0 = ⊤ :=
      (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ F F hne0).2
        hspan0
    have hint : (interior C0).Nonempty :=
      (hconv0.interior_nonempty_iff_affineSpan_eq_top).2 haff
    let ψ : C → C0 := fun y =>
      ⟨⟨(y : E) - x0, vsub_mem_vectorSpan ℝ y.2 hx0⟩, by simp [C0]⟩
    have hψ : Continuous ψ :=
      (Continuous.subtype_mk (continuous_subtype_val.sub continuous_const)
        (fun y => vsub_mem_vectorSpan ℝ y.2 hx0)).subtype_mk (fun y => by simp [C0])
    let ψinv : C0 → C := fun v => ⟨x0 + (v : E), v.2⟩
    have hψinv : Continuous ψinv := by
      unfold ψinv
      refine Continuous.subtype_mk ?_ fun v => v.2
      fun_prop
    have hcomp0 : IsCompact C0 := by
      let φ : C → F := fun y => ⟨(y : E) - x0, vsub_mem_vectorSpan ℝ y.2 hx0⟩
      have hφ : Continuous φ :=
        Continuous.subtype_mk (continuous_subtype_val.sub continuous_const)
          fun y => vsub_mem_vectorSpan ℝ y.2 hx0
      have hrange : Set.range φ = C0 := by
        ext v
        constructor
        · rintro ⟨y, rfl⟩
          simp [C0, φ]
        · intro hv
          refine ⟨ψinv ⟨v, hv⟩, ?_⟩
          apply Subtype.ext
          simp [φ, ψinv]
      rw [← hrange]
      have : CompactSpace C := isCompact_iff_compactSpace.mp hC
      exact isCompact_range hφ
    let T0 : C0 → C0 := fun v => ψ (T (ψinv v))
    have hT0 : Continuous T0 := hψ.comp (hT.comp hψinv)
    obtain ⟨v, hv⟩ := exists_fixedPoint_of_interior hne0 hcomp0 hconv0 hint T0 hT0
    refine ⟨ψinv v, ?_⟩
    have hv' : ψ (T (ψinv v)) = v := by simpa [T0] using hv
    have hcancel : ψinv (ψ (T (ψinv v))) = T (ψinv v) := by
      apply Subtype.ext
      simp [ψ, ψinv]
    rw [hv'] at hcancel
    exact hcancel.symm

/-- **35.13**: Schauder's theorem with relatively compact total image on a closed convex set.
Boundedness of the domain is not required when the total image is relatively compact. -/
theorem exists_fixedPoint_schauder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C)
    (hc : Convex ℝ C) (T : C → C) (hT : Continuous T)
    (himage : IsCompact (closure (Set.range (fun x : C ↦ (T x : E))))) :
    ∃ x : C, T x = x := by
  sorry

/-- **35.15**: Kakutani–Fan–Glicksberg for compact convex subsets of locally convex spaces.
The multifunction is defined on the ambient space but only its restriction to `C` is constrained. -/
theorem exists_fixedPoint_kakutani {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E]
    {C : Set E} (hne : C.Nonempty) (hC : IsCompact C) (hc : Convex ℝ C)
    (T : E → Set E) (hT : UpperHemicontinuousOn T C)
    (hvalues : ∀ x ∈ C, (T x).Nonempty ∧ IsClosed (T x) ∧ Convex ℝ (T x) ∧ T x ⊆ C) :
    ∃ x ∈ C, x ∈ T x := by
  sorry

/-- **35.21**: Browder–Göhde–Kirk requires uniform convexity of the Banach space,
not compactness of the nonexpansive map. -/
theorem exists_fixedPoint_nonexpansive {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [UniformConvexSpace E]
    {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C) (hbounded : Bornology.IsBounded C)
    (hc : Convex ℝ C) (T : C → C) (hT : LipschitzWith 1 T) : ∃ x : C, T x = x := by
  sorry

end CKMA
