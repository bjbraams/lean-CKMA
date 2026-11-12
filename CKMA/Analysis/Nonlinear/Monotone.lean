/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.AlgebraicTopology.Sphere.Contractible
public import TauCeti.Analysis.Convex.Uniform
public import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Tactic

/-!
# Monotone graphs, resolvents, and variational inequalities

Hilbert-space graph monotonicity gives resolvent uniqueness at nonnegative scales; Minty's
range criterion and existence use strictly positive scales. The normal cone includes its
base-point constraint.

For maps into a real Banach dual, monotonicity, hemicontinuity, boundedness on bounded sets,
and coercivity are expressed directly in the dual pairing. Reflexivity uses surjectivity of
the canonical bidual inclusion. Variational inequalities have separate bounded-domain and
coercive unbounded-domain existence statements. Sources: GAPS 35.32, 35.40, and 35.45.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology Bornology
open scoped InnerProductSpace

section FixedPoint

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
private theorem ContractibleSpace.of_retraction {A X : Type*} [TopologicalSpace A]
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
    ContractibleSpace.of_retraction i r hr
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
private theorem exists_fixedPoint_of_interior {E : Type*} [NormedAddCommGroup E]
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

/-- Continuous self-maps of a nonempty compact convex set in a finite-dimensional real normed
space have a fixed point. The set is reduced to a direction space in which its interior
is nonempty, and that case is the Euclidean ball. -/
private theorem exists_fixedPoint_compact_convex {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {C : Set E} (hne : C.Nonempty)
    (hcomp : IsCompact C) (hconv : Convex ℝ C) (T : C → C) (hT : Continuous T) :
    ∃ x, T x = x := by
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
        exact hconv hvC hwC ha hb hab
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
      have : CompactSpace C := isCompact_iff_compactSpace.mp hcomp
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

end FixedPoint

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Monotonicity of a Hilbert-space graph. -/
def IsMonotoneGraph (A : Set (H × H)) : Prop :=
  ∀ p ∈ A, ∀ q ∈ A, 0 ≤ ⟪p.1 - q.1, p.2 - q.2⟫_ℝ

/-- A monotone graph is maximal when it has no proper monotone enlargement. -/
def IsMaximalMonotoneGraph (A : Set (H × H)) : Prop :=
  IsMonotoneGraph A ∧ ∀ B, IsMonotoneGraph B → A ⊆ B → B ⊆ A

/-- A resolvent fiber: `y` belongs when `x ∈ y + a A(y)`.
This relation has a concrete body even before the existence theorem is proved. -/
def monotoneResolventFiber (A : Set (H × H)) (a : ℝ) (x : H) : Set H :=
  {y | ∃ u, (y, u) ∈ A ∧ x = y + a • u}

/-- Monotonicity alone makes a nonnegative-scale resolvent fiber single-valued.
This uniqueness statement does not depend on Minty's existence theorem. -/
theorem IsMonotoneGraph.resolventFiber_subsingleton {A : Set (H × H)}
    (hA : IsMonotoneGraph A) {a : ℝ} (ha : 0 ≤ a) (x : H) :
    (monotoneResolventFiber A a x).Subsingleton := by
  intro y hy z hz
  obtain ⟨u, hu, hxu⟩ := hy
  obtain ⟨v, hv, hxv⟩ := hz
  have hlinear : a • (u - v) = z - y := by
    calc
      a • (u - v) = (y + a • u) - (z + a • v) - (y - z) := by module
      _ = z - y := by rw [← hxu, ← hxv]; abel
  have hmon := hA (y, u) hu (z, v) hv
  have hscaled : 0 ≤ ⟪y - z, a • (u - v)⟫_ℝ := by
    simpa only [inner_smul_right, smul_eq_mul] using mul_nonneg ha hmon
  rw [hlinear] at hscaled
  have hneg : ⟪y - z, z - y⟫_ℝ = -(‖y - z‖ ^ 2) := by
    rw [show z - y = -(y - z) by abel, inner_neg_right, real_inner_self_eq_norm_sq]
  rw [hneg] at hscaled
  have hnorm : ‖y - z‖ = 0 := by nlinarith [sq_nonneg ‖y - z‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- A pair that is monotone against every pair of a maximal monotone graph already belongs to it. -/
private theorem IsMaximalMonotoneGraph.mem_of_monotone_with {A : Set (H × H)}
    (hA : IsMaximalMonotoneGraph A) {y u : H}
    (hmono : ∀ p ∈ A, 0 ≤ ⟪y - p.1, u - p.2⟫_ℝ) : (y, u) ∈ A := by
  let B := A ∪ {(y, u)}
  have hB : IsMonotoneGraph B := by
    intro p hp q hq
    rcases hp with hp | hp
    · rcases hq with hq | hq
      · exact hA.1 p hp q hq
      · rw [Set.mem_singleton_iff.mp hq]
        have hswap : ⟪p.1 - y, p.2 - u⟫_ℝ = ⟪y - p.1, u - p.2⟫_ℝ := by
          rw [show p.1 - y = -(y - p.1) by abel, show p.2 - u = -(u - p.2) by abel,
            inner_neg_left, inner_neg_right, neg_neg]
        rw [hswap]
        exact hmono p hp
    · rw [Set.mem_singleton_iff.mp hp]
      rcases hq with hq | hq
      · exact hmono q hq
      · rw [Set.mem_singleton_iff.mp hq]
        simp
  exact hA.2 B hB Set.subset_union_left (Set.mem_union_right _ rfl)

/-- A finite sum of continuous maps into a topological additive monoid is continuous. -/
private theorem continuous_finset_sum_apply {ι α β : Type*} [AddCommMonoid β]
    [TopologicalSpace α] [TopologicalSpace β] [ContinuousAdd β] (s : Finset ι)
    {f : ι → α → β} (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact continuous_const
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Pull a constant vector out of a finite weighted sum. -/
private theorem sum_smul_const {ι : Type*} (s : Finset ι) (w : ι → ℝ) (v : H) :
    ∑ i ∈ s, w i • v = (∑ i ∈ s, w i) • v := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih, add_smul]

/-- Pairwise real inner products rearrange into a sum against the weight barycenter. -/
private theorem sum_pair_inner_eq {n : ℕ} (w : Fin n → ℝ) (v u : Fin n → H)
    (hw : ∑ i, w i = 1) :
    ∑ i, ∑ j, w i * w j * ⟪v i - v j, u i - u j⟫_ℝ =
      2 * ∑ i, w i * ⟪v i - ∑ k, w k • v k, u i⟫_ℝ := by
  have hexpand (i j : Fin n) : ⟪v i - v j, u i - u j⟫_ℝ =
      ⟪v i, u i⟫_ℝ - ⟪v i, u j⟫_ℝ - ⟪v j, u i⟫_ℝ + ⟪v j, u j⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    abel
  have hterm (i j : Fin n) : w i * w j * ⟪v i - v j, u i - u j⟫_ℝ =
      w i * w j * ⟪v i, u i⟫_ℝ - w i * w j * ⟪v i, u j⟫_ℝ -
        w i * w j * ⟪v j, u i⟫_ℝ + w i * w j * ⟪v j, u j⟫_ℝ := by
    rw [hexpand]
    ring
  have hsplit : ∑ i, ∑ j, w i * w j * ⟪v i - v j, u i - u j⟫_ℝ =
      ∑ i, ∑ j, w i * w j * ⟪v i, u i⟫_ℝ -
        ∑ i, ∑ j, w i * w j * ⟪v i, u j⟫_ℝ -
        ∑ i, ∑ j, w i * w j * ⟪v j, u i⟫_ℝ +
        ∑ i, ∑ j, w i * w j * ⟪v j, u j⟫_ℝ := by
    have hrew :
        ∑ i, ∑ j, w i * w j * ⟪v i - v j, u i - u j⟫_ℝ =
          ∑ i, ∑ j,
            (w i * w j * ⟪v i, u i⟫_ℝ - w i * w j * ⟪v i, u j⟫_ℝ -
              w i * w j * ⟪v j, u i⟫_ℝ + w i * w j * ⟪v j, u j⟫_ℝ) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      exact hterm i j
    rw [hrew]
    have hinner (i : Fin n) :
        ∑ j, (w i * w j * ⟪v i, u i⟫_ℝ - w i * w j * ⟪v i, u j⟫_ℝ -
            w i * w j * ⟪v j, u i⟫_ℝ + w i * w j * ⟪v j, u j⟫_ℝ) =
          ∑ j, w i * w j * ⟪v i, u i⟫_ℝ - ∑ j, w i * w j * ⟪v i, u j⟫_ℝ -
            ∑ j, w i * w j * ⟪v j, u i⟫_ℝ + ∑ j, w i * w j * ⟪v j, u j⟫_ℝ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp_rw [hinner]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h11 : ∑ i, ∑ j, w i * w j * ⟪v i, u i⟫_ℝ = ∑ i, w i * ⟪v i, u i⟫_ℝ := by
    simp_rw [show ∀ i j, w i * w j * ⟪v i, u i⟫_ℝ = (w i * ⟪v i, u i⟫_ℝ) * w j by
      intros; ring, ← Finset.mul_sum, hw, mul_one]
  have h22 : ∑ i, ∑ j, w i * w j * ⟪v j, u j⟫_ℝ = ∑ i, w i * ⟪v i, u i⟫_ℝ := by
    rw [Finset.sum_comm]
    simp_rw [show ∀ i j, w i * w j * ⟪v j, u j⟫_ℝ = (w j * ⟪v j, u j⟫_ℝ) * w i by
      intros; ring, ← Finset.mul_sum, hw, mul_one]
  have hcross : ∑ i, ∑ j, w i * w j * ⟪v i, u j⟫_ℝ =
      ⟪∑ i, w i • v i, ∑ j, w j • u j⟫_ℝ := by
    symm
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, inner_smul_right]
    ring
  have hcross' : ∑ i, ∑ j, w i * w j * ⟪v j, u i⟫_ℝ =
      ∑ i, ∑ j, w i * w j * ⟪v i, u j⟫_ℝ := by
    rw [Finset.sum_comm]
    simp_rw [mul_comm (w _) (w _)]
  have hdot : ⟪∑ i, w i • v i, ∑ j, w j • u j⟫_ℝ =
      ∑ i, w i * ⟪∑ k, w k • v k, u i⟫_ℝ := by
    rw [inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_right]
  have hdiff : ∑ i, w i * ⟪v i, u i⟫_ℝ - ∑ i, w i * ⟪∑ k, w k • v k, u i⟫_ℝ =
      ∑ i, w i * ⟪v i - ∑ k, w k • v k, u i⟫_ℝ := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_sub, inner_sub_left]
  rw [hsplit, h11, h22, hcross', hcross, hdot]
  have htwo : ∑ i, w i * ⟪v i, u i⟫_ℝ - ∑ i, w i * ⟪∑ k, w k • v k, u i⟫_ℝ -
      ∑ i, w i * ⟪∑ k, w k • v k, u i⟫_ℝ + ∑ i, w i * ⟪v i, u i⟫_ℝ =
      2 * (∑ i, w i * ⟪v i, u i⟫_ℝ - ∑ i, w i * ⟪∑ k, w k • v k, u i⟫_ℝ) := by
    ring
  rw [htwo, hdiff]

/-- The inequality `0 ≤ ⟪y - v, c - y⟫` cuts out the closed ball with diameter from `v` to `c`. -/
private theorem inner_nonneg_iff_mem_closedBall {v c y : H} :
    0 ≤ ⟪y - v, c - y⟫_ℝ ↔
      y ∈ Metric.closedBall ((2⁻¹ : ℝ) • (v + c)) (‖c - v‖ / 2) := by
  rw [mem_closedBall_iff_norm]
  have hm : y - (2⁻¹ : ℝ) • (v + c) = (y - v) - (2⁻¹ : ℝ) • (c - v) := by
    module
  rw [hm]
  have hrad : 0 ≤ ‖c - v‖ / 2 := div_nonneg (norm_nonneg _) zero_le_two
  rw [← sq_le_sq₀ (norm_nonneg _) hrad]
  have hexpand : ‖(y - v) - (2⁻¹ : ℝ) • (c - v)‖ ^ 2 =
      ‖y - v‖ ^ 2 - ⟪y - v, c - v⟫_ℝ + ‖c - v‖ ^ 2 / 4 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr zero_le_two)]
    ring
  have hinner : ⟪y - v, c - y⟫_ℝ = ⟪y - v, c - v⟫_ℝ - ‖y - v‖ ^ 2 := by
    rw [show c - y = (c - v) - (y - v) by abel, inner_sub_right, real_inner_self_eq_norm_sq]
  constructor
  · intro hle
    nlinarith [hexpand, hinner, hle]
  · intro hle
    nlinarith [hexpand, hinner, hle]

/-- Finitely many monotone slices meet: a simplex map fixes a convex combination in every slice. -/
private theorem exists_common_monotoneSlice {A : Set (H × H)} (hA : IsMonotoneGraph A) {a : ℝ}
    (ha : 0 < a) {n : ℕ} (hn : 0 < n) (p : Fin n → H × H) (hp : ∀ i, p i ∈ A) (x : H) :
    ∃ y, ∀ i, 0 ≤ ⟪y - (p i).1, x - y - a • (p i).2⟫_ℝ := by
  let Simplex := stdSimplex ℝ (Fin n)
  have hne : Simplex.Nonempty := ⟨Pi.single ⟨0, hn⟩ 1, single_mem_stdSimplex _ _⟩
  let bary (weight : Fin n → ℝ) : H := ∑ i, weight i • (p i).1
  let gap (weight : Fin n → ℝ) (i : Fin n) : ℝ :=
    ⟪bary weight - (p i).1, x - bary weight - a • (p i).2⟫_ℝ
  let slack (weight : Fin n → ℝ) (i : Fin n) : ℝ := max 0 (-gap weight i)
  let total (weight : Fin n → ℝ) : ℝ := ∑ i, (weight i + slack weight i)
  have htotal (s : Simplex) : 1 ≤ total s := by
    have hsum : ∑ i, (s : Fin n → ℝ) i = 1 := s.2.2
    have hslack : ∀ i, 0 ≤ slack s i := fun i => le_max_left _ _
    calc
      1 = ∑ i, (s : Fin n → ℝ) i := hsum.symm
      _ ≤ ∑ i, ((s : Fin n → ℝ) i + slack s i) := by
        gcongr with i
        exact le_add_of_nonneg_right (hslack i)
      _ = total s := rfl
  let next (s : Simplex) : Fin n → ℝ :=
    fun i => ((s : Fin n → ℝ) i + slack s i) / total s
  have hnext (s : Simplex) : next s ∈ Simplex := by
    refine ⟨fun i => div_nonneg (add_nonneg (s.2.1 i) (le_max_left _ _))
        (le_trans zero_le_one (htotal s)), ?_⟩
    have hden : total s ≠ 0 := by linarith [htotal s]
    rw [← Finset.sum_div]
    exact div_self hden
  let T : Simplex → Simplex := fun s => ⟨next s, hnext s⟩
  have hcoord (i : Fin n) : Continuous fun s : Simplex => (s : Fin n → ℝ) i :=
    (continuous_apply i).comp continuous_subtype_val
  have hbary : Continuous fun s : Simplex => bary (s : Fin n → ℝ) := by
    unfold bary
    exact continuous_finset_sum_apply Finset.univ fun i _ => (hcoord i).smul continuous_const
  have hgapC (i : Fin n) : Continuous fun s : Simplex => gap (s : Fin n → ℝ) i := by
    unfold gap
    exact (hbary.sub continuous_const).inner
      ((continuous_const.sub hbary).sub continuous_const)
  have hslackC (i : Fin n) : Continuous fun s : Simplex => slack (s : Fin n → ℝ) i := by
    unfold slack
    exact continuous_const.max (hgapC i).neg
  have hdenC : Continuous fun s : Simplex => total (s : Fin n → ℝ) := by
    unfold total
    exact continuous_finset_sum_apply Finset.univ fun i _ => (hcoord i).add (hslackC i)
  have hT : Continuous T := by
    refine Continuous.subtype_mk ?_ hnext
    exact continuous_pi fun i =>
      ((hcoord i).add (hslackC i)).div₀ hdenC fun s => by linarith [htotal s]
  let Euc := EuclideanSpace ℝ (Fin n)
  let e : Euc ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  let K : Set Euc := e.symm '' Simplex
  have hneK : K.Nonempty := by
    obtain ⟨w0, hw0⟩ := hne
    exact ⟨e.symm w0, w0, hw0, rfl⟩
  have hcompK : IsCompact K := (isCompact_stdSimplex ℝ (Fin n)).image e.symm.continuous
  have hconvK : Convex ℝ K :=
    (convex_stdSimplex ℝ (Fin n)).linear_image e.symm.toLinearMap
  have hmemK (y : K) : e y.1 ∈ Simplex := by
    obtain ⟨w0, hw0, hy⟩ := y.2
    have heq : e y.1 = w0 := by
      rw [← hy]
      simp
    simpa [heq] using hw0
  have hlift : Continuous fun y : K => (⟨e y.1, hmemK y⟩ : Simplex) :=
    Continuous.subtype_mk (e.continuous.comp continuous_subtype_val) hmemK
  have hland (y : K) : e.symm (Subtype.val (T ⟨e y.1, hmemK y⟩)) ∈ K :=
    ⟨Subtype.val (T ⟨e y.1, hmemK y⟩), (T ⟨e y.1, hmemK y⟩).2, rfl⟩
  let S : K → K := fun y => ⟨e.symm (Subtype.val (T ⟨e y.1, hmemK y⟩)), hland y⟩
  have hS : Continuous S :=
    Continuous.subtype_mk
      (e.symm.continuous.comp (continuous_subtype_val.comp (hT.comp hlift))) hland
  obtain ⟨yK, hyK⟩ := exists_fixedPoint_compact_convex hneK hcompK hconvK S hS
  let s : Simplex := ⟨e yK.1, hmemK yK⟩
  have hs : T s = s := by
    apply Subtype.ext
    have happly := congrArg e (congrArg Subtype.val hyK)
    unfold S at happly
    rw [e.apply_symm_apply] at happly
    simpa [s] using happly
  have hfix : next s = (s : Fin n → ℝ) := congrArg Subtype.val hs
  let w : Fin n → ℝ := s
  have hweight : ∑ i, w i = 1 := s.2.2
  have hden : total s ≠ 0 := by linarith [htotal s]
  have hslack_eq (i : Fin n) : slack s i = w i * (total s - 1) := by
    have hi : (w i + slack s i) / total s = w i := by
      simpa [next, w] using congrFun hfix i
    rw [div_eq_iff hden] at hi
    linarith
  have hσ : total s = 1 := by
    by_contra hneσ
    have hgt : 1 < total s := lt_of_le_of_ne (htotal s) (Ne.symm hneσ)
    have hsign (i : Fin n) : w i * gap s i ≤ 0 := by
      by_cases hzi : w i = 0
      · simp [hzi]
      · have hwi : 0 < w i := lt_of_le_of_ne (s.2.1 i) (fun h => hzi h.symm)
        have hpos : 0 < slack s i := by
          rw [hslack_eq i]
          nlinarith
        have hng : 0 < -gap s i := by
          by_contra hng
          have : slack s i = 0 := by
            unfold slack
            exact max_eq_left (le_of_not_gt hng)
          linarith
        exact le_of_lt (mul_neg_of_pos_of_neg hwi (neg_pos.mp hng))
    have hsome : ∃ i, 0 < w i := by
      by_contra hall
      have hzero : ∀ i, w i = 0 := by
        intro i
        exact le_antisymm (le_of_not_gt (fun hpos => hall ⟨i, hpos⟩)) (s.2.1 i)
      have : ∑ i, w i = 0 := Finset.sum_eq_zero fun i _ => hzero i
      linarith [hweight, this]
    obtain ⟨i0, hi0⟩ := hsome
    have hstrict : w i0 * gap s i0 < 0 := by
      have hpos : 0 < slack s i0 := by
        rw [hslack_eq i0]
        nlinarith
      have hng : 0 < -gap s i0 := by
        by_contra hng
        have : slack s i0 = 0 := by
          unfold slack
          exact max_eq_left (le_of_not_gt hng)
        linarith
      exact mul_neg_of_pos_of_neg hi0 (neg_pos.mp hng)
    have hsumθ : ∑ i, w i * gap s i < 0 := by
      have hlt := Finset.sum_lt_sum (fun i _ => hsign i) ⟨i0, Finset.mem_univ _, hstrict⟩
      simpa [Finset.sum_const_zero] using hlt
    have hvanish : ∑ i, w i * ⟪bary w - (p i).1, x - bary w⟫_ℝ = 0 := by
      have hsumv : ∑ i, w i • (bary w - (p i).1) = 0 := by
        simp_rw [smul_sub, Finset.sum_sub_distrib]
        rw [sum_smul_const Finset.univ w (bary w), hweight, one_smul]
        have hbaryw : ∑ i, w i • (p i).1 = bary w := by simp [bary, w]
        rw [hbaryw, sub_self]
      have hpair : ∑ i, w i * ⟪bary w - (p i).1, x - bary w⟫_ℝ =
          ⟪∑ i, w i • (bary w - (p i).1), x - bary w⟫_ℝ := by
        rw [sum_inner]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [real_inner_smul_left]
      rw [hpair, hsumv, inner_zero_left]
    have hsplitSum : ∑ i, w i * gap s i =
        -a * ∑ i, w i * ⟪bary w - (p i).1, (p i).2⟫_ℝ := by
      have hgap_eq (i : Fin n) : gap s i = ⟪bary w - (p i).1, x - bary w⟫_ℝ -
          a * ⟪bary w - (p i).1, (p i).2⟫_ℝ := by
        unfold gap
        rw [inner_sub_right, inner_smul_right]
      simp_rw [hgap_eq, mul_sub, Finset.sum_sub_distrib, hvanish]
      simp_rw [mul_left_comm (w _) a, ← Finset.mul_sum]
      ring
    have hmono : 0 ≤ ∑ i, w i * ⟪(p i).1 - bary w, (p i).2⟫_ℝ := by
      have hpairEq := sum_pair_inner_eq w (fun i => (p i).1) (fun i => (p i).2) hweight
      have hnn : 0 ≤ ∑ i, ∑ j, w i * w j *
          ⟪(p i).1 - (p j).1, (p i).2 - (p j).2⟫_ℝ := by
        refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
        exact mul_nonneg (mul_nonneg (s.2.1 i) (s.2.1 j)) (hA _ (hp i) _ (hp j))
      have hbaryw : ∑ k, w k • (p k).1 = bary w := by simp [bary, w]
      rw [hpairEq, hbaryw] at hnn
      nlinarith
    have hnegSum : ∑ i, w i * ⟪bary w - (p i).1, (p i).2⟫_ℝ =
        -∑ i, w i * ⟪(p i).1 - bary w, (p i).2⟫_ℝ := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← neg_sub (p i).1 (bary w), inner_neg_left, mul_neg]
    have hle : ∑ i, w i * ⟪bary w - (p i).1, (p i).2⟫_ℝ ≤ 0 := by
      rw [hnegSum]
      linarith
    nlinarith [hsplitSum, hsumθ, ha, hle]
  refine ⟨bary w, fun i => ?_⟩
  have hzero : slack s i = 0 := by rw [hslack_eq i, hσ, sub_self, mul_zero]
  have hmax : max 0 (-gap s i) = 0 := by simpa [slack] using hzero
  have hgap0 : -gap s i ≤ 0 := (max_eq_left_iff).mp hmax
  simpa [gap, w] using (neg_nonpos.mp hgap0)

/-- **35.32**: Minty's characterization at each positive scale. -/
theorem isMaximalMonotoneGraph_iff_range [CompleteSpace H]
    {A : Set (H × H)} (hA : IsMonotoneGraph A) {a : ℝ} (ha : 0 < a) :
    IsMaximalMonotoneGraph A ↔ ∀ x, (monotoneResolventFiber A a x).Nonempty := by
  constructor
  · intro hmax x
    have hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ H) :=
      TauCeti.surjective_inclusionInDoubleDual_of_uniformConvexSpace
    have hneA : A.Nonempty := by
      by_contra hempty
      have hpair : (0, 0) ∈ A ∪ {(0, 0)} := Set.mem_union_right _ rfl
      have hB : IsMonotoneGraph (A ∪ {(0, 0)}) := by
        intro p hp q hq
        rcases hp with hp | hp
        · exact False.elim (hempty ⟨p, hp⟩)
        · rcases hq with hq | hq
          · exact False.elim (hempty ⟨q, hq⟩)
          · simp [show p = (0, 0) from hp, show q = (0, 0) from hq]
      have hsub := hmax.2 _ hB Set.subset_union_left hpair
      exact hempty ⟨_, hsub⟩
    let slice : A → Set H := fun q =>
      {y | 0 ≤ ⟪y - (q : H × H).1, x - y - a • (q : H × H).2⟫_ℝ}
    have hball (q : ↥A) : slice q =
        Metric.closedBall ((2⁻¹ : ℝ) • ((q : H × H).1 + (x - a • (q : H × H).2)))
          (‖(x - a • (q : H × H).2) - (q : H × H).1‖ / 2) := by
      ext y
      simp only [slice, Set.mem_setOf_eq]
      rw [show x - y - a • (q : H × H).2 = (x - a • (q : H × H).2) - y by abel]
      exact inner_nonneg_iff_mem_closedBall (v := (q : H × H).1)
        (c := x - a • (q : H × H).2) (y := y)
    have hcompact (q : ↥A) : IsCompact (toWeakSpace ℝ H '' slice q) := by
      rw [hball q]
      exact TauCeti.isCompact_toWeakSpace_closedBall hreflexive _ _
    obtain ⟨q0, hq0⟩ := hneA
    have hst (u : Finset (↥A)) :
        ((toWeakSpace ℝ H '' slice ⟨q0, hq0⟩) ∩
          ⋂ q ∈ u, toWeakSpace ℝ H '' slice q).Nonempty := by
      classical
      let qfin : Fin (u.card + 1) → H × H := fun i =>
        if h : (i : ℕ) < u.card then (u.equivFin.symm ⟨(i : ℕ), h⟩).1 else (⟨q0, hq0⟩ : ↥A)
      have hqfin : ∀ i, qfin i ∈ A := by
        intro i
        by_cases h : (i : ℕ) < u.card
        · exact (by simpa [qfin, h] using (u.equivFin.symm ⟨(i : ℕ), h⟩).1.2)
        · exact (by simpa [qfin, h] using hq0)
      obtain ⟨y, hy⟩ :=
        exists_common_monotoneSlice hA ha (Nat.succ_pos u.card) qfin hqfin x
      refine ⟨toWeakSpace ℝ H y, ?_, ?_⟩
      · have hlast : qfin (Fin.last u.card) = q0 := by
          simp [qfin, Fin.val_last]
        exact ⟨y, by simpa [slice, hlast] using hy (Fin.last u.card), rfl⟩
      · rw [Set.mem_iInter₂]
        intro q hq
        let i0 : Fin u.card := u.equivFin ⟨q, hq⟩
        let j : Fin (u.card + 1) := i0.castSucc
        have hj : (j : ℕ) < u.card := by
          have : (j : ℕ) = (i0 : ℕ) := by simp [j, Fin.val_castSucc]
          simpa [this] using i0.isLt
        have hqj : qfin j = (q : H × H) := by
          have heq : (u.equivFin.symm i0).1 = q :=
            congrArg Subtype.val (u.equivFin.symm_apply_apply ⟨q, hq⟩)
          simp [qfin, hj, j, Fin.val_castSucc, heq]
        exact ⟨y, by simpa [slice, hqj] using hy j, rfl⟩
    have hinter : (⋂ q : ↥A, toWeakSpace ℝ H '' slice q).Nonempty :=
      ((hcompact ⟨q0, hq0⟩).inter_iInter_nonempty (fun q : ↥A => toWeakSpace ℝ H '' slice q)
        (fun q => (hcompact q).isClosed) hst).imp fun _ h => h.2
    obtain ⟨zW, hzW⟩ := hinter
    let y : H := (toWeakSpace ℝ H).symm zW
    have hySlice : ∀ q : ↥A, y ∈ slice q := by
      intro q
      obtain ⟨y', hy', hzy⟩ := (Set.mem_iInter.mp hzW) q
      have hyeq : y' = y :=
        (toWeakSpace ℝ H).injective (by simpa [y] using hzy)
      exact hyeq ▸ hy'
    have hcrit : ∀ p ∈ A, 0 ≤ ⟪y - p.1, a⁻¹ • (x - y) - p.2⟫_ℝ := by
      intro p hp
      have hscale : a⁻¹ • (x - y) - p.2 = a⁻¹ • (x - y - a • p.2) := by
        calc
          a⁻¹ • (x - y) - p.2 = a⁻¹ • (x - y) - (a⁻¹ * a) • p.2 := by
            rw [inv_mul_cancel₀ ha.ne', one_smul]
          _ = a⁻¹ • (x - y) - a⁻¹ • (a • p.2) := by rw [smul_smul]
          _ = a⁻¹ • (x - y - a • p.2) := by rw [← smul_sub]
      rw [hscale, inner_smul_right]
      exact mul_nonneg (le_of_lt (inv_pos.mpr ha)) (hySlice ⟨p, hp⟩)
    refine ⟨y, a⁻¹ • (x - y), hmax.mem_of_monotone_with hcrit, ?_⟩
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    abel
  · intro hrange
    refine ⟨hA, fun B hB hAB z hz => ?_⟩
    obtain ⟨y, hy⟩ := hrange (z.1 + a • z.2)
    obtain ⟨u, huA, hxu⟩ := hy
    have hboth : (z.1, z.2) ∈ B ∧ (y, u) ∈ B := ⟨hz, hAB huA⟩
    have hmono := hB (z.1, z.2) hboth.1 (y, u) hboth.2
    have hlinear : a • (z.2 - u) = y - z.1 := by
      calc
        a • (z.2 - u) = (z.1 + a • z.2) - (y + a • u) - (z.1 - y) := by module
        _ = y - z.1 := by rw [← hxu]; abel
    have hscaled : 0 ≤ ⟪z.1 - y, a • (z.2 - u)⟫_ℝ := by
      simpa only [inner_smul_right, smul_eq_mul] using mul_nonneg ha.le hmono
    rw [hlinear] at hscaled
    have hneg : ⟪z.1 - y, y - z.1⟫_ℝ = -(‖z.1 - y‖ ^ 2) := by
      rw [show y - z.1 = -(z.1 - y) by abel, inner_neg_right, real_inner_self_eq_norm_sq]
    rw [hneg] at hscaled
    have hzero : z.1 = y := by
      have : ‖z.1 - y‖ = 0 := by nlinarith [sq_nonneg ‖z.1 - y‖]
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
    have hu_eq : z.2 = u := by
      have : a • (z.2 - u) = 0 := by simpa [hzero] using hlinear
      have hsub : z.2 - u = 0 := (smul_eq_zero.mp this).resolve_left ha.ne'
      exact sub_eq_zero.mp hsub
    have hzpair : z = (y, u) := Prod.ext hzero hu_eq
    rw [hzpair]
    exact huA

/-- Once a maximal monotone graph is given, every positive-scale resolvent fiber is a singleton. -/
theorem IsMaximalMonotoneGraph.existsUnique_resolvent [CompleteSpace H]
    {A : Set (H × H)} (hA : IsMaximalMonotoneGraph A) {a : ℝ} (ha : 0 < a) (x : H) :
    ∃! y, y ∈ monotoneResolventFiber A a x := by
  obtain ⟨y, hy⟩ := (isMaximalMonotoneGraph_iff_range hA.1 ha).mp hA x
  exact ⟨y, hy, fun z hz ↦ hA.1.resolventFiber_subsingleton ha.le x hz hy⟩

/-- The normal-cone graph of a convex set. Membership includes the base-point constraint. -/
def normalConeGraph (C : Set H) : Set (H × H) :=
  {p | p.1 ∈ C ∧ ∀ y ∈ C, ⟪p.2, y - p.1⟫_ℝ ≤ 0}

end Hilbert

section Banach

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Monotonicity for a map taking values in the continuous dual. -/
def IsMonotoneDualMap (A : E → StrongDual ℝ E) : Prop :=
  ∀ x y, 0 ≤ (A x - A y) (x - y)

/-- Strict monotonicity in the dual pairing. -/
def IsStrictlyMonotoneDualMap (A : E → StrongDual ℝ E) : Prop :=
  ∀ x y, x ≠ y → 0 < (A x - A y) (x - y)

/-- Hemicontinuity means continuity of every dual evaluation along each line segment. -/
def IsHemicontinuousDualMap (A : E → StrongDual ℝ E) : Prop :=
  ∀ x y z, ContinuousOn (fun t : ℝ ↦ A (x + t • y) z) (Set.Icc 0 1)

/-- Boundedness on bounded sets, without assuming global boundedness. -/
def MapsBoundedSetsToBoundedSets (A : E → StrongDual ℝ E) : Prop :=
  ∀ C : Set E, Bornology.IsBounded C → Bornology.IsBounded (A '' C)

/-- Coercivity in the dual pairing as the norm tends to infinity.
The ratio is totalized at zero, which does not affect this filter. -/
def IsCoerciveDualMap (A : E → StrongDual ℝ E) : Prop :=
  Tendsto (fun x ↦ A x x / ‖x‖) (Filter.comap (fun x : E ↦ ‖x‖) atTop) atTop

/-- **35.40**: Browder–Minty surjectivity for an everywhere-defined reflexive-Banach operator.
Reflexivity is expressed by the established bidual inclusion, as in TauCeti's weak compactness API.
  -/
theorem IsMonotoneDualMap.surjective [CompleteSpace E]
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    {A : E → StrongDual ℝ E} (hm : IsMonotoneDualMap A)
    (hh : IsHemicontinuousDualMap A) (hb : MapsBoundedSetsToBoundedSets A)
    (hc : IsCoerciveDualMap A) : Function.Surjective A := by
  sorry

/-- Strict monotonicity makes an inverse single-valued independently of existence. -/
theorem IsStrictlyMonotoneDualMap.injective {A : E → StrongDual ℝ E}
    (hA : IsStrictlyMonotoneDualMap A) : Function.Injective A := by
  intro x y hxy
  by_contra hne
  have h := hA x y hne
  simp [hxy] at h

/-- A variational inequality on `C` at forcing `f`. -/
def SolvesVariationalInequality (A : E → StrongDual ℝ E) (C : Set E)
    (f : StrongDual ℝ E) (u : E) : Prop :=
  u ∈ C ∧ ∀ v ∈ C, 0 ≤ (A u - f) (v - u)

/-- **35.45**: bounded-domain variational-inequality existence in a reflexive Banach space. -/
theorem exists_solution_variationalInequality [CompleteSpace E]
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    {A : E → StrongDual ℝ E} (hm : IsMonotoneDualMap A)
    (hh : IsHemicontinuousDualMap A) (hb : MapsBoundedSetsToBoundedSets A)
    {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbounded : Bornology.IsBounded C) (hc : Convex ℝ C) (f : StrongDual ℝ E) :
    ∃ u, SolvesVariationalInequality A C f u := by
  sorry

/-- Coercivity relative to a point of an unbounded constraint set. -/
def IsCoerciveOnAt (A : E → StrongDual ℝ E) (C : Set E)
    (f : StrongDual ℝ E) (u₀ : E) : Prop :=
  Tendsto (fun u ↦ (A u - f) (u - u₀) / ‖u‖)
    ((Filter.comap (fun u : E ↦ ‖u‖) atTop) ⊓ Filter.principal C) atTop

/-- The unbounded-domain version uses coercivity relative to one feasible point. -/
theorem exists_solution_variationalInequality_of_coercive [CompleteSpace E]
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    {A : E → StrongDual ℝ E} (hm : IsMonotoneDualMap A)
    (hh : IsHemicontinuousDualMap A) (hb : MapsBoundedSetsToBoundedSets A)
    {C : Set E} (hclosed : IsClosed C) (hc : Convex ℝ C)
    (f : StrongDual ℝ E) {u₀ : E} (hu₀ : u₀ ∈ C) (hcoercive : IsCoerciveOnAt A C f u₀) :
    ∃ u, SolvesVariationalInequality A C f u := by
  sorry

end Banach

end CKMA
