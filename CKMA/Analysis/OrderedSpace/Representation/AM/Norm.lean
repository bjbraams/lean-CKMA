/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.OrderedSpace.Representation.AM.State
public import Mathlib.Topology.Category.CompHaus.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Ordered

import Mathlib.Algebra.Order.Module.Basic
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Kakutani representation of an AM space with unit

Evaluation on the weak-star compact set of normalized lattice homomorphisms is a lattice
isometry onto `C(K, ℝ)`, by Krein–Milman and Stone–Weierstrass. The zero space is represented
by the empty compact carrier. The state space is constructed in
`CKMA.Analysis.OrderedSpace.Representation.AM.State`.
The argument follows Schaefer, *Banach Lattices and Positive Operators*, Theorem II.7.4.

## Main results

* `CKMA.exists_am_representation`: Kakutani representation of an AM Banach lattice with unit
  (**19.27**).
-/

public section

noncomputable section

open Set Metric LinearMap WeakDual ContinuousLinearMap

namespace CKMA

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E]
  [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]

variable {e : E} (he0 : 0 ≤ e) (hball : closedBall (0 : E) 1 = Icc (-e) e)

include he0 hball in
/-- A nonzero AM unit has a normalized lattice homomorphism. -/
private theorem amLatticeHomSet_nonempty (he : e ≠ 0) : (amLatticeHomSet e).Nonempty := by
  obtain ⟨φ, hφ⟩ :=
    (isCompact_amStateSet he0 hball he).extremePoints_nonempty (amStateSet_nonempty he0 hball he)
  exact ⟨φ, extremePoints_subset_amLatticeHomSet he0 hball he hφ⟩

include he0 hball in
/-- Supremum of a continuous linear image is unchanged by passing to extreme points. -/
private theorem csSup_extreme_eval (he : e ≠ 0) {y : E} :
    sSup ((fun φ : WeakDual ℝ E => φ y) '' (amStateSet e).extremePoints ℝ) =
      sSup ((fun φ : WeakDual ℝ E => φ y) '' amStateSet e) := by
  let s := amStateSet e
  let ext := s.extremePoints ℝ
  let f : WeakDual ℝ E → ℝ := fun φ => φ y
  have hscomp : IsCompact s := isCompact_amStateSet he0 hball he
  have hsconv : Convex ℝ s := convex_amStateSet
  have hsne : s.Nonempty := amStateSet_nonempty he0 hball he
  have hextne : ext.Nonempty := hscomp.extremePoints_nonempty hsne
  have hbext : BddAbove (f '' ext) := by
    obtain ⟨φ₀, hφ₀⟩ := hsne
    have hnorm : ‖φ₀.toStrongDual‖ = 1 := amState_opNorm_eq he0 hball he hφ₀
    refine ⟨‖y‖, ?_⟩
    rintro _ ⟨φ, hφ, rfl⟩
    have hstate : φ ∈ s := extremePoints_subset hφ
    have hop : ‖φ.toStrongDual‖ = 1 := amState_opNorm_eq he0 hball he hstate
    have hle := φ.toStrongDual.le_opNorm y
    rw [hop, one_mul, toStrongDual_apply] at hle
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hle)
  have hbs : BddAbove (f '' s) := by
    refine ⟨‖y‖, ?_⟩
    rintro _ ⟨φ, hφ, rfl⟩
    have hop : ‖φ.toStrongDual‖ = 1 := amState_opNorm_eq he0 hball he hφ
    have hle := φ.toStrongDual.le_opNorm y
    rw [hop, one_mul, toStrongDual_apply] at hle
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hle)
  have hle : sSup (f '' ext) ≤ sSup (f '' s) :=
    csSup_le_csSup hbs (hextne.image f) (image_mono extremePoints_subset)
  have hge : sSup (f '' s) ≤ sSup (f '' ext) := by
    let M : ℝ := sSup (f '' ext)
    have hlevel : ext ⊆ {φ | f φ ≤ M} := by
      intro φ hφ
      exact le_csSup hbext ⟨φ, hφ, rfl⟩
    have hclosed : IsClosed {φ : WeakDual ℝ E | f φ ≤ M} :=
      isClosed_le (eval_continuous y) continuous_const
    have hhull : convexHull ℝ ext ⊆ {φ | f φ ≤ M} := convexHull_min hlevel (by
      intro φ hφ ψ hψ a b ha hb hab
      have hcomb : f (a • φ + b • ψ) = a * f φ + b * f ψ := by
        change (a • φ + b • ψ) y = a * φ y + b * ψ y
        exact amWeakDual_combine φ ψ a b y
      have hle' : a * f φ + b * f ψ ≤ M := by
        calc
          a * f φ + b * f ψ ≤ a * M + b * M :=
            add_le_add (mul_le_mul_of_nonneg_left hφ ha) (mul_le_mul_of_nonneg_left hψ hb)
          _ = (a + b) * M := by rw [add_mul]
          _ = M := by rw [hab, one_mul]
      show f (a • φ + b • ψ) ≤ M
      rw [hcomb]
      exact hle')
    have hcl : closure (convexHull ℝ ext) ⊆ {φ | f φ ≤ M} :=
      closure_minimal hhull hclosed
    have hkm : closure (convexHull ℝ ext) = s :=
      closure_convexHull_extremePoints hscomp hsconv
    have hslevel : s ⊆ {φ | f φ ≤ M} := by simpa [hkm] using hcl
    apply csSup_le (hsne.image f)
    rintro _ ⟨φ, hφ, rfl⟩
    exact hslevel hφ
  exact le_antisymm hle hge

include he0 hball in
/-- Positive states recover the norm of a positive vector. -/
private theorem csSup_amState_eval (he : e ≠ 0) {y : E} (hy : 0 ≤ y) :
    sSup ((fun φ : WeakDual ℝ E => φ y) '' amStateSet e) = ‖y‖ := by
  have hsne : (amStateSet e).Nonempty := amStateSet_nonempty he0 hball he
  have hb : BddAbove ((fun φ : WeakDual ℝ E => φ y) '' amStateSet e) := by
    refine ⟨‖y‖, ?_⟩
    rintro _ ⟨φ, hφ, rfl⟩
    have hop : ‖φ.toStrongDual‖ = 1 := amState_opNorm_eq he0 hball he hφ
    have hle := φ.toStrongDual.le_opNorm y
    rw [hop, one_mul, toStrongDual_apply] at hle
    calc
      φ y ≤ |φ y| := le_abs_self _
      _ ≤ ‖y‖ := by simpa [Real.norm_eq_abs] using hle
  apply le_antisymm
  · apply csSup_le (hsne.image _)
    rintro _ ⟨φ, hφ, rfl⟩
    have hop : ‖φ.toStrongDual‖ = 1 := amState_opNorm_eq he0 hball he hφ
    have hle := φ.toStrongDual.le_opNorm y
    rw [hop, one_mul, toStrongDual_apply] at hle
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hle)
  · rcases eq_or_ne y 0 with rfl | hy0
    · have himage : (fun φ : WeakDual ℝ E => φ (0 : E)) '' amStateSet e = {0} := by
        ext t
        constructor
        · rintro ⟨φ, -, rfl⟩
          simp
        · rintro rfl
          obtain ⟨φ, hφ⟩ := hsne
          exact ⟨φ, hφ, by simp⟩
      rw [norm_zero, himage]
      exact (csSup_singleton (0 : ℝ)).ge
    · obtain ⟨φ, hpos, heφ, hyφ⟩ := exists_amState_norming he0 hball he hy hy0
      have hmem : φ ∈ amStateSet e := ⟨hpos, heφ⟩
      calc
        ‖y‖ = φ y := hyφ.symm
        _ ≤ sSup ((fun ψ : WeakDual ℝ E => ψ y) '' amStateSet e) :=
          le_csSup hb ⟨φ, hmem, rfl⟩

include he0 hball in
/-- Lattice homomorphisms recover the norm. -/
private theorem csSup_amLatticeHom_abs (he : e ≠ 0) (x : E) :
    sSup ((fun φ : WeakDual ℝ E => |φ x|) '' amLatticeHomSet e) = ‖x‖ := by
  have hext : sSup ((fun φ : WeakDual ℝ E => φ |x|) '' (amStateSet e).extremePoints ℝ) = ‖x‖ := by
    rw [csSup_extreme_eval he0 hball he, csSup_amState_eval he0 hball he (abs_nonneg x),
      norm_abs_eq_norm]
  have hne : ((amStateSet e).extremePoints ℝ).Nonempty :=
    (isCompact_amStateSet he0 hball he).extremePoints_nonempty (amStateSet_nonempty he0 hball he)
  have hb : BddAbove ((fun φ : WeakDual ℝ E => |φ x|) '' amLatticeHomSet e) := by
    refine ⟨‖x‖, ?_⟩
    rintro _ ⟨φ, hφ, rfl⟩
    have hpos : ∀ y, 0 ≤ y → 0 ≤ φ y := by
      intro y hy
      have habs := hφ.2 y
      rw [abs_of_nonneg hy] at habs
      have hnn : 0 ≤ |φ y| := abs_nonneg (φ y)
      rw [← habs] at hnn
      exact hnn
    have hop : ‖φ.toStrongDual‖ = 1 :=
      amState_opNorm_eq he0 hball he ⟨hpos, hφ.1⟩
    have hle := φ.toStrongDual.le_opNorm x
    rw [hop, one_mul, toStrongDual_apply] at hle
    simpa [Real.norm_eq_abs] using hle
  have hle : sSup ((fun φ : WeakDual ℝ E => φ |x|) '' (amStateSet e).extremePoints ℝ) ≤
      sSup ((fun φ : WeakDual ℝ E => |φ x|) '' amLatticeHomSet e) := by
    apply csSup_le_csSup hb (hne.image _)
    intro t ht
    obtain ⟨φ, hφ, rfl⟩ := ht
    have hK : φ ∈ amLatticeHomSet e := extremePoints_subset_amLatticeHomSet he0 hball he hφ
    refine ⟨φ, hK, ?_⟩
    exact (hK.2 x).symm
  have hge : sSup ((fun φ : WeakDual ℝ E => |φ x|) '' amLatticeHomSet e) ≤ ‖x‖ :=
    csSup_le ((amLatticeHomSet_nonempty he0 hball he).image _) (by
      rintro _ ⟨φ, hφ, rfl⟩
      have hpos : ∀ y, 0 ≤ y → 0 ≤ φ y := by
        intro y hy
        have habs := hφ.2 y
        rw [abs_of_nonneg hy] at habs
        have hnn : 0 ≤ |φ y| := abs_nonneg (φ y)
        rw [← habs] at hnn
        exact hnn
      have hop : ‖φ.toStrongDual‖ = 1 := amState_opNorm_eq he0 hball he ⟨hpos, hφ.1⟩
      have hle' := φ.toStrongDual.le_opNorm x
      rw [hop, one_mul, toStrongDual_apply] at hle'
      simpa [Real.norm_eq_abs] using hle')
  exact le_antisymm hge (hext.symm.trans_le hle)

omit [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- Normalized lattice homomorphisms preserve binary suprema. -/
private theorem amLatticeHom_map_sup {φ : WeakDual ℝ E} (hφ : φ ∈ amLatticeHomSet e) (x y : E) :
    φ (x ⊔ y) = φ x ⊔ φ y := by
  rw [sup_eq_half_smul_add_add_abs_sub' ℝ x y, map_smul, map_add, map_add, smul_eq_mul,
    hφ.2 (y - x), map_sub, sup_eq_half_smul_add_add_abs_sub' ℝ (φ x) (φ y), smul_eq_mul]

omit [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- Normalized lattice homomorphisms preserve binary infima. -/
private theorem amLatticeHom_map_inf {φ : WeakDual ℝ E} (hφ : φ ∈ amLatticeHomSet e) (x y : E) :
    φ (x ⊓ y) = φ x ⊓ φ y := by
  have h := amLatticeHom_map_sup hφ (-x) (-y)
  rw [← neg_inf] at h
  simp only [map_neg] at h
  rw [← neg_inf] at h
  exact neg_injective h

omit [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- Two normalized lattice homomorphisms take prescribed values at a common vector, provided
the values agree when the homomorphisms do. -/
private theorem exists_amLatticeHom_eq_and_eq {φ ψ : WeakDual ℝ E} (hφ : φ ∈ amLatticeHomSet e)
    (hψ : ψ ∈ amLatticeHomSet e) (a b : ℝ) (hab : φ = ψ → a = b) :
    ∃ x, φ x = a ∧ ψ x = b := by
  by_cases hφψ : φ = ψ
  · subst hφψ
    refine ⟨a • e, ?_, ?_⟩ <;> simp [map_smul, smul_eq_mul, hφ.1, hab rfl]
  obtain ⟨c, hc⟩ := DFunLike.exists_ne hφψ
  let δ : ℝ := φ c - ψ c
  have hδ : δ ≠ 0 := sub_ne_zero.mpr hc
  let q : ℝ := (a - b) / δ
  let p : ℝ := a - q * φ c
  refine ⟨p • e + q • c, ?_, ?_⟩
  · simp [map_add, map_smul, smul_eq_mul, hφ.1, p]
  · have hψpq : ψ (p • e + q • c) = p + q * ψ c := by
      simp [map_add, map_smul, smul_eq_mul, hψ.1]
    have hδ' : q * δ = a - b := by
      simp [q, div_mul_cancel₀ _ hδ]
    have : p + q * ψ c = a - q * δ := by
      unfold p δ
      ring
    rw [hψpq, this]
    linarith [hδ']

include hball in
omit [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- The Kakutani representation of the zero AM space, on the empty compact space. -/
private theorem exists_am_representation_of_eq_zero (he : e = 0) :
    ∃ K : CompHaus.{u}, ∃ U : E ≃ₗᵢ[ℝ] C(K, ℝ),
      U e = 1 ∧ ∀ x y, U (x ⊔ y) = U x ⊔ U y := by
  have _ : Subsingleton E := subsingleton_of_amUnit_eq_zero hball he
  have hempty : amLatticeHomSet e = ∅ := by
    ext φ
    simp only [amLatticeHomSet, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    intro hφ
    have hφe := hφ.1
    rw [he, map_zero] at hφe
    exact zero_ne_one hφe
  have hcomp : IsCompact (amLatticeHomSet e) := by simp [hempty]
  let : CompactSpace (↥(amLatticeHomSet e)) := isCompact_iff_compactSpace.mp hcomp
  let : T2Space (↥(amLatticeHomSet e)) := inferInstance
  let K : CompHaus.{u} := CompHaus.of (↥(amLatticeHomSet e))
  have hEmpty : IsEmpty K := by
    rw [show (K : Type u) = ↥(amLatticeHomSet e) from CompHausLike.coe_of _ _]
    rw [hempty]
    infer_instance
  have hsubC : Subsingleton C(K, ℝ) := ⟨fun f g => by ext x; exact hEmpty.elim x⟩
  let L : E →ₗᵢ[ℝ] C(K, ℝ) :=
    { toLinearMap := (0 : E →ₗ[ℝ] C(K, ℝ))
      norm_map' := fun x => by
        have hx : x = (0 : E) := Subsingleton.elim x 0
        rw [hx, LinearMap.zero_apply, norm_zero, norm_zero] }
  have hsurj : Function.Surjective L := fun f => ⟨0, hsubC.elim _ _⟩
  let U := LinearIsometryEquiv.ofSurjective L hsurj
  refine ⟨K, U, ?_, ?_⟩
  · exact hsubC.elim _ _
  · intro x y
    exact hsubC.elim _ _

include he0 hball in
/-- **19.27**. An AM space with unit is lattice isometric to `C(K, ℝ)`. -/
theorem exists_am_representation [CompleteSpace E] :
    ∃ K : CompHaus.{u}, ∃ U : E ≃ₗᵢ[ℝ] C(K, ℝ),
      U e = 1 ∧ ∀ x y, U (x ⊔ y) = U x ⊔ U y := by
  by_cases he : e = 0
  · exact exists_am_representation_of_eq_zero hball he
  have hcomp : IsCompact (amLatticeHomSet e) := isCompact_amLatticeHomSet he0 hball he
  let : CompactSpace (↥(amLatticeHomSet e)) := isCompact_iff_compactSpace.mp hcomp
  let : T2Space (↥(amLatticeHomSet e)) := inferInstance
  let K : CompHaus.{u} := CompHaus.of (↥(amLatticeHomSet e))
  let evalC : E → C(K, ℝ) := fun x =>
    ⟨fun φ => (φ : WeakDual ℝ E) x,
      (eval_continuous x).comp continuous_subtype_val⟩
  have heval_sup : ∀ x y, evalC (x ⊔ y) = evalC x ⊔ evalC y := by
    intro x y
    ext φ
    rw [ContinuousMap.sup_apply]
    exact amLatticeHom_map_sup φ.property x y
  have heval_inf : ∀ x y, evalC (x ⊓ y) = evalC x ⊓ evalC y := by
    intro x y
    ext φ
    rw [ContinuousMap.inf_apply]
    exact amLatticeHom_map_inf φ.property x y
  let L : E →ₗᵢ[ℝ] C(K, ℝ) :=
    { toLinearMap :=
        { toFun := evalC
          map_add' := fun x y => by ext φ; simp [evalC, map_add]
          map_smul' := fun c x => by ext φ; simp [evalC, map_smul, smul_eq_mul] }
      norm_map' := fun x => by
        rw [ContinuousMap.norm_eq_iSup_norm]
        have hne : Nonempty K := (amLatticeHomSet_nonempty he0 hball he).to_subtype
        have hsup : ⨆ φ : K, ‖evalC x φ‖ = ‖x‖ := by
          have hrange : range (fun φ : K => |((φ : WeakDual ℝ E) x)|) =
              (fun ψ : WeakDual ℝ E => |ψ x|) '' amLatticeHomSet e := by
            ext t
            constructor
            · rintro ⟨φ, rfl⟩
              exact ⟨φ, φ.property, rfl⟩
            · rintro ⟨ψ, hψ, rfl⟩
              exact ⟨⟨ψ, hψ⟩, rfl⟩
          rw [show ⨆ φ : K, ‖evalC x φ‖ =
              sSup (range fun φ : K => |((φ : WeakDual ℝ E) x)|) by
                simp [evalC, Real.norm_eq_abs, iSup]]
          rw [hrange, csSup_amLatticeHom_abs he0 hball he x]
        exact hsup }
  have hsep : (range L).SeparatesPointsStrongly := by
    intro v φ ψ
    obtain ⟨x, hxφ, hxψ⟩ := exists_amLatticeHom_eq_and_eq φ.property ψ.property (v φ) (v ψ)
      (fun h => by rw [Subtype.ext h])
    exact ⟨L x, ⟨x, rfl⟩, hxφ, hxψ⟩
  have hclosed : IsClosed (range L) :=
    L.antilipschitzWith.isClosed_range L.lipschitzWith.uniformContinuous
  have htop : range L = univ := by
    have hcl := ContinuousMap.sublattice_closure_eq_top (range L) ⟨L 0, 0, rfl⟩
      (fun f hf g hg => by
        obtain ⟨x, rfl⟩ := hf
        obtain ⟨y, rfl⟩ := hg
        refine ⟨x ⊓ y, ?_⟩
        ext φ
        simp [L, evalC, heval_inf])
      (fun f hf g hg => by
        obtain ⟨x, rfl⟩ := hf
        obtain ⟨y, rfl⟩ := hg
        refine ⟨x ⊔ y, ?_⟩
        ext φ
        simp [L, evalC, heval_sup])
      hsep
    rw [IsClosed.closure_eq hclosed] at hcl
    simpa using hcl
  let U := LinearIsometryEquiv.ofSurjective L (range_eq_univ.mp htop)
  refine ⟨K, U, ?_, ?_⟩
  · ext φ
    simp [U, L, evalC, φ.property.1]
  · intro x y
    ext φ
    simp [U, L, evalC, heval_sup]


end CKMA
