/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.OrderedSpace.Bands.Basic
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Tactic.Abel

/-!
# Contractive projections on Riesz spaces

A linear map is contractive when it maps the positive cone into the order interval from zero
to its argument; an order projection (`CKMA.IsOrderProjection`) is an idempotent contractive
map. Order projections are disjoint from the complementary projection, absolute values pass
inside, and a smaller range yields a smaller projection.

## Main results

* `CKMA.contractiveProjection_abs`: absolute value commutes with a contractive linear map.
* `CKMA.IsOrderProjection.latticeDisjoint`: an order projection is lattice-disjoint from its
  complement.
* `CKMA.IsOrderProjection.le_of_range_subset`: an order projection dominates every contractive
  map with smaller range.
* `CKMA.IsOrderProjection.sub`: the difference of nested order projections is an order
  projection.
-/

public section

noncomputable section

namespace CKMA

variable {E : Type*} [AddCommGroup E] [Lattice E] [Module ℝ E]
    [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]

omit [IsOrderedModule ℝ E] in
/-- The complement of a contractive positive projection is nonnegative on the cone. -/
theorem contractiveProjection_complement_nonneg {P : E →ₗ[ℝ] E}
    (hcon : ∀ x, 0 ≤ x → P x ≤ x) {x : E} (hx : 0 ≤ x) : 0 ≤ x - P x :=
  sub_nonneg.2 (hcon x hx)

omit [IsOrderedModule ℝ E] in
/-- The complement of a contractive positive projection is monotone. -/
private theorem contractiveProjection_complement_monotone {P : E →ₗ[ℝ] E}
    (hcon : ∀ x, 0 ≤ x → P x ≤ x) : Monotone fun x => x - P x := by
  intro a b hab
  have hba : 0 ≤ b - a := sub_nonneg.2 hab
  have h0 : 0 ≤ (b - a) - P (b - a) :=
    sub_nonneg.2 (hcon (b - a) hba)
  have hdiff : (b - a) - P (b - a) = (b - P b) - (a - P a) := by
    rw [map_sub]
    abel
  exact sub_nonneg.1 (by rw [← hdiff]; exact h0)

omit [IsOrderedModule ℝ E] in
/-- Positive values of an order projection are disjoint from the complement. -/
theorem IsOrderProjection.inf_sub_eq_zero {P : E →ₗ[ℝ] E} (hP : IsOrderProjection P)
    {x y : E} (hx : 0 ≤ x) (hy : 0 ≤ y) : P x ⊓ (y - P y) = 0 := by
  have hidem := hP.idem
  have hcon := hP.nonneg_le
  have hpos : ∀ z, 0 ≤ z → 0 ≤ P z := fun z hz => (hcon z hz).1
  have hle : ∀ z, 0 ≤ z → P z ≤ z := fun z hz => (hcon z hz).2
  have hmono : Monotone P := (monotone_iff_map_nonneg P).2 hpos
  have hImono : Monotone (fun z => z - P z) :=
    contractiveProjection_complement_monotone hle
  set z := P x ⊓ (y - P y)
  have hz0 : 0 ≤ z :=
    le_inf (hpos x hx) (contractiveProjection_complement_nonneg hle hy)
  have hPz : P z = 0 := by
    have hle' : P z ≤ P (y - P y) := hmono inf_le_right
    have hpy : P (y - P y) = 0 := by rw [map_sub, hidem, sub_self]
    exact le_antisymm (hle'.trans (le_of_eq hpy)) (hpos z hz0)
  have hIz : z - P z = 0 := by
    have hle' : z - P z ≤ P x - P (P x) := hImono inf_le_left
    rw [hidem, sub_self] at hle'
    exact le_antisymm hle' (contractiveProjection_complement_nonneg hle hz0)
  have hz : z = P z + (z - P z) := by abel
  rw [hIz, add_zero, hPz] at hz
  exact hz

omit [IsOrderedModule ℝ E] in
/-- Absolute value passes inside a contractive projection. -/
theorem contractiveProjection_abs {P : E →ₗ[ℝ] E}
    (hcon : ∀ x, 0 ≤ x → 0 ≤ P x ∧ P x ≤ x)
    (x : E) : |P x| = P |x| := by
  have hpos : ∀ z, 0 ≤ z → 0 ≤ P z := fun z hz => (hcon z hz).1
  have hle : ∀ z, 0 ≤ z → P z ≤ z := fun z hz => (hcon z hz).2
  have hdisj : P x⁺ ⊓ P x⁻ = 0 := by
    refine le_antisymm ?_ (le_inf (hpos _ (posPart_nonneg x)) (hpos _ (negPart_nonneg x)))
    exact (inf_le_inf (hle _ (posPart_nonneg x)) (hle _ (negPart_nonneg x))).trans
      (le_of_eq (posPart_inf_negPart_eq_zero x))
  have habs : |P x⁺ - P x⁻| = P x⁺ + P x⁻ := by
    rw [← posPart_add_negPart (P x⁺ - P x⁻)]
    have hparts := eq_posPart_negPart_of_inf_eq_zero hdisj rfl
    rw [hparts.1, hparts.2]
  calc
    |P x| = |P (x⁺ - x⁻)| := by rw [posPart_sub_negPart]
    _ = |P x⁺ - P x⁻| := by rw [map_sub]
    _ = P x⁺ + P x⁻ := habs
    _ = P (x⁺ + x⁻) := by rw [← map_add]
    _ = P |x| := by rw [posPart_add_negPart]

omit [IsOrderedModule ℝ E] in
/-- Absolute value passes inside the complementary projection. -/
private theorem contractiveProjection_complement_abs {P : E →ₗ[ℝ] E}
    (hcon : ∀ x, 0 ≤ x → 0 ≤ P x ∧ P x ≤ x)
    (x : E) : |x - P x| = |x| - P |x| := by
  have hpos : ∀ z, 0 ≤ z → 0 ≤ P z := fun z hz => (hcon z hz).1
  have hle : ∀ z, 0 ≤ z → P z ≤ z := fun z hz => (hcon z hz).2
  let a := x⁺ - P x⁺
  let b := x⁻ - P x⁻
  have ha : 0 ≤ a := contractiveProjection_complement_nonneg hle (posPart_nonneg x)
  have hb : 0 ≤ b := contractiveProjection_complement_nonneg hle (negPart_nonneg x)
  have hdisj : a ⊓ b = 0 := by
    refine le_antisymm ?_ (le_inf ha hb)
    have hleab : a ⊓ b ≤ x⁺ ⊓ x⁻ :=
      inf_le_inf (sub_le_self _ (hpos _ (posPart_nonneg x)))
        (sub_le_self _ (hpos _ (negPart_nonneg x)))
    exact hleab.trans (le_of_eq (posPart_inf_negPart_eq_zero x))
  have habs : |a - b| = a + b := by
    rw [← posPart_add_negPart (a - b)]
    have hparts := eq_posPart_negPart_of_inf_eq_zero hdisj rfl
    rw [hparts.1, hparts.2]
  have hx' : x = x⁺ - x⁻ := (posPart_sub_negPart x).symm
  have hsplit : x - P x = a - b := by
    dsimp [a, b]
    calc
      x - P x = (x⁺ - x⁻) - P x := by
        conv_lhs => lhs; rw [hx']
      _ = (x⁺ - x⁻) - P (x⁺ - x⁻) := by
        conv_lhs => rhs; rw [hx']
      _ = (x⁺ - x⁻) - (P x⁺ - P x⁻) := by rw [map_sub]
      _ = (x⁺ - P x⁺) - (x⁻ - P x⁻) := by abel
  calc
    |x - P x| = |a - b| := by rw [hsplit]
    _ = a + b := habs
    _ = |x| - P |x| := by
      dsimp [a, b]
      calc
        (x⁺ - P x⁺) + (x⁻ - P x⁻) = (x⁺ + x⁻) - (P x⁺ + P x⁻) := by abel
        _ = |x| - P |x| := by rw [← map_add, posPart_add_negPart x]

omit [IsOrderedModule ℝ E] in
/-- An order projection is lattice-disjoint from its complement. -/
theorem IsOrderProjection.latticeDisjoint {P : E →ₗ[ℝ] E} (hP : IsOrderProjection P)
    (x y : E) : LatticeDisjoint (P x) (y - P y) := by
  rw [LatticeDisjoint, contractiveProjection_abs hP.nonneg_le x,
    contractiveProjection_complement_abs hP.nonneg_le y]
  exact hP.inf_sub_eq_zero (abs_nonneg x) (abs_nonneg y)

omit [IsOrderedModule ℝ E] in
/-- On the positive cone, an order projection is the maximum of its range in the order
interval. -/
private theorem IsOrderProjection.isLUB {P : E →ₗ[ℝ] E} (hP : IsOrderProjection P)
    {x : E} (hx : 0 ≤ x) :
    IsLUB {y | y ∈ LinearMap.range P ∧ 0 ≤ y ∧ y ≤ x} (P x) := by
  have hidem := hP.idem
  have hcon := hP.nonneg_le
  have hmono : Monotone P :=
    (monotone_iff_map_nonneg P).2 fun z hz => (hcon z hz).1
  refine ⟨?_, ?_⟩
  · intro y hy
    have hyfix : P y = y := by
      obtain ⟨z, hz⟩ := hy.1
      rw [← hz, hidem]
    calc
      y = P y := hyfix.symm
      _ ≤ P x := hmono hy.2.2
  · intro b hb
    exact hb ⟨LinearMap.mem_range_self P x, (hcon x hx).1, (hcon x hx).2⟩

omit [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] in
/-- A contractive projection fixes every vector of its range. -/
theorem contractiveProjection_eq_of_mem_range {P : E →ₗ[ℝ] E}
    (hidem : ∀ x, P (P x) = P x) {y : E} (hy : y ∈ LinearMap.range P) :
    P y = y := by
  obtain ⟨z, hz⟩ := hy
  rw [← hz, hidem]

omit [IsOrderedModule ℝ E] in
/-- A contractive map whose range lies in the range of an order projection is smaller on the
positive cone. -/
theorem IsOrderProjection.le_of_range_subset {P Q : E →ₗ[ℝ] E} (hP : IsOrderProjection P)
    (hQcon : ∀ x, 0 ≤ x → 0 ≤ Q x ∧ Q x ≤ x)
    (hsubset : (LinearMap.range Q : Set E) ⊆ (LinearMap.range P : Set E))
    {x : E} (hx : 0 ≤ x) : Q x ≤ P x := by
  have hmem : Q x ∈ {y | y ∈ LinearMap.range P ∧ 0 ≤ y ∧ y ≤ x} :=
    ⟨hsubset (LinearMap.mem_range_self Q x), (hQcon x hx).1, (hQcon x hx).2⟩
  exact (hP.isLUB hx).1 hmem

omit [Lattice E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] in
/-- A contractive projection fixes a map whose range it contains. -/
private theorem contractiveProjection_comp_eq_of_range_subset {P Q : E →ₗ[ℝ] E}
    (hPidem : ∀ x, P (P x) = P x)
    (hsubset : (LinearMap.range Q : Set E) ⊆ (LinearMap.range P : Set E)) :
    P.comp Q = Q := by
  ext x
  exact contractiveProjection_eq_of_mem_range hPidem
    (hsubset (LinearMap.mem_range_self Q x))

omit [IsOrderedModule ℝ E] in
/-- For nested order projections, the smaller one absorbs the larger. -/
theorem IsOrderProjection.comp_eq_of_range_subset {P Q : E →ₗ[ℝ] E}
    (hP : IsOrderProjection P) (hQ : IsOrderProjection Q)
    (hsubset : (LinearMap.range Q : Set E) ⊆ (LinearMap.range P : Set E)) :
    Q.comp P = Q := by
  have hPidem := hP.idem
  have hPcon := hP.nonneg_le
  have hpos : ∀ {x : E}, 0 ≤ x → Q (P x) = Q x := by
    intro x hx
    have hPx : 0 ≤ P x := (hPcon x hx).1
    have hQPx := hQ.isLUB hPx
    have hQx := hQ.isLUB hx
    have hmono : Monotone P :=
      (monotone_iff_map_nonneg P).2 fun z hz => (hPcon z hz).1
    have hset :
        {y | y ∈ LinearMap.range Q ∧ 0 ≤ y ∧ y ≤ P x} =
          {y | y ∈ LinearMap.range Q ∧ 0 ≤ y ∧ y ≤ x} := by
      ext y
      constructor
      · intro hy
        exact ⟨hy.1, hy.2.1, hy.2.2.trans (hPcon x hx).2⟩
      · intro hy
        refine ⟨hy.1, hy.2.1, ?_⟩
        have hyfix : P y = y :=
          contractiveProjection_eq_of_mem_range hPidem (hsubset hy.1)
        calc
          y = P y := hyfix.symm
          _ ≤ P x := hmono hy.2.2
    rw [hset] at hQPx
    exact IsLUB.unique hQPx hQx
  ext x
  rw [LinearMap.comp_apply, ← posPart_sub_negPart x, map_sub, map_sub, map_sub,
    hpos (posPart_nonneg x), hpos (negPart_nonneg x)]

omit [IsOrderedModule ℝ E] in
/-- The difference of nested order projections is an order projection. -/
theorem IsOrderProjection.sub {P Q : E →ₗ[ℝ] E} (hP : IsOrderProjection P)
    (hQ : IsOrderProjection Q)
    (hsubset : (LinearMap.range Q : Set E) ⊆ (LinearMap.range P : Set E)) :
    IsOrderProjection (P - Q) := by
  have hPidem := hP.idem
  have hPcon := hP.nonneg_le
  have hQidem := hQ.idem
  have hQcon := hQ.nonneg_le
  have hPQ : P.comp Q = Q :=
    contractiveProjection_comp_eq_of_range_subset hPidem hsubset
  have hQP : Q.comp P = Q := hP.comp_eq_of_range_subset hQ hsubset
  refine ⟨?_, ?_⟩
  · intro x
    have hPQx : P (Q x) = Q x := by
      simpa [LinearMap.comp_apply] using congrFun (congrArg DFunLike.coe hPQ) x
    have hQPx : Q (P x) = Q x := by
      simpa [LinearMap.comp_apply] using congrFun (congrArg DFunLike.coe hQP) x
    calc
      (P - Q) ((P - Q) x)
          = P (P x - Q x) - Q (P x - Q x) := by
            simp only [LinearMap.sub_apply]
      _ = (P (P x) - P (Q x)) - (Q (P x) - Q (Q x)) := by
            rw [map_sub, map_sub]
      _ = (P x - Q x) - (Q x - Q x) := by
            rw [hPidem, hPQx, hQPx, hQidem]
      _ = (P - Q) x := by
            simp only [LinearMap.sub_apply, sub_self, sub_zero]
  · intro x hx
    have hle : Q x ≤ P x :=
      hP.le_of_range_subset hQcon hsubset hx
    refine ⟨sub_nonneg.2 hle, ?_⟩
    exact (sub_le_self _ (hQcon x hx).1).trans (hPcon x hx).2

end CKMA
