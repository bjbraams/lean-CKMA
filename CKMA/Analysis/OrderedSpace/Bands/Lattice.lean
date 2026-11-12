/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Tactic

/-!
# Lattice calculus for real Riesz spaces

Decomposition, scalar identities, and least-upper-bound calculus used for band projections,
Freudenthal approximation, and the Riesz–Kantorovich formulas. The arguments follow the
standard identities in Aliprantis–Burkinshaw, *Positive Operators*, §§1.1 and 1.3.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace CKMA

open Finset

variable {E F : Type*} [AddCommGroup E] [Lattice E] [Module ℝ E]
    [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]

/-- Disjoint vectors in a Riesz space, using lattice absolute values. -/
def LatticeDisjoint (x y : E) : Prop := |x| ⊓ |y| = 0

/-- Lattice disjointness is symmetric. -/
theorem LatticeDisjoint.symm {x y : E} (h : LatticeDisjoint x y) :
    LatticeDisjoint y x := by
  simpa only [LatticeDisjoint, inf_comm] using h

/-- A smaller pair of absolute values remains disjoint. -/
theorem LatticeDisjoint.of_abs_le {x y x' y' : E} (h : LatticeDisjoint x y)
    (hx : |x'| ≤ |x|) (hy : |y'| ≤ |y|) : LatticeDisjoint x' y' := by
  refine le_antisymm ?_ (le_inf (abs_nonneg x') (abs_nonneg y'))
  exact (inf_le_inf hx hy).trans (le_of_eq h)

/-- The disjoint complement of an arbitrary set of vectors. -/
def latticeDisjointComplement (s : Set E) : Set E :=
  {x | ∀ y ∈ s, LatticeDisjoint x y}

/-- Every vector lies in the double disjoint complement of its singleton. -/
theorem mem_doubleLatticeDisjointComplement (x : E) :
    x ∈ latticeDisjointComplement (latticeDisjointComplement {x}) := by
  intro y hy
  exact (hy x (Set.mem_singleton x)).symm

/-- The disjoint complement of zero is the whole space. -/
theorem latticeDisjointComplement_singleton_zero :
    latticeDisjointComplement {(0 : E)} = Set.univ := by
  ext x
  constructor
  · intro _
    exact Set.mem_univ x
  · intro _ y hy
    have hy0 : y = 0 := Set.mem_singleton_iff.mp hy
    rw [LatticeDisjoint, hy0, abs_zero, inf_eq_right.2 (abs_nonneg x)]

/-- Only zero is disjoint from every vector. -/
theorem latticeDisjointComplement_univ :
    latticeDisjointComplement (Set.univ : Set E) = {0} := by
  ext x
  constructor
  · intro hx
    have hxx : |x| ⊓ |x| = 0 := by
      simpa [LatticeDisjoint] using hx x (Set.mem_univ x)
    have habs : |x| = 0 := by rwa [inf_idem] at hxx
    have hsum : x⁺ + x⁻ = 0 := by rw [posPart_add_negPart, habs]
    have hxpos : x⁺ = 0 := by
      have hle : x⁺ ≤ x⁺ + x⁻ := le_add_of_nonneg_right (negPart_nonneg x)
      rw [hsum] at hle
      exact le_antisymm hle (posPart_nonneg x)
    have hxneg : x⁻ = 0 := by
      have hle : x⁻ ≤ x⁺ + x⁻ := le_add_of_nonneg_left (posPart_nonneg x)
      rw [hsum] at hle
      exact le_antisymm hle (negPart_nonneg x)
    have hx0 : x = 0 := by
      calc
        x = x⁺ - x⁻ := (posPart_sub_negPart x).symm
        _ = 0 := by rw [hxpos, hxneg, sub_zero]
    exact Set.mem_singleton_iff.mpr hx0
  · intro hx y _
    have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
    rw [LatticeDisjoint, hx0, abs_zero]
    exact inf_eq_left.2 (abs_nonneg y)

/-- The double disjoint complement of zero is zero. -/
theorem doubleLatticeDisjointComplement_zero :
    latticeDisjointComplement (latticeDisjointComplement {(0 : E)}) = {0} := by
  rw [latticeDisjointComplement_singleton_zero, latticeDisjointComplement_univ]

/-- Double disjoint complements grow with the generating positive vector. -/
theorem doubleLatticeDisjointComplement_mono {w v : E} (hw : 0 ≤ w) (hwv : w ≤ v) :
    latticeDisjointComplement (latticeDisjointComplement {w}) ⊆
      latticeDisjointComplement (latticeDisjointComplement {v}) := by
  intro x hx y hy
  have hv : 0 ≤ v := hw.trans hwv
  have habs : |w| ≤ |v| := by
    simpa [abs_of_nonneg hw, abs_of_nonneg hv] using hwv
  have hyw : y ∈ latticeDisjointComplement {w} := by
    intro z hz
    have hzv : LatticeDisjoint y v := hy v (Set.mem_singleton v)
    have hz0 : z = w := Set.mem_singleton_iff.mp hz
    have hzw : |y| ⊓ |z| ≤ |y| ⊓ |v| := by simpa [hz0] using inf_le_inf_left |y| habs
    exact le_antisymm (hzw.trans (le_of_eq hzv))
      (le_inf (abs_nonneg y) (abs_nonneg z))
  exact hx y hyw

/-- Subtracting the infimum leaves the positive part of the difference. -/
theorem sub_inf_eq_posPart_sub (x y : E) : x - (x ⊓ y) = (x - y)⁺ := by
  rw [sub_eq_add_neg, neg_inf, add_sup, add_neg_cancel, ← sub_eq_add_neg, sup_comm]
  rfl

/-- Positive part of a nonpositive element vanishes. -/
theorem posPart_eq_zero_of_nonpos {x : E} (hx : x ≤ 0) : x⁺ = 0 :=
  sup_eq_right.2 hx

/-- Negative part of a nonnegative element vanishes. -/
theorem negPart_eq_zero_of_nonneg {x : E} (hx : 0 ≤ x) : x⁻ = 0 := by
  rw [negPart_def, sup_eq_right.2 (neg_nonpos.2 hx)]

/-- Canonical decomposition of a difference of nonnegative elements with infimum zero. -/
theorem eq_posPart_negPart_of_inf_eq_zero {x y z : E} (_hy : 0 ≤ y) (_hz : 0 ≤ z)
    (hinf : y ⊓ z = 0) (hx : x = y - z) : x⁺ = y ∧ x⁻ = z := by
  have hsup : y ⊔ z = y + z := by
    have hsum : y ⊓ z + (y ⊔ z) = y + z := inf_add_sup y z
    simpa [hinf, zero_add, add_comm] using hsum
  have hpos : x⁺ = y := by
    calc
      x⁺ = (y - z) ⊔ 0 := by simp [hx, posPart]
      _ = (y - z) ⊔ (z - z) := by rw [sub_self]
      _ = (y ⊔ z) - z := by rw [← sup_sub]
      _ = (y + z) - z := by rw [hsup]
      _ = y := by abel
  have hneg : x⁻ = z := by
    have hsub : x⁺ - x = x⁻ := by
      calc
        x⁺ - x = x⁺ - (x⁺ - x⁻) := by rw [posPart_sub_negPart]
        _ = x⁻ := by abel
    rw [← hsub]
    calc
      x⁺ - x = y - (y - z) := by rw [hpos, hx]
      _ = z := by abel
  exact ⟨hpos, hneg⟩

/-- Positive scalar multiplication preserves finite suprema. -/
theorem smul_sup_of_nonneg {c : ℝ} (hc : 0 ≤ c) (x y : E) :
    c • (x ⊔ y) = c • x ⊔ c • y := by
  rcases hc.eq_or_lt with rfl | hc
  · simp
  · refine le_antisymm ?_ ?_
    · have hinv : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
      have hx' : c⁻¹ • (c • x) = x := by
        rw [← mul_smul, inv_mul_cancel₀ hc.ne', one_smul]
      have hy' : c⁻¹ • (c • y) = y := by
        rw [← mul_smul, inv_mul_cancel₀ hc.ne', one_smul]
      have hx : x ≤ c⁻¹ • (c • x ⊔ c • y) := by
        conv_lhs => rw [← hx']
        exact smul_le_smul_of_nonneg_left le_sup_left hinv
      have hy : y ≤ c⁻¹ • (c • x ⊔ c • y) := by
        conv_lhs => rw [← hy']
        exact smul_le_smul_of_nonneg_left le_sup_right hinv
      have hle := smul_le_smul_of_nonneg_left (sup_le hx hy) hc.le
      rwa [← mul_smul, mul_inv_cancel₀ hc.ne', one_smul] at hle
    · exact sup_le (smul_le_smul_of_nonneg_left le_sup_left hc.le)
        (smul_le_smul_of_nonneg_left le_sup_right hc.le)

/-- Positive scalar multiplication preserves finite infima. -/
theorem smul_inf_of_nonneg {c : ℝ} (hc : 0 ≤ c) (x y : E) :
    c • (x ⊓ y) = c • x ⊓ c • y := by
  rw [← neg_neg (c • (x ⊓ y)), ← smul_neg, neg_inf, smul_sup_of_nonneg hc, smul_neg, smul_neg,
    neg_sup]
  simp [neg_neg]

/-- Positive and negative parts scale by a nonnegative real. -/
theorem posPart_smul_of_nonneg {c : ℝ} (hc : 0 ≤ c) (x : E) : (c • x)⁺ = c • x⁺ :=
  (eq_posPart_negPart_of_inf_eq_zero (smul_nonneg hc (posPart_nonneg x))
    (smul_nonneg hc (negPart_nonneg x))
    (by rw [← smul_inf_of_nonneg hc, posPart_inf_negPart_eq_zero, smul_zero])
    (by rw [← smul_sub, posPart_sub_negPart])).1

/-- Negative parts scale by a nonnegative real. -/
theorem negPart_smul_of_nonneg {c : ℝ} (hc : 0 ≤ c) (x : E) : (c • x)⁻ = c • x⁻ :=
  (eq_posPart_negPart_of_inf_eq_zero (smul_nonneg hc (posPart_nonneg x))
    (smul_nonneg hc (negPart_nonneg x))
    (by rw [← smul_inf_of_nonneg hc, posPart_inf_negPart_eq_zero, smul_zero])
    (by rw [← smul_sub, posPart_sub_negPart])).2

/-- Absolute value is homogeneous over the scalar field of a Riesz space. -/
theorem abs_smul (c : ℝ) (x : E) : |c • x| = |c| • |x| := by
  rcases le_total 0 c with hc | hc
  · rw [abs_of_nonneg hc, ← posPart_add_negPart (c • x), posPart_smul_of_nonneg hc,
      negPart_smul_of_nonneg hc, ← smul_add, posPart_add_negPart]
  · have hc' : 0 ≤ -c := neg_nonneg.2 hc
    rw [abs_of_nonpos hc, show c • x = -((-c) • x) by rw [neg_smul, neg_neg], abs_neg,
      ← posPart_add_negPart ((-c) • x), posPart_smul_of_nonneg hc',
      negPart_smul_of_nonneg hc', ← smul_add, posPart_add_negPart]

/-- Riesz decomposition of a positive element dominated by a sum of two positive elements. -/
theorem exists_add_eq_of_le_add {x y z : E} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : x ≤ y + z) :
    ∃ x₁ x₂ : E, x = x₁ + x₂ ∧ 0 ≤ x₁ ∧ x₁ ≤ y ∧ 0 ≤ x₂ ∧ x₂ ≤ z := by
  refine ⟨x ⊓ y, x - x ⊓ y, by abel, le_inf hx hy, inf_le_right, ?_, ?_⟩
  · rw [sub_inf_eq_posPart_sub]
    exact posPart_nonneg _
  · rw [sub_inf_eq_posPart_sub]
    exact sup_le ((sub_le_iff_le_add).2 (by rwa [add_comm])) hz

/-- The infimum of a sum is dominated by the sum of the infima, for nonnegative elements. -/
theorem inf_add_le_add_inf {x y z : E} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x ⊓ (y + z) ≤ x ⊓ y + x ⊓ z := by
  set w := x ⊓ (y + z)
  have hw_le_x : w ≤ x := inf_le_left
  have hw_le_sum : w ≤ y + z := inf_le_right
  have hwy : w - y ≤ z := (sub_le_iff_le_add').2 hw_le_sum
  have hwyx : w - y ≤ x := (sub_le_self _ hy).trans hw_le_x
  have hwy_inf : w - y ≤ x ⊓ z := le_inf hwyx hwy
  have hw_le : w ≤ y + (x ⊓ z) := (sub_le_iff_le_add').1 hwy_inf
  have hwz : w - (x ⊓ z) ≤ y := (sub_le_iff_le_add).2 hw_le
  have hwx : w - (x ⊓ z) ≤ x :=
    (sub_le_self _ (le_inf hx hz)).trans hw_le_x
  have hfinal : w ≤ (x ⊓ z) + (x ⊓ y) := (sub_le_iff_le_add').1 (le_inf hwx hwz)
  simpa [add_comm] using hfinal

/-- A nonnegative element disjoint from `y` remains disjoint after multiplication by a natural. -/
theorem inf_nsmul_eq_zero {x y : E} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ⊓ y = 0) (n : ℕ) :
    (n • x) ⊓ y = 0 := by
  induction n with
  | zero => simp [hy]
  | succ n ih =>
    have hnx : 0 ≤ n • x := nsmul_nonneg hx n
    have hle : y ⊓ ((n • x) + x) ≤ y ⊓ (n • x) + y ⊓ x :=
      inf_add_le_add_inf hy hnx hx
    rw [inf_comm] at ih
    have hxy' : y ⊓ x = 0 := by rwa [inf_comm]
    rw [hxy', ih, add_zero] at hle
    have hsum : (n + 1) • x = n • x + x := succ_nsmul x n
    rw [← hsum, inf_comm] at hle
    exact le_antisymm hle (le_inf (nsmul_nonneg hx _) hy)

/-- A nonnegative element disjoint from `y` remains disjoint after nonnegative scaling. -/
theorem inf_smul_eq_zero {c : ℝ} (hc : 0 ≤ c) {x y : E} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x ⊓ y = 0) : (c • x) ⊓ y = 0 := by
  obtain ⟨n, hn⟩ := exists_nat_ge c
  have hle : (c • x) ⊓ y ≤ ((n : ℝ) • x) ⊓ y := by
    simpa [inf_comm] using
      inf_le_inf_left y (smul_le_smul_of_nonneg_right hn hx)
  have hn0 : ((n : ℝ) • x) ⊓ y = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    exact inf_nsmul_eq_zero hx hy hxy n
  exact le_antisymm (hle.trans (le_of_eq hn0)) (le_inf (smul_nonneg hc hx) hy)

/-- Disjoint nonnegative elements add as their supremum. -/
theorem add_eq_sup_of_inf_eq_zero {x y : E} (hxy : x ⊓ y = 0) :
    x + y = x ⊔ y := by
  have hsum : x ⊓ y + (x ⊔ y) = x + y := inf_add_sup x y
  simpa [hxy, zero_add] using hsum.symm

/-- Finite infimum-sum estimate for nonnegative families. -/
theorem inf_sum_le_sum_inf {n : ℕ} {x : E} {y : Fin n → E} (hx : 0 ≤ x) (hy : ∀ i, 0 ≤ y i) :
    x ⊓ ∑ i, y i ≤ ∑ i, x ⊓ y i := by
  induction n with
  | zero =>
    simp [hx]
  | succ n ih =>
    have hrest : 0 ≤ ∑ i : Fin n, y i.castSucc :=
      Finset.sum_nonneg fun i _ ↦ hy i.castSucc
    have hih := ih (y := fun i : Fin n ↦ y i.castSucc) (fun i ↦ hy i.castSucc)
    calc
      x ⊓ ∑ i, y i
          = x ⊓ (∑ i : Fin n, y i.castSucc + y (Fin.last n)) := by
            rw [Fin.sum_univ_castSucc]
      _ ≤ x ⊓ ∑ i : Fin n, y i.castSucc + x ⊓ y (Fin.last n) :=
            inf_add_le_add_inf hx hrest (hy _)
      _ ≤ (∑ i : Fin n, x ⊓ y i.castSucc) + x ⊓ y (Fin.last n) :=
            add_le_add_left hih _
      _ = ∑ i, x ⊓ y i := (Fin.sum_univ_castSucc (fun i ↦ x ⊓ y i)).symm

/-- Telescoping difference of a sequence in an additive group. -/
theorem sum_range_sub {G : Type*} [AddCommGroup G] (f : ℕ → G) (n : ℕ) :
    ∑ i ∈ range n, (f i - f (i + 1)) = f 0 - f n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    abel

/-- Positive scaling preserves least upper bounds of nonempty sets. -/
theorem isLUB_smul_of_pos {c : ℝ} (hc : 0 < c) {s : Set E} {a : E} (ha : IsLUB s a) :
    IsLUB ((fun y : E ↦ c • y) '' s) (c • a) := by
  rw [isLUB_iff_le_iff] at ha ⊢
  intro b
  have hinv : 0 < c⁻¹ := inv_pos.2 hc
  constructor
  · intro hb z hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hy' : y ≤ a := (ha a).1 le_rfl hy
    exact (smul_le_smul_of_nonneg_left hy' hc.le).trans hb
  · intro hb
    have hupper : c⁻¹ • b ∈ upperBounds s := by
      intro y hy
      have hmem : c • y ∈ (fun y : E ↦ c • y) '' s := ⟨y, hy, rfl⟩
      have hle : c • y ≤ b := hb hmem
      have hmul := smul_le_smul_of_nonneg_left hle hinv.le
      simpa [smul_smul, inv_mul_cancel₀ hc.ne'] using hmul
    have ha' : a ≤ c⁻¹ • b := (ha (c⁻¹ • b)).2 hupper
    have hmul := smul_le_smul_of_nonneg_left ha' hc.le
    simpa [smul_smul, mul_inv_cancel₀ hc.ne'] using hmul

/-- Addition preserves least upper bounds. -/
theorem isLUB_add {s t : Set E} {a b : E} (hs : IsLUB s a) (ht : IsLUB t b) :
    IsLUB {z : E | ∃ x y, x ∈ s ∧ y ∈ t ∧ z = x + y} (a + b) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨x, y, hx, hy, rfl⟩ := hz
    exact add_le_add (hs.1 hx) (ht.1 hy)
  · intro z hz
    have ha : a ≤ z - b := by
      refine (isLUB_le_iff hs).2 ?_
      intro x hx
      have hb : b ≤ z - x := by
        refine (isLUB_le_iff ht).2 ?_
        intro y hy
        have hxy : x + y ≤ z := hz ⟨x, y, hx, hy, rfl⟩
        exact (le_sub_iff_add_le).2 (by rwa [add_comm])
      exact (le_sub_iff_add_le').2 (by simpa [add_comm, sub_add_cancel] using add_le_add_left hb x)
    exact (le_sub_iff_add_le).1 ha

/-- Existing suprema distribute over infima. -/
theorem isLUB_inf {s : Set E} {a x : E} (ha : IsLUB s a) :
    IsLUB ((fun y ↦ x ⊓ y) '' s) (x ⊓ a) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact inf_le_inf_left x (ha.1 hy)
  · intro z hz
    have hupper : ∀ y ∈ s, y ≤ z + (x ⊔ a) - x := by
      intro y hy
      have hxy : x ⊓ y ≤ z := hz ⟨y, hy, rfl⟩
      have hdecomp : y = x ⊓ y + (x ⊔ y) - x := by
        have hsum : x ⊓ y + (x ⊔ y) = x + y := inf_add_sup x y
        calc
          y = x + y - x := by abel
          _ = x ⊓ y + (x ⊔ y) - x := by rw [hsum]
      have hsup : x ⊔ y ≤ x ⊔ a := sup_le_sup_left (ha.1 hy) x
      calc
        y = x ⊓ y + (x ⊔ y) - x := hdecomp
        _ ≤ z + (x ⊔ a) - x := by
          exact sub_le_sub_right (add_le_add hxy hsup) x
    have ha' : a ≤ z + (x ⊔ a) - x := (isLUB_le_iff ha).2 hupper
    have hxa : x ⊓ a = x + a - (x ⊔ a) := by
      have hsum : x ⊓ a + (x ⊔ a) = x + a := inf_add_sup x a
      calc
        x ⊓ a = x ⊓ a + (x ⊔ a) - (x ⊔ a) := by abel
        _ = x + a - (x ⊔ a) := by rw [hsum]
    have hle : x + a - (x ⊔ a) ≤ z := by
      have hax : a + x ≤ z + (x ⊔ a) := (le_sub_iff_add_le).1 ha'
      rw [add_comm a x] at hax
      exact (sub_le_iff_le_add).2 hax
    simpa [hxa] using hle

section ConeExtension

variable [AddCommGroup F] [Module ℝ F]

/-- An additive, positively homogeneous map on the positive cone extends to a linear map
by the Jordan decomposition. Homogeneity is an explicit hypothesis, so no Archimedean
argument is required. -/
theorem coneAdditive_isLinearMap (f : E → F)
    (hadd : ∀ x y : E, 0 ≤ x → 0 ≤ y → f (x + y) = f x + f y)
    (hsmul : ∀ (c : ℝ) (x : E), 0 ≤ c → 0 ≤ x → f (c • x) = c • f x) :
    IsLinearMap ℝ (fun x : E ↦ f x⁺ - f x⁻) := by
  have hf0 : f 0 = 0 := by
    have h := hadd 0 0 le_rfl le_rfl
    have h' : f 0 + 0 = f 0 + f 0 := by simpa [add_zero] using h
    exact (add_left_cancel h').symm
  have hdiff : ∀ {x a b : E}, 0 ≤ a → 0 ≤ b → x = a - b →
      f x⁺ - f x⁻ = f a - f b := by
    intro x a b ha hb hx
    have hsum : x⁺ + b = a + x⁻ := by
      calc
        x⁺ + b = (x⁺ - x⁻) + x⁻ + b := by abel
        _ = x + x⁻ + b := by rw [posPart_sub_negPart]
        _ = a - b + x⁻ + b := by rw [hx]
        _ = a + x⁻ := by abel
    have hf := hadd _ _ (posPart_nonneg x) hb
    rw [hsum] at hf
    rw [hadd _ _ ha (negPart_nonneg x)] at hf
    exact (sub_eq_sub_iff_add_eq_add).2 hf.symm
  have hposneg : ∀ {c : ℝ} {x : E}, 0 ≤ c → (c • x)⁺ = c • x⁺ ∧ (c • x)⁻ = c • x⁻ := by
    intro c x hc
    exact eq_posPart_negPart_of_inf_eq_zero (smul_nonneg hc (posPart_nonneg _))
      (smul_nonneg hc (negPart_nonneg _))
      (by rw [← smul_inf_of_nonneg hc, posPart_inf_negPart_eq_zero, smul_zero])
      (by rw [← smul_sub, posPart_sub_negPart])
  let g : E → F := fun x ↦ f x⁺ - f x⁻
  have hadd_g : ∀ x y, g (x + y) = g x + g y := by
    intro x y
    have hx : x + y = (x⁺ + y⁺) - (x⁻ + y⁻) := by
      calc
        x + y = (x⁺ - x⁻) + (y⁺ - y⁻) := by rw [posPart_sub_negPart, posPart_sub_negPart]
        _ = (x⁺ + y⁺) - (x⁻ + y⁻) := by abel
    rw [show g (x + y) = f (x + y)⁺ - f (x + y)⁻ from rfl]
    rw [hdiff (add_nonneg (posPart_nonneg _) (posPart_nonneg _))
      (add_nonneg (negPart_nonneg _) (negPart_nonneg _)) hx,
      hadd _ _ (posPart_nonneg _) (posPart_nonneg _),
      hadd _ _ (negPart_nonneg _) (negPart_nonneg _)]
    simp only [g]
    abel
  have hneg_g : ∀ x, g (-x) = -g x := by
    intro x
    have h0 : g (x + -x) = g x + g (-x) := hadd_g x (-x)
    rw [add_neg_cancel, show g 0 = f 0⁺ - f 0⁻ from rfl] at h0
    rw [posPart_eq_zero_of_nonpos le_rfl, negPart_eq_zero_of_nonneg le_rfl, hf0, sub_zero] at h0
    exact eq_neg_of_add_eq_zero_right h0.symm
  have hsmul_nonneg : ∀ {c : ℝ} {x : E}, 0 ≤ c → g (c • x) = c • g x := by
    intro c x hc
    have hparts := hposneg (x := x) hc
    simp only [g, hparts.1, hparts.2, hsmul _ _ hc (posPart_nonneg _),
      hsmul _ _ hc (negPart_nonneg _), ← smul_sub]
  refine ⟨hadd_g, ?_⟩
  intro c x
  rcases le_total 0 c with hc | hc
  · exact hsmul_nonneg hc
  · have hc' : 0 ≤ -c := neg_nonneg.2 hc
    calc
      g (c • x) = g (-((-c) • x)) := by rw [neg_smul, neg_neg]
      _ = -g ((-c) • x) := hneg_g _
      _ = -((-c) • g x) := by rw [hsmul_nonneg hc']
      _ = c • g x := by rw [neg_smul, neg_neg]

/-- The linear extension of an additive positively homogeneous cone map. -/
def coneAdditiveLinearMap (f : E → F)
    (hadd : ∀ x y : E, 0 ≤ x → 0 ≤ y → f (x + y) = f x + f y)
    (hsmul : ∀ (c : ℝ) (x : E), 0 ≤ c → 0 ≤ x → f (c • x) = c • f x) : E →ₗ[ℝ] F :=
  IsLinearMap.mk' (fun x ↦ f x⁺ - f x⁻) (coneAdditive_isLinearMap f hadd hsmul)

/-- On the positive cone the extension reproduces `f`. -/
theorem coneAdditiveLinearMap_apply_of_nonneg (f : E → F)
    (hadd : ∀ x y : E, 0 ≤ x → 0 ≤ y → f (x + y) = f x + f y)
    (hsmul : ∀ (c : ℝ) (x : E), 0 ≤ c → 0 ≤ x → f (c • x) = c • f x)
    {x : E} (hx : 0 ≤ x) :
    coneAdditiveLinearMap f hadd hsmul x = f x := by
  have hf0 : f 0 = 0 := by
    have h := hadd 0 0 le_rfl le_rfl
    have h' : f 0 + 0 = f 0 + f 0 := by simpa [add_zero] using h
    exact (add_left_cancel h').symm
  rw [coneAdditiveLinearMap, IsLinearMap.mk'_apply, posPart_eq_self.2 hx,
    negPart_eq_zero_of_nonneg hx, hf0, sub_zero]

end ConeExtension

end CKMA
