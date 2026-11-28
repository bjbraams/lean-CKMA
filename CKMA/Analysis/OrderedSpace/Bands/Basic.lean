/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.OrderedSpace.Bands.Lattice
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Abel

/-!
# Order projections, components, principal ideals and the order-unit gauge

Basic predicates of the band theory of a real Riesz space, and the order-unit gauge of a
principal ideal.

An order projection is an idempotent linear map `P` with `0 ≤ P x ≤ x` for `0 ≤ x`. A component
of a positive vector `u` is a vector `v` with `0 ≤ v ≤ u` and `v ⊓ (u - v) = 0`. The principal
projection property asks for an order projection onto the double disjoint complement of every
singleton. The principal order ideal of `u` consists of the vectors with `|x| ≤ c • u` for some
`c ≥ 0`, and the order-unit gauge of `x` is the infimum of these scalars `c`. Since `Real.sInf`
of the empty set is `0`, the gauge is meaningful only on the principal ideal.

## Main definitions

* `CKMA.IsOrderProjection`: idempotent linear map with `0 ≤ P x ≤ x` on the positive cone.
* `CKMA.IsLatticeComponent`: component of a positive vector, disjoint from its remainder.
* `CKMA.HasPrincipalBandProjections`: principal projection property.
* `CKMA.principalOrderIdeal`: principal order ideal of a vector, and
  `CKMA.principalOrderIdealSubmodule`, the same set as a real linear subspace.
* `CKMA.orderUnitGauge`: order-unit gauge on a principal ideal.

## Main results

* `CKMA.principalOrderIdeal_add`, `CKMA.principalOrderIdeal_smul`, `CKMA.principalOrderIdeal_sup`,
  `CKMA.principalOrderIdeal_inf`: closure properties of a principal ideal.
* `CKMA.abs_le_orderUnitGauge_smul`, `CKMA.orderUnitGauge_le_iff`: in a normed lattice with a solid
  norm, the gauge attains `|x| ≤ c • u` and is the least such scalar.
* `CKMA.orderUnitGauge_smul`, `CKMA.orderUnitGauge_add_le`: absolute homogeneity and
  subadditivity of the gauge.
-/

public section

noncomputable section

namespace CKMA

section Projections

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [Module ℝ E]

/-- An order projection: an idempotent linear map with `0 ≤ P x ≤ x` for every `0 ≤ x`. -/
structure IsOrderProjection (P : E →ₗ[ℝ] E) : Prop where
  /-- Idempotence. -/
  idem : ∀ x, P (P x) = P x
  /-- Positivity and contractivity on the positive cone. -/
  nonneg_le : ∀ x, 0 ≤ x → 0 ≤ P x ∧ P x ≤ x

/-- Defining property of `IsOrderProjection`. -/
theorem isOrderProjection_iff {P : E →ₗ[ℝ] E} :
    IsOrderProjection P ↔ (∀ x, P (P x) = P x) ∧ ∀ x, 0 ≤ x → 0 ≤ P x ∧ P x ≤ x :=
  ⟨fun h ↦ ⟨h.idem, h.nonneg_le⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- An order projection is positive. -/
theorem IsOrderProjection.nonneg {P : E →ₗ[ℝ] E} (hP : IsOrderProjection P) {x : E}
    (hx : 0 ≤ x) : 0 ≤ P x :=
  (hP.nonneg_le x hx).1

/-- An order projection is below the identity on the positive cone. -/
theorem IsOrderProjection.le {P : E →ₗ[ℝ] E} (hP : IsOrderProjection P) {x : E} (hx : 0 ≤ x) :
    P x ≤ x :=
  (hP.nonneg_le x hx).2

end Projections

variable {E : Type*} [AddCommGroup E] [Lattice E] [Module ℝ E]
    [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]

/-- An element is a component of a nonnegative order unit when it is disjoint from its remainder. -/
@[expose]
def IsLatticeComponent (v u : E) : Prop := 0 ≤ v ∧ v ≤ u ∧ v ⊓ (u - v) = 0

omit [Module ℝ E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] in
/-- Defining property of `IsLatticeComponent`. -/
theorem isLatticeComponent_iff {v u : E} :
    IsLatticeComponent v u ↔ 0 ≤ v ∧ v ≤ u ∧ v ⊓ (u - v) = 0 := Iff.rfl

/-- The principal projection property: for every `u` there is an order projection onto the
double disjoint complement of `{u}`. -/
@[expose]
def HasPrincipalBandProjections (E : Type*) [AddCommGroup E] [Lattice E] [Module ℝ E] : Prop :=
  ∀ u : E, ∃ P : E →ₗ[ℝ] E,
    (LinearMap.range P : Set E) = latticeDisjointComplement (latticeDisjointComplement {u}) ∧
    IsOrderProjection P

/-- Defining property of `HasPrincipalBandProjections`. -/
theorem hasPrincipalBandProjections_iff {E : Type*} [AddCommGroup E] [Lattice E] [Module ℝ E] :
    HasPrincipalBandProjections E ↔ ∀ u : E, ∃ P : E →ₗ[ℝ] E,
      (LinearMap.range P : Set E) = latticeDisjointComplement (latticeDisjointComplement {u}) ∧
      IsOrderProjection P := Iff.rfl

section PrincipalOrderIdeal

/-- The principal order ideal of `u`: the vectors `x` with `|x| ≤ c • u` for some `c ≥ 0`. -/
@[expose]
def principalOrderIdeal (u : E) : Set E := {x | ∃ c : ℝ, 0 ≤ c ∧ |x| ≤ c • u}

omit [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] in
/-- Membership in the principal order ideal. -/
theorem mem_principalOrderIdeal {u x : E} :
    x ∈ principalOrderIdeal u ↔ ∃ c : ℝ, 0 ≤ c ∧ |x| ≤ c • u := Iff.rfl

omit [Module ℝ E] [IsOrderedModule ℝ E] in
/-- The absolute value of a supremum is dominated by the supremum of the absolute values. -/
private theorem abs_sup_le_sup_abs (x y : E) : |x ⊔ y| ≤ |x| ⊔ |y| := by
  refine sup_le ?_ ?_
  · exact sup_le_sup (le_abs_self x) (le_abs_self y)
  · rw [neg_sup]
    exact inf_le_left.trans ((neg_le_abs x).trans le_sup_left)

omit [Module ℝ E] [IsOrderedModule ℝ E] in
/-- The absolute value of an infimum is dominated by the supremum of the absolute values. -/
private theorem abs_inf_le_sup_abs (x y : E) : |x ⊓ y| ≤ |x| ⊔ |y| := by
  rw [show x ⊓ y = -(-x ⊔ -y) by rw [← neg_inf, neg_neg], abs_neg]
  exact (abs_sup_le_sup_abs (-x) (-y)).trans (by simp [abs_neg])

/-- Scaling preserves a principal ideal. -/
theorem principalOrderIdeal_smul {u : E} {c : ℝ} {x : E} (hx : x ∈ principalOrderIdeal u) :
    c • x ∈ principalOrderIdeal u := by
  obtain ⟨d, hd, hxd⟩ := hx
  refine ⟨|c| * d, mul_nonneg (abs_nonneg c) hd, ?_⟩
  calc |c • x| = |c| • |x| := abs_smul_of_lattice c x
    _ ≤ |c| • (d • u) := smul_le_smul_of_nonneg_left hxd (abs_nonneg c)
    _ = (|c| * d) • u := by rw [mul_smul]

omit [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] in
/-- Negation preserves a principal ideal. -/
theorem principalOrderIdeal_neg {u x : E} (hx : x ∈ principalOrderIdeal u) :
    -x ∈ principalOrderIdeal u := by
  obtain ⟨c, hc, hxc⟩ := hx
  exact ⟨c, hc, by simpa [abs_neg] using hxc⟩

omit [IsOrderedModule ℝ E] in
/-- Addition preserves a principal ideal. -/
theorem principalOrderIdeal_add {u x y : E} (hx : x ∈ principalOrderIdeal u)
    (hy : y ∈ principalOrderIdeal u) : x + y ∈ principalOrderIdeal u := by
  obtain ⟨c, hc, hxc⟩ := hx
  obtain ⟨d, hd, hyd⟩ := hy
  refine ⟨c + d, add_nonneg hc hd, ?_⟩
  calc |x + y| ≤ |x| + |y| := abs_add_le x y
    _ ≤ c • u + d • u := add_le_add hxc hyd
    _ = (c + d) • u := by rw [add_smul]

omit [IsOrderedModule ℝ E] in
/-- Subtraction preserves a principal ideal. -/
theorem principalOrderIdeal_sub {u x y : E} (hx : x ∈ principalOrderIdeal u)
    (hy : y ∈ principalOrderIdeal u) : x - y ∈ principalOrderIdeal u := by
  simpa [sub_eq_add_neg] using principalOrderIdeal_add hx (principalOrderIdeal_neg hy)

/-- Natural scaling preserves a principal ideal. -/
theorem principalOrderIdeal_nsmul {u : E} {n : ℕ} {x : E} (hx : x ∈ principalOrderIdeal u) :
    n • x ∈ principalOrderIdeal u := by
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  exact principalOrderIdeal_smul hx

/-- Integer scaling preserves a principal ideal. -/
theorem principalOrderIdeal_zsmul {u : E} {n : ℤ} {x : E} (hx : x ∈ principalOrderIdeal u) :
    n • x ∈ principalOrderIdeal u := by
  rw [← Int.cast_smul_eq_zsmul ℝ]
  exact principalOrderIdeal_smul hx

omit [IsOrderedModule ℝ E] in
/-- A principal ideal is closed under binary suprema. -/
theorem principalOrderIdeal_sup {u x y : E} (hx : x ∈ principalOrderIdeal u)
    (hy : y ∈ principalOrderIdeal u) : x ⊔ y ∈ principalOrderIdeal u := by
  obtain ⟨c, hc, hxc⟩ := hx
  obtain ⟨d, hd, hyd⟩ := hy
  refine ⟨c + d, add_nonneg hc hd, ?_⟩
  calc |x ⊔ y| ≤ |x| ⊔ |y| := abs_sup_le_sup_abs x y
    _ ≤ |x| + |y| :=
        sup_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
    _ ≤ c • u + d • u := add_le_add hxc hyd
    _ = (c + d) • u := by rw [add_smul]

omit [IsOrderedModule ℝ E] in
/-- A principal ideal is closed under binary infima. -/
theorem principalOrderIdeal_inf {u x y : E} (hx : x ∈ principalOrderIdeal u)
    (hy : y ∈ principalOrderIdeal u) : x ⊓ y ∈ principalOrderIdeal u := by
  obtain ⟨c, hc, hxc⟩ := hx
  obtain ⟨d, hd, hyd⟩ := hy
  refine ⟨c + d, add_nonneg hc hd, ?_⟩
  calc |x ⊓ y| ≤ |x| ⊔ |y| := abs_inf_le_sup_abs x y
    _ ≤ |x| + |y| :=
        sup_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
    _ ≤ c • u + d • u := add_le_add hxc hyd
    _ = (c + d) • u := by rw [add_smul]

/-- The principal order ideal of `u`, as a real linear subspace. -/
@[expose]
def principalOrderIdealSubmodule (u : E) : Submodule ℝ E where
  carrier := principalOrderIdeal u
  add_mem' := principalOrderIdeal_add
  zero_mem' := ⟨0, le_rfl, by simp⟩
  smul_mem' _ _ hx := principalOrderIdeal_smul hx

/-- The carrier of `principalOrderIdealSubmodule u` is `principalOrderIdeal u`. -/
@[simp]
theorem coe_principalOrderIdealSubmodule (u : E) :
    (principalOrderIdealSubmodule u : Set E) = principalOrderIdeal u := rfl

/-- Membership in `principalOrderIdealSubmodule u`. -/
theorem mem_principalOrderIdealSubmodule {u x : E} :
    x ∈ principalOrderIdealSubmodule u ↔ x ∈ principalOrderIdeal u := Iff.rfl

/-- The order-unit gauge, used only on the principal ideal when `u` is nonnegative. -/
@[expose]
def orderUnitGauge (u x : E) : ℝ := sInf {c : ℝ | 0 ≤ c ∧ |x| ≤ c • u}

omit [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] in
/-- Defining equation of `orderUnitGauge`. -/
theorem orderUnitGauge_def (u x : E) :
    orderUnitGauge u x = sInf {c : ℝ | 0 ≤ c ∧ |x| ≤ c • u} := rfl

end PrincipalOrderIdeal

section OrderUnitGauge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E]
  [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]

private theorem archimedean_of_norm {x y : E} (h : ∀ n : ℕ, (n : ℝ) • x ≤ y) : x ≤ 0 := by
  have hpos : ∀ n : ℕ, (n : ℝ) • x⁺ ≤ y⁺ := by
    intro n
    rw [← posPart_smul_of_nonneg (Nat.cast_nonneg n)]
    exact sup_le_sup_right (h n) 0
  have hnorm : ∀ n : ℕ, (n : ℝ) * ‖x⁺‖ ≤ ‖y⁺‖ := by
    intro n
    have habs : |(n : ℝ) • x⁺| ≤ |y⁺| := by
      rw [abs_of_nonneg (smul_nonneg (Nat.cast_nonneg n) (posPart_nonneg x)),
        abs_of_nonneg (posPart_nonneg y)]
      exact hpos n
    have hle := norm_le_norm_of_abs_le_abs habs
    rwa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)] at hle
  have hz : ‖x⁺‖ = 0 := by
    by_contra hne
    have hpos' : 0 < ‖x⁺‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    obtain ⟨n, hn⟩ := exists_nat_gt (‖y⁺‖ / ‖x⁺‖)
    have hlt : ‖y⁺‖ < (n : ℝ) * ‖x⁺‖ := by
      rwa [div_lt_iff₀ hpos'] at hn
    exact not_lt.mpr (hnorm n) hlt
  rw [norm_eq_zero] at hz
  exact posPart_eq_zero.mp hz

private def gaugeSet (u x : E) : Set ℝ := {c : ℝ | 0 ≤ c ∧ |x| ≤ c • u}

omit [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- The gauge set of an ideal element is nonempty and bounded below by zero. -/
private theorem gaugeSet_nonempty {u x : E} (hx : x ∈ principalOrderIdeal u) :
    (gaugeSet u x).Nonempty := by
  obtain ⟨c, hc, hx⟩ := hx
  exact ⟨c, hc, hx⟩

omit [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- Every gauge scalar is nonnegative. -/
private theorem bddBelow_gaugeSet (u x : E) : BddBelow (gaugeSet u x) :=
  ⟨0, fun _ hc => hc.1⟩

omit [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- The order-unit gauge of an ideal element is nonnegative. -/
theorem orderUnitGauge_nonneg {u x : E} (hx : x ∈ principalOrderIdeal u) :
    0 ≤ orderUnitGauge u x := by
  unfold orderUnitGauge
  exact le_csInf (gaugeSet_nonempty hx) fun _ hc => hc.1

omit [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- An admissible scalar dominates the gauge. -/
theorem orderUnitGauge_le_of_mem {u x : E} {c : ℝ} (hc : 0 ≤ c ∧ |x| ≤ c • u) :
    orderUnitGauge u x ≤ c := by
  unfold orderUnitGauge
  exact csInf_le (bddBelow_gaugeSet u x) hc

/-- Archimedean attainment: the absolute value is bounded by the gauge multiple. -/
theorem abs_le_orderUnitGauge_smul {u x : E} (hu : 0 ≤ u) (hx : x ∈ principalOrderIdeal u) :
    |x| ≤ orderUnitGauge u x • u := by
  set p : ℝ := orderUnitGauge u x
  have hp : 0 ≤ p := orderUnitGauge_nonneg hx
  let z : E := (|x| - p • u)⁺
  have hz0 : 0 ≤ z := posPart_nonneg _
  have hzε : ∀ ε : ℝ, 0 < ε → z ≤ ε • u := by
    intro ε hε
    have hnot : ¬ ∀ c ∈ gaugeSet u x, p + ε ≤ c := by
      intro hall
      have hle : p + ε ≤ p := le_csInf (gaugeSet_nonempty hx) hall
      linarith
    push Not at hnot
    obtain ⟨c, hc, hclt⟩ := hnot
    have habs : |x| ≤ c • u := hc.2
    have hcε : c • u ≤ (p + ε) • u :=
      smul_le_smul_of_nonneg_right (le_of_lt hclt) hu
    have hdiff : |x| - p • u ≤ ε • u := by
      have hsum : c • u ≤ p • u + ε • u := by
        rw [← add_smul]
        exact hcε
      exact (sub_le_sub_right (habs.trans hsum) (p • u)).trans_eq (by abel)
    have hpos : (|x| - p • u)⁺ ≤ ε • u := by
      exact sup_le hdiff (smul_nonneg hε.le hu)
    simpa [z] using hpos
  have harch : ∀ n : ℕ, (n : ℝ) • z ≤ u := by
    intro n
    cases n with
    | zero => simp [hu]
    | succ n =>
      have hε : (0 : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) :=
        one_div_pos.mpr (by exact_mod_cast Nat.succ_pos n)
      have hz := hzε _ hε
      have hmul := smul_le_smul_of_nonneg_left hz
        (Nat.cast_nonneg (α := ℝ) (n + 1))
      have hcoe : ((n + 1 : ℕ) : ℝ) * (1 / ((n + 1 : ℕ) : ℝ)) = 1 := by
        rw [mul_one_div]
        exact div_self (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
      rw [smul_smul, hcoe, one_smul] at hmul
      exact hmul
  have hzle : z ≤ 0 := archimedean_of_norm harch
  have hz : z = 0 := le_antisymm hzle hz0
  exact sub_nonpos.mp (posPart_eq_zero.mp (by simpa [z] using hz))

/-- Membership in the gauge set is equivalent to dominating the gauge, for ideal elements. -/
theorem orderUnitGauge_le_iff {u x : E} (hu : 0 ≤ u) (hx : x ∈ principalOrderIdeal u) {c : ℝ}
    (hc : 0 ≤ c) : orderUnitGauge u x ≤ c ↔ |x| ≤ c • u := by
  constructor
  · intro hle
    exact (abs_le_orderUnitGauge_smul hu hx).trans (smul_le_smul_of_nonneg_right hle hu)
  · intro habs
    exact orderUnitGauge_le_of_mem ⟨hc, habs⟩

/-- The gauge is absolutely homogeneous on the principal ideal. -/
theorem orderUnitGauge_smul {u x : E} (hu : 0 ≤ u) (hx : x ∈ principalOrderIdeal u) (c : ℝ) :
    orderUnitGauge u (c • x) = |c| * orderUnitGauge u x := by
  have hx' : c • x ∈ principalOrderIdeal u := principalOrderIdeal_smul hx
  have hp : 0 ≤ orderUnitGauge u x := orderUnitGauge_nonneg hx
  have hq : 0 ≤ orderUnitGauge u (c • x) := orderUnitGauge_nonneg hx'
  apply le_antisymm
  · have habs : |c • x| ≤ (|c| * orderUnitGauge u x) • u := by
      calc |c • x| = |c| • |x| := abs_smul_of_lattice c x
        _ ≤ |c| • (orderUnitGauge u x • u) :=
            smul_le_smul_of_nonneg_left (abs_le_orderUnitGauge_smul hu hx) (abs_nonneg c)
        _ = (|c| * orderUnitGauge u x) • u := by rw [mul_smul]
    exact (orderUnitGauge_le_iff hu hx' (mul_nonneg (abs_nonneg c) hp)).2 habs
  · rcases eq_or_ne c 0 with rfl | hc
    · simpa using hq
    · have habs : |x| ≤ (|c|⁻¹ * orderUnitGauge u (c • x)) • u := by
        have hback : x = c⁻¹ • c • x := by
          rw [← mul_smul, inv_mul_cancel₀ hc, one_smul]
        calc |x| = |c⁻¹ • c • x| := by rw [← hback]
          _ = |c|⁻¹ • |c • x| := by rw [abs_smul_of_lattice, abs_inv]
          _ ≤ |c|⁻¹ • (orderUnitGauge u (c • x) • u) :=
              smul_le_smul_of_nonneg_left (abs_le_orderUnitGauge_smul hu hx')
                (inv_nonneg.mpr (abs_nonneg c))
          _ = (|c|⁻¹ * orderUnitGauge u (c • x)) • u := by rw [mul_smul]
      have hp' : orderUnitGauge u x ≤ |c|⁻¹ * orderUnitGauge u (c • x) :=
        (orderUnitGauge_le_iff hu hx (mul_nonneg (inv_nonneg.mpr (abs_nonneg c)) hq)).2 habs
      have hmul := mul_le_mul_of_nonneg_left hp' (abs_nonneg c)
      rwa [← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hc), one_mul] at hmul

/-- The gauge is subadditive on the principal ideal. -/
theorem orderUnitGauge_add_le {u x y : E} (hu : 0 ≤ u) (hx : x ∈ principalOrderIdeal u)
    (hy : y ∈ principalOrderIdeal u) :
    orderUnitGauge u (x + y) ≤ orderUnitGauge u x + orderUnitGauge u y := by
  have hxy : x + y ∈ principalOrderIdeal u := principalOrderIdeal_add hx hy
  have habs : |x + y| ≤ (orderUnitGauge u x + orderUnitGauge u y) • u := by
    calc |x + y| ≤ |x| + |y| := abs_add_le x y
      _ ≤ orderUnitGauge u x • u + orderUnitGauge u y • u :=
          add_le_add (abs_le_orderUnitGauge_smul hu hx) (abs_le_orderUnitGauge_smul hu hy)
      _ = (orderUnitGauge u x + orderUnitGauge u y) • u := by rw [add_smul]
  exact (orderUnitGauge_le_iff hu hxy
    (add_nonneg (orderUnitGauge_nonneg hx) (orderUnitGauge_nonneg hy))).2 habs

end OrderUnitGauge

end CKMA
