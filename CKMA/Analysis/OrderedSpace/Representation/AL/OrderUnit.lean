/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.OrderedSpace.Bands
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Order-unit renorming of a principal ideal

`OrderUnitSpace u` is the principal ideal of a vector `u`, as a fresh type whose norm is the
order-unit gauge. For nonnegative `u` the gauge satisfies the normed-space axioms, the closed
unit ball is the order interval of `u`, and completeness of the ambient Banach lattice passes
to the ideal. The gauge inequalities are proved in `CKMA.Analysis.OrderedSpace.Bands` next to
`orderUnitGauge`. The weak-unit density and the L¹ representation stay in
`CKMA.Analysis.OrderedSpace.Representation.AL`.

## Main definitions

* `CKMA.OrderUnitSpace`: principal order ideal equipped with the order-unit gauge norm.
* `CKMA.OrderUnitSpace.unit`: the order unit as an element of its principal ideal.
* `CKMA.OrderUnitSpace.toVecₗ`: inclusion of the ideal into the ambient space.

## Main results

* `CKMA.OrderUnitSpace.core`: the gauge satisfies the normed-space axioms.
* `CKMA.OrderUnitSpace.ball_eq_Icc`: the closed gauge ball is the order interval of the unit.
-/

public section

noncomputable section

open Set Metric Filter Topology

namespace CKMA

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [Lattice E]
  [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E]

/-- The principal ideal of `u`, as a fresh type carrying the order-unit gauge norm. -/
@[ext]
structure OrderUnitSpace (u : E) where
  /-- Underlying vector of the ideal element. -/
  toVec : E
  /-- Witness that the vector lies in the principal ideal. -/
  mem_ideal : toVec ∈ principalOrderIdeal u

namespace OrderUnitSpace

variable {u : E}

omit [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- The underlying-vector map is injective. -/
theorem toVec_injective : Function.Injective (toVec : OrderUnitSpace u → E) :=
  fun _ _ h => OrderUnitSpace.ext h

@[expose]
instance : Zero (OrderUnitSpace u) where
  zero := ⟨0, ⟨0, le_rfl, by simp⟩⟩

@[expose]
instance : Add (OrderUnitSpace u) where
  add x y := ⟨x.toVec + y.toVec, principalOrderIdeal_add x.mem_ideal y.mem_ideal⟩

@[expose]
instance : Neg (OrderUnitSpace u) where
  neg x := ⟨-x.toVec, principalOrderIdeal_neg x.mem_ideal⟩

@[expose]
instance : Sub (OrderUnitSpace u) where
  sub x y := ⟨x.toVec - y.toVec, principalOrderIdeal_sub x.mem_ideal y.mem_ideal⟩

@[expose]
instance : SMul ℕ (OrderUnitSpace u) where
  smul n x := ⟨n • x.toVec, principalOrderIdeal_nsmul x.mem_ideal⟩

@[expose]
instance : SMul ℤ (OrderUnitSpace u) where
  smul n x := ⟨n • x.toVec, principalOrderIdeal_zsmul x.mem_ideal⟩

@[expose]
instance : SMul ℝ (OrderUnitSpace u) where
  smul c x := ⟨c • x.toVec, principalOrderIdeal_smul x.mem_ideal⟩

omit [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- The underlying vector of zero is zero. -/
@[simp] theorem toVec_zero : (0 : OrderUnitSpace u).toVec = 0 := rfl

omit [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- The underlying vector of a sum is the sum of the underlying vectors. -/
@[simp] theorem toVec_add (x y : OrderUnitSpace u) : (x + y).toVec = x.toVec + y.toVec := rfl

omit [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- The underlying vector of a negation is the negation of the underlying vector. -/
@[simp] theorem toVec_neg (x : OrderUnitSpace u) : (-x).toVec = -x.toVec := rfl

omit [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- The underlying vector of a difference is the difference of the underlying vectors. -/
@[simp] theorem toVec_sub (x y : OrderUnitSpace u) : (x - y).toVec = x.toVec - y.toVec := rfl

omit [HasSolidNorm E] in
/-- The underlying vector of a natural multiple is that multiple of the vector. -/
@[simp] theorem toVec_nsmul (n : ℕ) (x : OrderUnitSpace u) : (n • x).toVec = n • x.toVec := rfl

omit [HasSolidNorm E] in
/-- The underlying vector of an integer multiple is that multiple of the vector. -/
@[simp] theorem toVec_zsmul (n : ℤ) (x : OrderUnitSpace u) : (n • x).toVec = n • x.toVec := rfl

omit [HasSolidNorm E] in
/-- The underlying vector of a scalar multiple is that multiple of the vector. -/
@[simp] theorem toVec_smul (c : ℝ) (x : OrderUnitSpace u) : (c • x).toVec = c • x.toVec := rfl

@[expose]
instance : AddCommGroup (OrderUnitSpace u) :=
  Function.Injective.addCommGroup toVec toVec_injective rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- The underlying vector, as an additive monoid homomorphism. -/
@[expose]
def toVecAddMonoidHom : OrderUnitSpace u →+ E where
  toFun := toVec
  map_zero' := rfl
  map_add' := fun _ _ => rfl

@[expose]
instance : Module ℝ (OrderUnitSpace u) :=
  Function.Injective.module ℝ toVecAddMonoidHom toVec_injective fun _ _ => rfl

/-- Inclusion of the principal ideal into the ambient space. -/
@[expose]
def toVecₗ : OrderUnitSpace u →ₗ[ℝ] E where
  toFun := toVec
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

omit [HasSolidNorm E] in
/-- The linear inclusion agrees with the underlying vector. -/
@[simp] theorem toVecₗ_apply (x : OrderUnitSpace u) : toVecₗ x = x.toVec := rfl

@[expose]
instance : PartialOrder (OrderUnitSpace u) where
  le x y := x.toVec ≤ y.toVec
  le_refl := fun _ => le_rfl
  le_trans := fun _ _ _ => le_trans
  le_antisymm := fun _ _ hxy hyx => OrderUnitSpace.ext (le_antisymm hxy hyx)

@[expose]
instance : Lattice (OrderUnitSpace u) where
  sup x y := ⟨x.toVec ⊔ y.toVec, principalOrderIdeal_sup x.mem_ideal y.mem_ideal⟩
  le_sup_left := fun _ _ => le_sup_left
  le_sup_right := fun _ _ => le_sup_right
  sup_le := fun _ _ _ hxz hyz => sup_le hxz hyz
  inf x y := ⟨x.toVec ⊓ y.toVec, principalOrderIdeal_inf x.mem_ideal y.mem_ideal⟩
  inf_le_left := fun _ _ => inf_le_left
  inf_le_right := fun _ _ => inf_le_right
  le_inf := fun _ _ _ hxy hxz => le_inf hxy hxz

omit [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- The underlying vector of a supremum is the supremum of the underlying vectors. -/
@[simp] theorem toVec_sup (x y : OrderUnitSpace u) : (x ⊔ y).toVec = x.toVec ⊔ y.toVec := rfl

omit [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- The underlying vector of an infimum is the infimum of the underlying vectors. -/
@[simp] theorem toVec_inf (x y : OrderUnitSpace u) : (x ⊓ y).toVec = x.toVec ⊓ y.toVec := rfl

omit [HasSolidNorm E] in
/-- The underlying vector of an absolute value is the absolute value of the vector. -/
@[simp] theorem toVec_abs (x : OrderUnitSpace u) : |x|.toVec = |x.toVec| := by
  simp [abs]

@[expose]
instance : IsOrderedAddMonoid (OrderUnitSpace u) where
  add_le_add_left a b hab c := by
    change (a + c).toVec ≤ (b + c).toVec
    rw [toVec_add, toVec_add]
    exact add_le_add_left (show a.toVec ≤ b.toVec from hab) c.toVec

@[expose]
instance : IsOrderedModule ℝ (OrderUnitSpace u) where
  smul_le_smul_of_nonneg_left a ha b₁ b₂ hb := by
    change (a • b₁).toVec ≤ (a • b₂).toVec
    rw [toVec_smul, toVec_smul]
    exact smul_le_smul_of_nonneg_left (show b₁.toVec ≤ b₂.toVec from hb) ha
  smul_le_smul_of_nonneg_right b hb a₁ a₂ ha := by
    change (a₁ • b).toVec ≤ (a₂ • b).toVec
    rw [toVec_smul, toVec_smul]
    exact smul_le_smul_of_nonneg_right (show a₁ ≤ a₂ from ha)
      (show (0 : E) ≤ b.toVec from hb)

variable [Fact (0 ≤ u)]

/-- The order unit, as an element of its principal ideal. -/
@[expose]
def unit : OrderUnitSpace u :=
  ⟨u, ⟨1, zero_le_one, by rw [abs_of_nonneg (Fact.out : 0 ≤ u), one_smul]⟩⟩

omit [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- The underlying vector of the order unit is the unit vector `u`. -/
@[simp] theorem toVec_unit : (unit : OrderUnitSpace u).toVec = u := rfl

@[expose]
instance : Norm (OrderUnitSpace u) where
  norm x := orderUnitGauge u x.toVec

/-- The gauge satisfies the normed-space axioms on the principal ideal. -/
theorem core : NormedSpace.Core ℝ (OrderUnitSpace u) where
  norm_nonneg x := gauge_nonneg x.mem_ideal
  norm_smul c x := by
    simpa [norm, Real.norm_eq_abs] using gauge_smul (Fact.out : 0 ≤ u) x.mem_ideal c
  norm_triangle x y := gauge_add (Fact.out : 0 ≤ u) x.mem_ideal y.mem_ideal
  norm_eq_zero_iff x := by
    constructor
    · intro h
      have hgauge := abs_le_gauge_smul (Fact.out : 0 ≤ u) x.mem_ideal
      rw [show orderUnitGauge u x.toVec = ‖x‖ by rfl, h, zero_smul] at hgauge
      have hz : |x.toVec| = 0 := le_antisymm hgauge (abs_nonneg _)
      have hle : x.toVec ≤ 0 := by
        rw [← hz, abs]
        exact le_sup_left
      have hge : 0 ≤ x.toVec := by
        have hneg : -x.toVec ≤ 0 := by
          rw [← hz, abs]
          exact le_sup_right
        exact neg_nonpos.mp hneg
      exact OrderUnitSpace.ext (le_antisymm hle hge)
    · rintro rfl
      apply le_antisymm
      · exact gauge_le_of_mem ⟨le_rfl, by simp⟩
      · exact gauge_nonneg ⟨0, le_rfl, by simp⟩

@[expose]
instance : NormedAddCommGroup (OrderUnitSpace u) := NormedAddCommGroup.ofCore core

@[expose]
instance : NormedSpace ℝ (OrderUnitSpace u) := NormedSpace.ofCore core

@[expose]
instance : HasSolidNorm (OrderUnitSpace u) where
  solid x y hxy := by
    have hxy' : |x.toVec| ≤ |y.toVec| := by
      change |x|.toVec ≤ |y|.toVec at hxy
      simpa [toVec_abs] using hxy
    exact (gauge_le_iff (Fact.out : 0 ≤ u) x.mem_ideal (gauge_nonneg y.mem_ideal)).2
      (hxy'.trans (abs_le_gauge_smul (Fact.out : 0 ≤ u) y.mem_ideal))

/-- The gauge metric on a principal ideal of a Banach lattice is complete. -/
@[expose]
instance [CompleteSpace E] : CompleteSpace (OrderUnitSpace u) := by
  refine complete_of_cauchySeq_tendsto fun s hs => ?_
  have hu : 0 ≤ u := Fact.out
  have hmul : ∀ z : OrderUnitSpace u, ‖z.toVec‖ ≤ ‖z‖ * ‖u‖ := by
    intro z
    have hle : ‖z.toVec‖ ≤ ‖‖z‖ • u‖ := by
      apply norm_le_norm_of_abs_le_abs
      rw [abs_of_nonneg (smul_nonneg (norm_nonneg _) hu)]
      simpa [norm] using abs_le_gauge_smul hu z.mem_ideal
    rwa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hle
  have hE : CauchySeq fun n => (s n).toVec := by
    rw [Metric.cauchySeq_iff] at hs ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hs (ε / (‖u‖ + 1)) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hdist : dist (s m) (s n) < ε / (‖u‖ + 1) := hN m hm n hn
    have hle : dist (s m).toVec (s n).toVec ≤ dist (s m) (s n) * ‖u‖ := by
      rw [dist_eq_norm, dist_eq_norm]
      exact hmul (s m - s n)
    have hcmp : (ε / (‖u‖ + 1)) * ‖u‖ ≤ ε := by
      calc (ε / (‖u‖ + 1)) * ‖u‖ ≤ (ε / (‖u‖ + 1)) * (‖u‖ + 1) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (by positivity)
        _ = ε := by rw [div_mul_cancel₀ _ (by positivity)]
    by_cases hu0 : ‖u‖ = 0
    · have hzero : dist (s m).toVec (s n).toVec ≤ 0 := by simpa [hu0] using hle
      exact (le_antisymm hzero (dist_nonneg)).trans_lt hε
    · exact (hle.trans_lt (mul_lt_mul_of_pos_right hdist
        (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu0)))).trans_le hcmp
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hE
  rw [Metric.cauchySeq_iff] at hs
  have hclose : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m, N ≤ m → |(s m).toVec - y| ≤ ε • u := by
    intro ε hε
    obtain ⟨N, hN⟩ := hs ε hε
    refine ⟨N, fun m hm => ?_⟩
    have htail : ∀ n, N ≤ n → (s n).toVec ∈ Icc ((s m).toVec - ε • u) ((s m).toVec + ε • u) := by
      intro n hn
      have hdist : dist (s m) (s n) < ε := hN m hm n hn
      have hgauge : ‖s m - s n‖ < ε := by rwa [dist_eq_norm] at hdist
      have habs : |(s m).toVec - (s n).toVec| ≤ ‖s m - s n‖ • u :=
        abs_le_gauge_smul hu (s m - s n).mem_ideal
      have hle : |(s m).toVec - (s n).toVec| ≤ ε • u :=
        habs.trans (smul_le_smul_of_nonneg_right (le_of_lt hgauge) hu)
      rw [abs_le'] at hle
      constructor
      · rw [sub_le_iff_le_add]
        exact (sub_le_iff_le_add').mp hle.1
      · simp only [neg_sub] at hle
        exact (sub_le_iff_le_add').mp hle.2
    have hyI := isClosed_Icc.mem_of_tendsto hy
      (eventually_atTop.2 ⟨N, fun n hn => htail n hn⟩)
    rw [mem_Icc] at hyI
    rw [abs_le']
    constructor
    · rw [sub_le_iff_le_add']
      exact (sub_le_iff_le_add).mp hyI.1
    · simp only [neg_sub]
      rw [sub_le_iff_le_add']
      exact hyI.2
  have hyideal : y ∈ principalOrderIdeal u := by
    obtain ⟨N, hN⟩ := hclose 1 zero_lt_one
    have hdiff : (s N).toVec - y ∈ principalOrderIdeal u :=
      ⟨1, zero_le_one, by simpa [one_smul] using hN N le_rfl⟩
    have hyeq : y = (s N).toVec - ((s N).toVec - y) := by abel
    rw [hyeq]
    exact principalOrderIdeal_sub (s N).mem_ideal hdiff
  refine ⟨⟨y, hyideal⟩, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hclose (ε / 2) (half_pos hε)
  refine ⟨N, fun m hm => ?_⟩
  rw [dist_eq_norm]
  have hgauge : orderUnitGauge u ((s m).toVec - y) ≤ ε / 2 :=
    (gauge_le_iff hu (principalOrderIdeal_sub (s m).mem_ideal hyideal) (half_pos hε).le).2
      (hN m hm)
  change orderUnitGauge u ((s m - ⟨y, hyideal⟩).toVec) < ε
  exact hgauge.trans_lt (half_lt_self hε)

/-- The closed gauge ball is the order interval of the unit. -/
theorem ball_eq_Icc : closedBall (0 : OrderUnitSpace u) 1 = Icc (-unit) unit := by
  ext x
  rw [mem_closedBall_iff_norm, sub_zero]
  change orderUnitGauge u x.toVec ≤ 1 ↔ -unit ≤ x ∧ x ≤ unit
  rw [gauge_le_iff (Fact.out : 0 ≤ u) x.mem_ideal zero_le_one, one_smul, abs_le']
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · change (-unit).toVec ≤ x.toVec
      rw [toVec_neg, toVec_unit]
      exact (neg_le_neg h.2).trans_eq (by simp)
    · change x.toVec ≤ unit.toVec
      rw [toVec_unit]
      exact h.1
  · intro h
    refine ⟨?_, ?_⟩
    · have hx : x.toVec ≤ unit.toVec := h.2
      rwa [toVec_unit] at hx
    · change -x.toVec ≤ u
      have hx : (-unit).toVec ≤ x.toVec := h.1
      rw [toVec_neg, toVec_unit] at hx
      exact (neg_le_neg hx).trans_eq (by simp)

omit [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- The order unit is positive. -/
theorem unit_nonneg : 0 ≤ (unit : OrderUnitSpace u) := by
  change (0 : OrderUnitSpace u).toVec ≤ unit.toVec
  rw [toVec_zero, toVec_unit]
  exact Fact.out

end OrderUnitSpace

end CKMA
