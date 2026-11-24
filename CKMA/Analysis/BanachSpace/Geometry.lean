/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.FunctionalAnalysis.Basic
public import CKMA.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Normed.Module.RademacherSum.Basic

import TauCeti.Analysis.Matrix.Grothendieck
import TauCeti.Analysis.Normed.Module.RademacherSum.TypeCotype

/-!
# Weak sequence structure and local Hilbert geometry

Rosenthal's theorem is expressed using weakly Cauchy subsequences and two-sided finite
coefficient estimates for the l1 basis. Type and cotype use the L2 energy of finite Rademacher
sums, with one constant uniform over all finite families. Hilbertizability concerns an equivalent
Hilbert norm, rather than the parallelogram identity for the original norm.

Dvoretzky's theorem uses scaled embeddings, and the real Grothendieck bound has a universal
constant independent of every finite dimension. Dimension-zero cases are included.
Sources: GAPS 17.21, 17.38, 17.39, and 17.57.
The real Grothendieck inequality uses TauCeti's matrix inequality with constant `8`.
The forward Kwapień implication uses TauCeti's type and cotype transport API.

## Main definitions

* `CKMA.IsEquivalentToEllOneBasis`: two-sided finite `ℓ¹` coefficient bounds for a sequence.
* `CKMA.rademacherEnergy`: second moment of a finite Rademacher sum.
* `CKMA.HasRademacherType`, `CKMA.HasRademacherCotype`: Rademacher type `p` and cotype `q`.
* `CKMA.IsHilbertizable`: existence of a continuous linear equivalence with a Hilbert space.
* `CKMA.grothendieckScalarBound`: scalar sign-choice supremum for a finite matrix.

## Main results

* `CKMA.rosenthal_ellOne`: Rosenthal's `ℓ¹` theorem.
* `CKMA.kwapien`: Kwapień's characterization of Hilbertizable Banach spaces.
* `CKMA.IsHilbertizable.hasRademacherType_two_and_cotype_two`: type and cotype of Hilbertizable
  normed spaces.
* `CKMA.dvoretzky`: Dvoretzky's theorem on almost-isometric Euclidean subspaces.
* `CKMA.grothendieck_real`: the real Grothendieck inequality.
-/

public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped BigOperators

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Equivalence to the standard l1 basis, expressed by two-sided finite coefficient estimates.
Completeness then extends the coefficient map to the closed linear span. -/
@[expose]
def IsEquivalentToEllOneBasis (x : ℕ → E) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n : ℕ) (a : Fin n → ℝ),
    c * (∑ i, |a i|) ≤ ‖∑ i, a i • x i.val‖ ∧
      ‖∑ i, a i • x i.val‖ ≤ C * ∑ i, |a i|

/-- **17.21**, Rosenthal's l1 theorem over real Banach spaces. -/
theorem rosenthal_ellOne [CompleteSpace E] (x : ℕ → E)
    (hx : Bornology.IsBounded (Set.range x)) :
    ∃ r : ℕ → ℕ, StrictMono r ∧
      (IsWeaklyCauchy ℝ (x ∘ r) ∨ IsEquivalentToEllOneBasis (x ∘ r)) := by
  sorry

/-- The second moment of a finite Rademacher sum, using the uniform finite sign space. -/
@[expose]
def rademacherEnergy {n : ℕ} (x : Fin n → E) : ℝ :=
  ((Fintype.card (Fin n → Bool) : ℝ)⁻¹) *
    ∑ ε : Fin n → Bool, ‖∑ i, (if ε i then (1 : ℝ) else -1) • x i‖ ^ 2

/-- Type p, with a single constant uniform in all finite families. -/
@[expose]
def HasRademacherType (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (p : ℝ) : Prop :=
  1 ≤ p ∧ p ≤ 2 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : Fin n → E),
    Real.sqrt (rademacherEnergy x) ≤ C * (∑ i, ‖x i‖ ^ p) ^ (1 / p)

/-- Cotype q, with a single constant uniform in all finite families. -/
@[expose]
def HasRademacherCotype (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (q : ℝ) : Prop :=
  2 ≤ q ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : Fin n → E),
    (∑ i, ‖x i‖ ^ q) ^ (1 / q) ≤ C * Real.sqrt (rademacherEnergy x)

/-- A concrete Hilbert-space isomorphism criterion for the original Banach norm. -/
@[expose]
def IsHilbertizable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∃ H : RealHilbertSpace.{u}, Nonempty (E ≃L[ℝ] H.carrier)

/-- The Boolean sign average agrees with TauCeti's signed average over integer units. -/
theorem sqrt_rademacherEnergy_eq_rademacherSecondMoment {n : ℕ} (x : Fin n → E) :
    Real.sqrt (rademacherEnergy x) = TauCeti.rademacherSecondMoment x := by
  let e : Bool ≃ ℤˣ :=
    { toFun := fun b ↦ if b then 1 else -1
      invFun := fun s ↦ decide (s = 1)
      left_inv := by intro b; cases b <;> decide
      right_inv := by intro s; rcases Int.units_eq_one_or s with rfl | rfl <;> decide }
  rw [TauCeti.rademacherSecondMoment_def, rademacherEnergy]
  congr 1
  let f : (Fin n → Bool) → ℝ := fun ε ↦ ‖∑ i, (if ε i then (1 : ℝ) else -1) • x i‖ ^ 2
  let g : (Fin n → ℤˣ) → ℝ := fun ε ↦ ‖∑ i, ε i • x i‖ ^ 2
  suffices he : (𝔼 ε, f ε) = (𝔼 ε, g ε) by
    simpa only [Fintype.expect_eq_sum_div_card, div_eq_inv_mul, f, g] using he
  refine Fintype.expect_equiv (Equiv.piCongrRight fun _ : Fin n ↦ e) f g fun ε ↦ ?_
  dsimp only [f, g]
  congr 2
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Equiv.piCongrRight_apply, e, Equiv.coe_fn_mk]
  cases hε : ε i <;> simp [hε, Units.smul_def]

open scoped ENNReal NNReal in
/-- A Hilbertizable normed space has Rademacher type and cotype `2`. -/
theorem IsHilbertizable.hasRademacherType_two_and_cotype_two (h : IsHilbertizable E) :
    HasRademacherType E 2 ∧ HasRademacherCotype E 2 := by
  obtain ⟨H, ⟨U⟩⟩ := h
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  -- Type and cotype transport from the Hilbert norm via TauCeti's equivalence lemmas.
  have htype := (TauCeti.hasType_two_of_innerProductSpace ℝ H.carrier).of_continuousLinearEquiv U
  have hcotype :=
    (TauCeti.hasCotype_two_of_innerProductSpace ℝ H.carrier).of_continuousLinearEquiv U
  let C : ℝ≥0 := ‖(U.symm : H.carrier →L[ℝ] E)‖₊ * 1 * ‖(U : E →L[ℝ] H.carrier)‖₊
  have hnorm {n : ℕ} (x : Fin n → E) :
      ‖WithLp.toLp 2 x‖ = (∑ i, ‖x i‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    rw [PiLp.norm_eq_of_L2, Real.sqrt_eq_rpow]
    simp only [Real.rpow_two]
  refine ⟨⟨by norm_num, le_rfl, C, C.2, ?_⟩, ⟨le_rfl, C, C.2, ?_⟩⟩
  · intro n x
    rw [sqrt_rademacherEnergy_eq_rademacherSecondMoment, ← hnorm]
    exact (TauCeti.hasType_iff.mp htype) n x
  · intro n x
    rw [sqrt_rademacherEnergy_eq_rademacherSecondMoment, ← hnorm]
    exact (TauCeti.hasCotype_iff.mp hcotype) n x

/-- **17.38**, Kwapień: type two and cotype two characterize Hilbert-isomorphic Banach spaces. -/
theorem kwapien [CompleteSpace E] :
    IsHilbertizable E ↔ HasRademacherType E 2 ∧ HasRademacherCotype E 2 := by
  refine ⟨IsHilbertizable.hasRademacherType_two_and_cotype_two, ?_⟩
  sorry

/-- **17.39**, Dvoretzky in a scaled embedding form equivalent to Banach–Mazur distortion
at most `1+ε`. The lower bound `‖x‖ ≤ ‖T x‖` makes `T` injective. This also makes the
dimension-zero case unambiguous. -/
theorem dvoretzky [CompleteSpace E] (hE : ¬ FiniteDimensional ℝ E) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : EuclideanSpace ℝ (Fin n) →L[ℝ] E,
      ∀ x, ‖x‖ ≤ ‖T x‖ ∧ ‖T x‖ ≤ (1 + ε) * ‖x‖ := by
  sorry

/-- The scalar sign optimum in the real Grothendieck inequality. The set is nonempty even
if one index type is empty. -/
@[expose]
def grothendieckScalarBound {α β : Type*} [Fintype α] [Fintype β] (a : α → β → ℝ) : ℝ :=
  sSup {b | ∃ s : α → ℝ, ∃ t : β → ℝ,
    (∀ i, |s i| ≤ 1) ∧ (∀ j, |t j| ≤ 1) ∧ b = |∑ i, ∑ j, a i j * s i * t j|}

/-- **17.57**, the real Grothendieck inequality, with a universal constant independent of
both index types and the real inner product space. -/
theorem grothendieck_real : ∃ K : ℝ, 0 < K ∧ ∀ {α β H : Type*} [Fintype α] [Fintype β]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a : α → β → ℝ) (v : α → H) (w : β → H),
    (∀ i, ‖v i‖ ≤ 1) → (∀ j, ‖w j‖ ≤ 1) →
      |∑ i, ∑ j, a i j * inner ℝ (v i) (w j)| ≤ K * grothendieckScalarBound a := by
  refine ⟨8, by norm_num, ?_⟩
  intro α β H _ _ _ _ a v w hv hw
  -- TauCeti's inequality applies once the scalar sign-choice supremum is bounded above.
  refine Matrix.abs_sum_sum_mul_inner_le_eight_mul a (fun s t hs ht ↦ ?_) hv hw
  unfold grothendieckScalarBound
  refine le_csSup ?_ ⟨s, t, hs, ht, rfl⟩
  refine ⟨∑ i, ∑ j, |a i j|, ?_⟩
  rintro b ⟨u, z, hu, hz, rfl⟩
  calc
    |∑ i, ∑ j, a i j * u i * z j| ≤ ∑ i, |∑ j, a i j * u i * z j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |a i j * u i * z j| :=
      Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |a i j| := by
      refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
      rw [abs_mul, abs_mul]
      calc
        |a i j| * |u i| * |z j| ≤ |a i j| * |u i| * 1 :=
          mul_le_mul_of_nonneg_left (hz j) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = |a i j| * |u i| := mul_one _
        _ ≤ |a i j| * 1 := mul_le_mul_of_nonneg_left (hu i) (abs_nonneg _)
        _ = |a i j| := mul_one _

end CKMA
