/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Tactic
public import CKMA.Analysis.OrderedSpace.Bands.Lattice
public import CKMA.Analysis.OrderedSpace.Bands.Freudenthal

/-!
# Riesz ideals, band projections, and order approximation

A Riesz ideal is a real linear subspace solid under domination by lattice absolute values.
Bands are closed under existing positive suprema. Dedekind completeness is stated on the
chosen vector-lattice order, and the Archimedean predicate is the vector-lattice axiom rather
than positive-element domination in a linear order.

Band projections, Freudenthal component approximation, and Riesz–Kantorovich suprema are
formulated through their order characterizations. Positive maps reuse Mathlib's monotonicity
criterion; regular maps are differences of positive maps. Sources: GAPS 19.5, 19.8, and 19.20.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped BigOperators

variable {E F : Type*} [AddCommGroup E] [Lattice E] [Module ℝ E]
    [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
    [AddCommGroup F] [Lattice F] [Module ℝ F]
    [IsOrderedAddMonoid F] [IsOrderedModule ℝ F]

/-- A Riesz ideal is a linear subspace solid under domination of lattice absolute values. -/
structure RieszIdeal (E : Type*) [AddCommGroup E] [Lattice E] [Module ℝ E] where
  /-- Underlying real linear subspace. -/
  toSubmodule : Submodule ℝ E
  /-- Solidity. -/
  solid : ∀ ⦃x y : E⦄, |x| ≤ |y| → y ∈ toSubmodule → x ∈ toSubmodule

/-- A band is an ideal closed under existing suprema of nonempty positive subsets. -/
def RieszIdeal.IsBand (B : RieszIdeal E) : Prop :=
  ∀ s : Set E, s.Nonempty → (∀ x ∈ s, 0 ≤ x ∧ x ∈ B.toSubmodule) →
    ∀ x : E, IsLUB s x → x ∈ B.toSubmodule

section PositiveMaps

variable {E₁ E₂ : Type*} [AddCommGroup E₁] [PartialOrder E₁] [Module ℝ E₁]
    [IsOrderedAddMonoid E₁] [AddCommGroup E₂] [PartialOrder E₂] [Module ℝ E₂]
    [IsOrderedAddMonoid E₂]

/-- Positivity of an algebraic linear operator on ordered real vector spaces. -/
def IsPositiveLinearMap (T : E₁ →ₗ[ℝ] E₂) : Prop := ∀ x, 0 ≤ x → 0 ≤ T x

omit [IsOrderedAddMonoid E₁] in
/-- The identity is positive. -/
theorem isPositiveLinearMap_id : IsPositiveLinearMap (LinearMap.id : E₁ →ₗ[ℝ] E₁) :=
  fun _ hx ↦ hx

omit [IsOrderedAddMonoid E₁] [IsOrderedAddMonoid E₂] in
/-- Composition preserves positivity. -/
theorem IsPositiveLinearMap.comp {G : Type*} [AddCommGroup G] [PartialOrder G] [Module ℝ G]
    {S : E₂ →ₗ[ℝ] G} {T : E₁ →ₗ[ℝ] E₂} (hS : IsPositiveLinearMap S)
    (hT : IsPositiveLinearMap T) : IsPositiveLinearMap (S.comp T) :=
  fun x hx ↦ hS _ (hT x hx)

/-- A positive linear map is monotone. -/
theorem IsPositiveLinearMap.monotone {T : E₁ →ₗ[ℝ] E₂} (hT : IsPositiveLinearMap T) :
    Monotone T := (monotone_iff_map_nonneg T).2 hT

/-- Positivity of a linear map is exactly monotonicity of its underlying function. -/
theorem isPositiveLinearMap_iff_monotone (T : E₁ →ₗ[ℝ] E₂) :
    IsPositiveLinearMap T ↔ Monotone T := (monotone_iff_map_nonneg T).symm

/-- The difference-of-positive-maps definition of a regular operator. -/
def IsRegularLinearMap (T : E₁ →ₗ[ℝ] E₂) : Prop :=
  ∃ S U : E₁ →ₗ[ℝ] E₂, IsPositiveLinearMap S ∧ IsPositiveLinearMap U ∧ T = S - U

/-- Order boundedness is tested on every closed order interval. -/
def IsOrderBoundedLinearMap (T : E₁ →ₗ[ℝ] E₂) : Prop :=
  ∀ a b : E₁, ∃ c d : E₂, ∀ x : E₁, a ≤ x → x ≤ b → c ≤ T x ∧ T x ≤ d

/-- Every positive operator maps an order interval into the interval of its endpoint images. -/
theorem IsPositiveLinearMap.isOrderBounded {T : E₁ →ₗ[ℝ] E₂} (hT : IsPositiveLinearMap T) :
    IsOrderBoundedLinearMap T := by
  intro a b
  exact ⟨T a, T b, fun _ ha hb ↦ ⟨hT.monotone ha, hT.monotone hb⟩⟩

/-- Every regular operator is order bounded, without a Dedekind-completeness hypothesis. -/
theorem IsRegularLinearMap.isOrderBounded {T : E₁ →ₗ[ℝ] E₂} (hT : IsRegularLinearMap T) :
    IsOrderBoundedLinearMap T := by
  obtain ⟨S, U, hS, hU, rfl⟩ := hT
  intro a b
  refine ⟨S a - U b, S b - U a, ?_⟩
  intro x ha hb
  exact ⟨sub_le_sub (hS.monotone ha) (hU.monotone hb),
    sub_le_sub (hS.monotone hb) (hU.monotone ha)⟩

end PositiveMaps

/-- Dedekind completeness stated on the already chosen Riesz order. -/
def IsDedekindCompleteRieszSpace (E : Type*) [Lattice E] : Prop :=
  ∀ s : Set E, s.Nonempty → BddAbove s → ∃ x : E, IsLUB s x

/-- **19.5**: every band in a Dedekind-complete vector lattice admits its band projection.
The positive-vector supremum characterization and the disjoint-complement kernel are included. -/
theorem exists_bandProjection (hcomplete : IsDedekindCompleteRieszSpace E)
    (B : RieszIdeal E) (hB : B.IsBand) : ∃ P : E →ₗ[ℝ] E,
      LinearMap.range P = B.toSubmodule ∧
      (∀ x, P (P x) = P x) ∧
      (∀ x, P x = 0 ↔ x ∈ latticeDisjointComplement (B.toSubmodule : Set E)) ∧
      ∀ x : E, 0 ≤ x → 0 ≤ P x ∧ P x ≤ x ∧
        IsLUB {y | y ∈ B.toSubmodule ∧ 0 ≤ y ∧ y ≤ x} (P x) := by
  let slice : E → Set E := fun x =>
    {y | y ∈ B.toSubmodule ∧ 0 ≤ y ∧ y ≤ x}
  have hnonempty : ∀ x : E, 0 ≤ x → (slice x).Nonempty := by
    intro x hx
    exact ⟨0, B.toSubmodule.zero_mem, le_rfl, hx⟩
  have hbdd : ∀ x : E, BddAbove (slice x) := by
    intro x
    exact ⟨x, fun _y hy => hy.2.2⟩
  have hexists : ∀ x : E, ∃ z : E, IsLUB (slice x⁺) z := by
    intro x
    exact hcomplete (slice x⁺) (hnonempty x⁺ (posPart_nonneg x)) (hbdd x⁺)
  let component : E → E := fun x => Classical.choose (hexists x)
  have hspec : ∀ x : E, IsLUB (slice x⁺) (component x) :=
    fun x => Classical.choose_spec (hexists x)
  have hspec_pos : ∀ {x : E}, 0 ≤ x → IsLUB (slice x) (component x) := by
    intro x hx
    have h := hspec x
    rw [posPart_eq_self.2 hx] at h
    exact h
  have hmem : ∀ {x : E}, 0 ≤ x → component x ∈ slice x := by
    intro x hx
    have hL := hspec_pos hx
    have h0 : 0 ≤ component x := hL.1 ⟨B.toSubmodule.zero_mem, le_rfl, hx⟩
    have hxle : component x ≤ x := hL.2 (fun _y hy => hy.2.2)
    have hBin : component x ∈ B.toSubmodule :=
      hB (slice x) ⟨0, B.toSubmodule.zero_mem, le_rfl, hx⟩
        (fun _y hy => ⟨hy.2.1, hy.1⟩) (component x) hL
    exact ⟨hBin, h0, hxle⟩
  have hadd : ∀ x y : E, 0 ≤ x → 0 ≤ y →
      component (x + y) = component x + component y := by
    intro x y hx hy
    have hxy : 0 ≤ x + y := add_nonneg hx hy
    have hxmem := hmem hx
    have hymem := hmem hy
    have hxymem := hmem hxy
    have hsum_le : component x + component y ≤ component (x + y) := by
      have hin : component x + component y ∈ slice (x + y) :=
        ⟨B.toSubmodule.add_mem hxmem.1 hymem.1,
          add_nonneg hxmem.2.1 hymem.2.1, add_le_add hxmem.2.2 hymem.2.2⟩
      exact (hspec_pos hxy).1 hin
    have hle_sum : component (x + y) ≤ component x + component y := by
      obtain ⟨w1, w2, hw, hw10, hw1x, hw20, hw2y⟩ :=
        exists_add_eq_of_le_add hxymem.2.1 hx hy hxymem.2.2
      have hw1_le : w1 ≤ component (x + y) := by
        have hw1eq : w1 = component (x + y) - w2 := by
          calc
            w1 = w1 + w2 - w2 := by abel
            _ = component (x + y) - w2 := by rw [← hw]
        rw [hw1eq]
        exact sub_le_self _ hw20
      have hw1B : w1 ∈ B.toSubmodule :=
        B.solid (by rw [abs_of_nonneg hw10, abs_of_nonneg hxymem.2.1]; exact hw1_le)
          hxymem.1
      have hw2_le : w2 ≤ component (x + y) := by
        have hw2eq : w2 = component (x + y) - w1 := by
          calc
            w2 = w1 + w2 - w1 := by abel
            _ = component (x + y) - w1 := by rw [← hw]
        rw [hw2eq]
        exact sub_le_self _ hw10
      have hw2B : w2 ∈ B.toSubmodule :=
        B.solid (by rw [abs_of_nonneg hw20, abs_of_nonneg hxymem.2.1]; exact hw2_le)
          hxymem.1
      calc
        component (x + y) = w1 + w2 := hw
        _ ≤ component x + component y :=
          add_le_add ((hspec_pos hx).1 ⟨hw1B, hw10, hw1x⟩)
            ((hspec_pos hy).1 ⟨hw2B, hw20, hw2y⟩)
    exact le_antisymm hle_sum hsum_le
  have hzero : component 0 = 0 := by
    have hL : IsLUB (slice (0 : E)) 0 := by
      refine ⟨fun _y hy => hy.2.2, ?_⟩
      intro b hb
      exact hb ⟨B.toSubmodule.zero_mem, le_rfl, le_rfl⟩
    exact IsLUB.unique (hspec_pos le_rfl) hL
  have hsmul : ∀ (c : ℝ) (x : E), 0 ≤ c → 0 ≤ x →
      component (c • x) = c • component x := by
    intro c x hc hx
    rcases eq_or_lt_of_le hc with hc0 | hcpos
    · rw [← hc0, zero_smul, zero_smul, hzero]
    · have hset : slice (c • x) = (fun y => c • y) '' slice x := by
        ext z
        constructor
        · intro hz
          have hinv : 0 ≤ c⁻¹ := inv_nonneg.2 hcpos.le
          refine ⟨c⁻¹ • z, ?_, ?_⟩
          · exact ⟨B.toSubmodule.smul_mem c⁻¹ hz.1,
              smul_nonneg hinv hz.2.1,
              calc
                c⁻¹ • z ≤ c⁻¹ • (c • x) := smul_le_smul_of_nonneg_left hz.2.2 hinv
                _ = x := by rw [← mul_smul, inv_mul_cancel₀ hcpos.ne', one_smul]⟩
          · change c • (c⁻¹ • z) = z
            rw [← mul_smul, mul_inv_cancel₀ hcpos.ne', one_smul]
        · rintro ⟨y, hy, rfl⟩
          exact ⟨B.toSubmodule.smul_mem c hy.1, smul_nonneg hcpos.le hy.2.1,
            smul_le_smul_of_nonneg_left hy.2.2 hcpos.le⟩
      have hlub := isLUB_smul_of_pos hcpos (hspec_pos hx)
      rw [← hset] at hlub
      exact IsLUB.unique (hspec_pos (smul_nonneg hcpos.le hx)) hlub
  let P := coneAdditiveLinearMap component hadd hsmul
  have hPpos : ∀ {x : E}, 0 ≤ x → P x = component x :=
    fun {_x} hx => coneAdditiveLinearMap_apply_of_nonneg component hadd hsmul hx
  have hidem_pos : ∀ {x : E}, 0 ≤ x → P (P x) = P x := by
    intro x hx
    have hc0 : 0 ≤ component x := (hmem hx).2.1
    rw [hPpos hx, hPpos hc0]
    have hfx : component x ∈ slice (component x) := ⟨(hmem hx).1, hc0, le_rfl⟩
    exact IsLUB.unique (hspec_pos hc0)
      ⟨fun _y hy => hy.2.2, fun _b hb => hb hfx⟩
  have hidem : ∀ x, P (P x) = P x := by
    intro x
    have hsplit : P x = P x⁺ - P x⁻ := by
      conv_lhs => rw [(posPart_sub_negPart x).symm]
      rw [map_sub]
    calc
      P (P x) = P (P x⁺ - P x⁻) := by rw [hsplit]
      _ = P (P x⁺) - P (P x⁻) := map_sub P (P x⁺) (P x⁻)
      _ = P x⁺ - P x⁻ := by
        rw [hidem_pos (posPart_nonneg x), hidem_pos (negPart_nonneg x)]
      _ = P x := hsplit.symm
  have hrange : LinearMap.range P = B.toSubmodule := by
    refine Submodule.ext fun z => ?_
    constructor
    · intro hz
      rcases LinearMap.mem_range.mp hz with ⟨y, rfl⟩
      have hpy : P y = P y⁺ - P y⁻ := by
        conv_lhs => rw [(posPart_sub_negPart y).symm]
        rw [map_sub]
      rw [hpy]
      exact B.toSubmodule.sub_mem
        (by rw [hPpos (posPart_nonneg y)]; exact (hmem (posPart_nonneg y)).1)
        (by rw [hPpos (negPart_nonneg y)]; exact (hmem (negPart_nonneg y)).1)
    · intro hz
      have hzp : z⁺ ∈ B.toSubmodule :=
        B.solid (by
          rw [abs_of_nonneg (posPart_nonneg z)]
          calc
            z⁺ ≤ z⁺ + z⁻ := le_add_of_nonneg_right (negPart_nonneg z)
            _ = |z| := posPart_add_negPart z) hz
      have hzn : z⁻ ∈ B.toSubmodule :=
        B.solid (by
          rw [abs_of_nonneg (negPart_nonneg z)]
          calc
            z⁻ ≤ z⁺ + z⁻ := le_add_of_nonneg_left (posPart_nonneg z)
            _ = |z| := posPart_add_negPart z) hz
      have hfixp : P z⁺ = z⁺ := by
        rw [hPpos (posPart_nonneg z)]
        have hin : z⁺ ∈ slice z⁺ := ⟨hzp, posPart_nonneg z, le_rfl⟩
        exact IsLUB.unique (hspec_pos (posPart_nonneg z))
          ⟨fun _y hy => hy.2.2, fun _b hb => hb hin⟩
      have hfixn : P z⁻ = z⁻ := by
        rw [hPpos (negPart_nonneg z)]
        have hin : z⁻ ∈ slice z⁻ := ⟨hzn, negPart_nonneg z, le_rfl⟩
        exact IsLUB.unique (hspec_pos (negPart_nonneg z))
          ⟨fun _y hy => hy.2.2, fun _b hb => hb hin⟩
      have hzP : P z = z := by
        calc
          P z = P (z⁺ - z⁻) := by
            conv_lhs => rw [(posPart_sub_negPart z).symm]
          _ = P z⁺ - P z⁻ := map_sub P z⁺ z⁻
          _ = z⁺ - z⁻ := by rw [hfixp, hfixn]
          _ = z := posPart_sub_negPart z
      exact LinearMap.mem_range.mpr ⟨z, hzP⟩
  have hker : ∀ x, P x = 0 ↔
      x ∈ latticeDisjointComplement (B.toSubmodule : Set E) := by
    intro x
    constructor
    · intro hPx y hy
      have hsplit : P x⁺ - P x⁻ = 0 := by
        rw [← map_sub, posPart_sub_negPart x, hPx]
      have heq : P x⁺ = P x⁻ := sub_eq_zero.mp hsplit
      have hpos_le : P x⁺ ≤ x⁺ := by
        rw [hPpos (posPart_nonneg x)]
        exact (hmem (posPart_nonneg x)).2.2
      have hneg_le : P x⁻ ≤ x⁻ := by
        rw [hPpos (negPart_nonneg x)]
        exact (hmem (negPart_nonneg x)).2.2
      have hpos0 : P x⁺ = 0 := by
        have hle_inf : P x⁺ ≤ x⁺ ⊓ x⁻ := le_inf hpos_le (by rw [heq]; exact hneg_le)
        rw [posPart_inf_negPart_eq_zero] at hle_inf
        exact le_antisymm hle_inf (by
          rw [hPpos (posPart_nonneg x)]
          exact (hmem (posPart_nonneg x)).2.1)
      have hneg0 : P x⁻ = 0 := by rw [← heq, hpos0]
      have habs_mem : |y| ∈ B.toSubmodule :=
        B.solid (le_of_eq (abs_of_nonneg (abs_nonneg y))) hy
      have hxpos0 : x⁺ ⊓ |y| = 0 := by
        set w := x⁺ ⊓ |y|
        have hw0 : 0 ≤ w := le_inf (posPart_nonneg x) (abs_nonneg y)
        have hwB : w ∈ B.toSubmodule :=
          B.solid (by rw [abs_of_nonneg hw0, abs_of_nonneg (abs_nonneg y)]; exact inf_le_right)
            habs_mem
        have hwle : w ≤ P x⁺ := by
          rw [hPpos (posPart_nonneg x)]
          exact (hspec_pos (posPart_nonneg x)).1 ⟨hwB, hw0, inf_le_left⟩
        rw [hpos0] at hwle
        exact le_antisymm hwle hw0
      have hxneg0 : x⁻ ⊓ |y| = 0 := by
        set w := x⁻ ⊓ |y|
        have hw0 : 0 ≤ w := le_inf (negPart_nonneg x) (abs_nonneg y)
        have hwB : w ∈ B.toSubmodule :=
          B.solid (by rw [abs_of_nonneg hw0, abs_of_nonneg (abs_nonneg y)]; exact inf_le_right)
            habs_mem
        have hwle : w ≤ P x⁻ := by
          rw [hPpos (negPart_nonneg x)]
          exact (hspec_pos (negPart_nonneg x)).1 ⟨hwB, hw0, inf_le_left⟩
        rw [hneg0] at hwle
        exact le_antisymm hwle hw0
      have h1 : |y| ⊓ x⁺ = 0 := by rw [inf_comm]; exact hxpos0
      have h2 : |y| ⊓ x⁻ = 0 := by rw [inf_comm]; exact hxneg0
      have hle : |y| ⊓ |x| ≤ 0 := by
        have hsum := inf_add_le_add_inf (abs_nonneg y) (posPart_nonneg x) (negPart_nonneg x)
        rw [posPart_add_negPart, h1, h2, add_zero] at hsum
        exact hsum
      rw [LatticeDisjoint]
      exact le_antisymm (by rw [inf_comm]; exact hle) (le_inf (abs_nonneg x) (abs_nonneg y))
    · intro hx
      have hpos : P x⁺ = 0 := by
        rw [hPpos (posPart_nonneg x)]
        have hmemx := hmem (posPart_nonneg x)
        have hdisj : |x| ⊓ component x⁺ = 0 := by
          have hL := hx (component x⁺) hmemx.1
          rwa [LatticeDisjoint, abs_of_nonneg hmemx.2.1] at hL
        have hle : component x⁺ ≤ |x| := by
          calc
            component x⁺ ≤ x⁺ := hmemx.2.2
            _ ≤ x⁺ + x⁻ := le_add_of_nonneg_right (negPart_nonneg x)
            _ = |x| := posPart_add_negPart x
        rw [← inf_eq_right.2 hle]
        exact hdisj
      have hneg : P x⁻ = 0 := by
        rw [hPpos (negPart_nonneg x)]
        have hmemx := hmem (negPart_nonneg x)
        have hdisj : |x| ⊓ component x⁻ = 0 := by
          have hL := hx (component x⁻) hmemx.1
          rwa [LatticeDisjoint, abs_of_nonneg hmemx.2.1] at hL
        have hle : component x⁻ ≤ |x| := by
          calc
            component x⁻ ≤ x⁻ := hmemx.2.2
            _ ≤ x⁺ + x⁻ := le_add_of_nonneg_left (posPart_nonneg x)
            _ = |x| := posPart_add_negPart x
        rw [← inf_eq_right.2 hle]
        exact hdisj
      conv_lhs => rw [(posPart_sub_negPart x).symm]
      rw [map_sub, hpos, hneg, sub_zero]
  refine ⟨P, hrange, hidem, hker, ?_⟩
  intro x hx
  refine ⟨?_, ?_, ?_⟩
  · rw [hPpos hx]
    exact (hmem hx).2.1
  · rw [hPpos hx]
    exact (hmem hx).2.2
  · rw [hPpos hx]
    exact hspec_pos hx

/-- The Archimedean axiom appropriate to a partially ordered vector lattice. -/
def IsArchimedeanRieszSpace (E : Type*) [AddCommGroup E] [Lattice E] [Module ℝ E] : Prop :=
  ∀ x y : E, (∀ n : ℕ, (n : ℝ) • x ≤ y) → x ≤ 0

/-- An element is a component of a nonnegative order unit when it is disjoint from its remainder. -/
def IsLatticeComponent (v u : E) : Prop := 0 ≤ v ∧ v ≤ u ∧ v ⊓ (u - v) = 0

/-- The principal projection property is recorded by positive contractive order projections
onto double disjoint complements, rather than by arbitrary assumed theorem predicates. -/
def HasPrincipalBandProjections (E : Type*) [AddCommGroup E] [Lattice E] [Module ℝ E] : Prop :=
  ∀ u : E, ∃ P : E →ₗ[ℝ] E,
    (LinearMap.range P : Set E) = latticeDisjointComplement (latticeDisjointComplement {u}) ∧
    (∀ x, P (P x) = P x) ∧ ∀ x, 0 ≤ x → 0 ≤ P x ∧ P x ≤ x

/-- The principal order ideal as a concrete carrier. -/
def principalOrderIdeal (u : E) : Set E := {x | ∃ c : ℝ, 0 ≤ c ∧ |x| ≤ c • u}

/-- The order-unit gauge, used only on the principal ideal when `u` is nonnegative. -/
def orderUnitGauge (u x : E) : ℝ := sInf {c : ℝ | 0 ≤ c ∧ |x| ≤ c • u}

set_option linter.unusedVariables false in
/-- **19.8**, Freudenthal approximation in the equivalent order-error form.
The Archimedean hypothesis is explicit, as required by the usual spectral theorem. -/
theorem freudenthal_approximation (ha : IsArchimedeanRieszSpace E)
    (hp : HasPrincipalBandProjections E) {u x : E} (hu : 0 ≤ u)
    (hx : x ∈ principalOrderIdeal u) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (a : Fin n → ℝ) (v : Fin n → E),
      (∀ i, IsLatticeComponent (v i) u) ∧
      (∀ i j, i ≠ j → LatticeDisjoint (v i) (v j)) ∧
      |x - ∑ i, a i • v i| ≤ ε • u :=
  freudenthal_components hp hu hx hε

/-- **19.20**, Riesz–Kantorovich: order-bounded operators into a Dedekind-complete vector
lattice are precisely differences of positive operators. -/
theorem orderBounded_iff_regular (hcomplete : IsDedekindCompleteRieszSpace F) (T : E →ₗ[ℝ] F) :
    IsOrderBoundedLinearMap T ↔ IsRegularLinearMap T := by
  constructor
  · intro hT
    let imageSet : E → Set F := fun x => {z | ∃ y : E, 0 ≤ y ∧ y ≤ x ∧ z = T y}
    have hnonempty : ∀ {x : E}, 0 ≤ x → (imageSet x).Nonempty := by
      intro x hx
      exact ⟨0, 0, le_rfl, hx, (map_zero T).symm⟩
    have hbdd : ∀ {x : E}, 0 ≤ x → BddAbove (imageSet x) := by
      intro x hx
      obtain ⟨_c, d, hcd⟩ := hT 0 x
      refine ⟨d, ?_⟩
      intro z hz
      obtain ⟨y, hy0, hyx, rfl⟩ := hz
      exact (hcd y hy0 hyx).2
    have hexists : ∀ x : E, ∃ z : F, IsLUB (imageSet x⁺) z := by
      intro x
      exact hcomplete _ (hnonempty (posPart_nonneg x)) (hbdd (posPart_nonneg x))
    let g : E → F := fun x => Classical.choose (hexists x)
    have hspec : ∀ x : E, IsLUB (imageSet x⁺) (g x) :=
      fun x => Classical.choose_spec (hexists x)
    have hspec_pos : ∀ {x : E}, 0 ≤ x → IsLUB (imageSet x) (g x) := by
      intro x hx
      have h := hspec x
      rw [posPart_eq_self.2 hx] at h
      exact h
    have hadd : ∀ x y : E, 0 ≤ x → 0 ≤ y → g (x + y) = g x + g y := by
      intro x y hx hy
      have hxy : 0 ≤ x + y := add_nonneg hx hy
      have hset : imageSet (x + y) =
          {z | ∃ a b, a ∈ imageSet x ∧ b ∈ imageSet y ∧ z = a + b} := by
        ext z
        constructor
        · intro hz
          obtain ⟨w, hw0, hwxy, rfl⟩ := hz
          obtain ⟨w1, w2, hw, hw10, hw1x, hw20, hw2y⟩ :=
            exists_add_eq_of_le_add hw0 hx hy hwxy
          exact ⟨T w1, T w2, ⟨w1, hw10, hw1x, rfl⟩, ⟨w2, hw20, hw2y, rfl⟩,
            by rw [← map_add, hw]⟩
        · intro hz
          obtain ⟨a, b, ⟨y1, hy10, hy1x, rfl⟩, ⟨y2, hy20, hy2y, rfl⟩, rfl⟩ := hz
          exact ⟨y1 + y2, add_nonneg hy10 hy20, add_le_add hy1x hy2y,
            (map_add T y1 y2).symm⟩
      have hlub := isLUB_add (hspec_pos hx) (hspec_pos hy)
      rw [← hset] at hlub
      exact IsLUB.unique (hspec_pos hxy) hlub
    have hzero : g 0 = 0 := by
      have hL : IsLUB (imageSet (0 : E)) 0 := by
        refine ⟨?_, ?_⟩
        · intro z hz
          obtain ⟨y, hy0, hyx, rfl⟩ := hz
          have hy0' : y = 0 := le_antisymm hyx hy0
          rw [hy0']
          exact le_of_eq (map_zero T)
        · intro b hb
          exact hb ⟨0, le_rfl, le_rfl, (map_zero T).symm⟩
      exact IsLUB.unique (hspec_pos le_rfl) hL
    have hsmul : ∀ (c : ℝ) (x : E), 0 ≤ c → 0 ≤ x → g (c • x) = c • g x := by
      intro c x hc hx
      rcases eq_or_lt_of_le hc with hc0 | hcpos
      · rw [← hc0, zero_smul, zero_smul, hzero]
      · have hset : imageSet (c • x) = (fun w : F => c • w) '' imageSet x := by
          ext z
          constructor
          · intro hz
            obtain ⟨y, hy0, hyx, rfl⟩ := hz
            have hinv : 0 ≤ c⁻¹ := inv_nonneg.2 hcpos.le
            have hle : c⁻¹ • y ≤ x := by
              calc
                c⁻¹ • y ≤ c⁻¹ • (c • x) := smul_le_smul_of_nonneg_left hyx hinv
                _ = x := by rw [← mul_smul, inv_mul_cancel₀ hcpos.ne', one_smul]
            refine ⟨T (c⁻¹ • y), ⟨c⁻¹ • y, smul_nonneg hinv hy0, hle, rfl⟩, ?_⟩
            change c • T (c⁻¹ • y) = T y
            rw [map_smul, ← mul_smul, mul_inv_cancel₀ hcpos.ne', one_smul]
          · rintro ⟨w, ⟨y, hy0, hyx, rfl⟩, rfl⟩
            exact ⟨c • y, smul_nonneg hcpos.le hy0,
              smul_le_smul_of_nonneg_left hyx hcpos.le, (map_smul T c y).symm⟩
        have hlub := isLUB_smul_of_pos hcpos (hspec_pos hx)
        rw [← hset] at hlub
        exact IsLUB.unique (hspec_pos (smul_nonneg hcpos.le hx)) hlub
    let S := coneAdditiveLinearMap g hadd hsmul
    have hSon : ∀ {x : E}, 0 ≤ x → S x = g x :=
      fun {_x} hx => coneAdditiveLinearMap_apply_of_nonneg g hadd hsmul hx
    have hSpos : IsPositiveLinearMap S := by
      intro x hx
      rw [hSon hx]
      exact (hspec_pos hx).1 ⟨0, le_rfl, hx, (map_zero T).symm⟩
    have hdom : ∀ {x : E}, 0 ≤ x → T x ≤ S x := by
      intro x hx
      rw [hSon hx]
      exact (hspec_pos hx).1 ⟨x, hx, le_rfl, rfl⟩
    have hUpos : IsPositiveLinearMap (S - T) := by
      intro x hx
      rw [LinearMap.sub_apply]
      exact sub_nonneg.2 (hdom hx)
    refine ⟨S, S - T, hSpos, hUpos, ?_⟩
    ext x
    simp only [LinearMap.sub_apply]
    exact (sub_sub_cancel (S x) (T x)).symm
  · exact IsRegularLinearMap.isOrderBounded

/-- Binary Riesz–Kantorovich supremum with its actual positive-cone least-upper-bound property.
Bundling the full Dedekind-complete operator lattice is separate infrastructure. -/
theorem exists_rieszKantorovich_sup (hcomplete : IsDedekindCompleteRieszSpace F)
    (S T : E →ₗ[ℝ] F) (hS : IsOrderBoundedLinearMap S) (hT : IsOrderBoundedLinearMap T) :
    ∃ U : E →ₗ[ℝ] F, IsOrderBoundedLinearMap U ∧
      (∀ x, 0 ≤ x → S x ≤ U x ∧ T x ≤ U x) ∧
      (∀ V : E →ₗ[ℝ] F, (∀ x, 0 ≤ x → S x ≤ V x ∧ T x ≤ V x) →
        ∀ x, 0 ≤ x → U x ≤ V x) ∧
      ∀ x, 0 ≤ x → IsLUB {z | ∃ y, 0 ≤ y ∧ y ≤ x ∧ z = S y + T (x - y)} (U x) := by
  let rkSet : E → Set F := fun x =>
    {z | ∃ y : E, 0 ≤ y ∧ y ≤ x ∧ z = S y + T (x - y)}
  have hnonempty : ∀ {x : E}, 0 ≤ x → (rkSet x).Nonempty := by
    intro x hx
    exact ⟨T x, 0, le_rfl, hx, by rw [map_zero S, sub_zero, zero_add]⟩
  have hbdd : ∀ {x : E}, 0 ≤ x → BddAbove (rkSet x) := by
    intro x hx
    obtain ⟨_cS, dS, hSb⟩ := hS 0 x
    obtain ⟨_cT, dT, hTb⟩ := hT 0 x
    refine ⟨dS + dT, ?_⟩
    intro z hz
    obtain ⟨y, hy0, hyx, rfl⟩ := hz
    exact add_le_add (hSb y hy0 hyx).2
      (hTb (x - y) (sub_nonneg.2 hyx) (sub_le_self _ hy0)).2
  have hexists : ∀ x : E, ∃ z : F, IsLUB (rkSet x⁺) z := by
    intro x
    exact hcomplete _ (hnonempty (posPart_nonneg x)) (hbdd (posPart_nonneg x))
  let g : E → F := fun x => Classical.choose (hexists x)
  have hspec : ∀ x : E, IsLUB (rkSet x⁺) (g x) :=
    fun x => Classical.choose_spec (hexists x)
  have hspec_pos : ∀ {x : E}, 0 ≤ x → IsLUB (rkSet x) (g x) := by
    intro x hx
    have h := hspec x
    rw [posPart_eq_self.2 hx] at h
    exact h
  have hadd : ∀ x y : E, 0 ≤ x → 0 ≤ y → g (x + y) = g x + g y := by
    intro x y hx hy
    have hxy : 0 ≤ x + y := add_nonneg hx hy
    have hset : rkSet (x + y) =
        {z | ∃ a b, a ∈ rkSet x ∧ b ∈ rkSet y ∧ z = a + b} := by
      ext z
      constructor
      · intro hz
        obtain ⟨w, hw0, hwxy, rfl⟩ := hz
        obtain ⟨w1, w2, hw, hw10, hw1x, hw20, hw2y⟩ :=
          exists_add_eq_of_le_add hw0 hx hy hwxy
        refine ⟨S w1 + T (x - w1), S w2 + T (y - w2),
          ⟨w1, hw10, hw1x, rfl⟩, ⟨w2, hw20, hw2y, rfl⟩, ?_⟩
        have hrest : (x + y) - w = (x - w1) + (y - w2) := by
          rw [hw]
          abel
        have hSw : S w = S w1 + S w2 := by
          rw [hw, map_add]
        rw [hSw, hrest, map_add]
        abel
      · intro hz
        obtain ⟨a, b, ⟨y1, hy10, hy1x, rfl⟩, ⟨y2, hy20, hy2y, rfl⟩, rfl⟩ := hz
        refine ⟨y1 + y2, add_nonneg hy10 hy20, add_le_add hy1x hy2y, ?_⟩
        have hrest : (x + y) - (y1 + y2) = (x - y1) + (y - y2) := by abel
        rw [hrest, map_add, map_add]
        abel
    have hlub := isLUB_add (hspec_pos hx) (hspec_pos hy)
    rw [← hset] at hlub
    exact IsLUB.unique (hspec_pos hxy) hlub
  have hzero : g 0 = 0 := by
    have hL : IsLUB (rkSet (0 : E)) 0 := by
      refine ⟨?_, ?_⟩
      · intro z hz
        obtain ⟨y, hy0, hyx, rfl⟩ := hz
        have hy0' : y = 0 := le_antisymm hyx hy0
        rw [hy0', map_zero S, sub_zero, map_zero T, add_zero]
      · intro b hb
        exact hb ⟨0, le_rfl, le_rfl, by rw [map_zero S, sub_zero, map_zero T, zero_add]⟩
    exact IsLUB.unique (hspec_pos le_rfl) hL
  have hsmul : ∀ (c : ℝ) (x : E), 0 ≤ c → 0 ≤ x → g (c • x) = c • g x := by
    intro c x hc hx
    rcases eq_or_lt_of_le hc with hc0 | hcpos
    · rw [← hc0, zero_smul, zero_smul, hzero]
    · have hset : rkSet (c • x) = (fun w : F => c • w) '' rkSet x := by
        ext z
        constructor
        · intro hz
          obtain ⟨y, hy0, hyx, rfl⟩ := hz
          have hinv : 0 ≤ c⁻¹ := inv_nonneg.2 hcpos.le
          have hle : c⁻¹ • y ≤ x := by
            calc
              c⁻¹ • y ≤ c⁻¹ • (c • x) := smul_le_smul_of_nonneg_left hyx hinv
              _ = x := by rw [← mul_smul, inv_mul_cancel₀ hcpos.ne', one_smul]
          refine ⟨S (c⁻¹ • y) + T (x - c⁻¹ • y),
            ⟨c⁻¹ • y, smul_nonneg hinv hy0, hle, rfl⟩, ?_⟩
          have hyeq : y = c • (c⁻¹ • y) := by
            rw [← mul_smul, mul_inv_cancel₀ hcpos.ne', one_smul]
          have hrest : c • x - y = c • (x - c⁻¹ • y) := by
            conv_lhs => rw [hyeq]
            exact (smul_sub c x (c⁻¹ • y)).symm
          change c • (S (c⁻¹ • y) + T (x - c⁻¹ • y)) = S y + T (c • x - y)
          calc
            c • (S (c⁻¹ • y) + T (x - c⁻¹ • y))
                = c • S (c⁻¹ • y) + c • T (x - c⁻¹ • y) := smul_add c _ _
            _ = S (c • (c⁻¹ • y)) + T (c • (x - c⁻¹ • y)) := by
              rw [← map_smul, ← map_smul]
            _ = S y + T (c • x - y) := by rw [← hyeq, ← hrest]
        · rintro ⟨w, ⟨y, hy0, hyx, rfl⟩, rfl⟩
          refine ⟨c • y, smul_nonneg hcpos.le hy0,
            smul_le_smul_of_nonneg_left hyx hcpos.le, ?_⟩
          change c • (S y + T (x - y)) = S (c • y) + T (c • x - c • y)
          rw [smul_add, ← map_smul, ← map_smul, ← smul_sub]
      have hlub := isLUB_smul_of_pos hcpos (hspec_pos hx)
      rw [← hset] at hlub
      exact IsLUB.unique (hspec_pos (smul_nonneg hcpos.le hx)) hlub
  let U := coneAdditiveLinearMap g hadd hsmul
  have hUon : ∀ {x : E}, 0 ≤ x → U x = g x :=
    fun {_x} hx => coneAdditiveLinearMap_apply_of_nonneg g hadd hsmul hx
  have hdom : ∀ x : E, 0 ≤ x → S x ≤ U x ∧ T x ≤ U x := by
    intro x hx
    rw [hUon hx]
    refine ⟨?_, ?_⟩
    · exact (hspec_pos hx).1 ⟨x, hx, le_rfl, by rw [sub_self, map_zero, add_zero]⟩
    · exact (hspec_pos hx).1 ⟨0, le_rfl, hx, by rw [map_zero, sub_zero, zero_add]⟩
  have hleast : ∀ V : E →ₗ[ℝ] F,
      (∀ x, 0 ≤ x → S x ≤ V x ∧ T x ≤ V x) → ∀ x, 0 ≤ x → U x ≤ V x := by
    intro V hV x hx
    rw [hUon hx]
    refine (hspec_pos hx).2 ?_
    intro z hz
    obtain ⟨y, hy0, hyx, rfl⟩ := hz
    have hsum : y + (x - y) = x := by abel
    calc
      S y + T (x - y) ≤ V y + V (x - y) :=
        add_le_add (hV y hy0).1 (hV (x - y) (sub_nonneg.2 hyx)).2
      _ = V x := by rw [← map_add, hsum]
  have hord : IsOrderBoundedLinearMap U := by
    intro a b
    obtain ⟨cS, dS, hSb⟩ := hS 0 (b - a)
    obtain ⟨cT, dT, hTb⟩ := hT 0 (b - a)
    refine ⟨cS + cT + U a, dS + dT + U a, ?_⟩
    intro x hax hxb
    have hab : 0 ≤ b - a := sub_nonneg.2 (hax.trans hxb)
    have hxa : 0 ≤ x - a := sub_nonneg.2 hax
    have hxab : x - a ≤ b - a := sub_le_sub_right hxb a
    have hsplit : U x = U a + U (x - a) := by
      have hsum : a + (x - a) = x := by abel
      rw [← map_add, hsum]
    rw [hsplit, hUon hxa]
    have hupper : g (x - a) ≤ dS + dT := by
      refine (hspec_pos hxa).2 ?_
      intro z hz
      obtain ⟨y, hy0, hyxa, rfl⟩ := hz
      have hyb : y ≤ b - a := hyxa.trans hxab
      have hrest0 : 0 ≤ x - a - y := sub_nonneg.2 hyxa
      have hrestb : x - a - y ≤ b - a := (sub_le_self _ hy0).trans hxab
      exact add_le_add (hSb y hy0 hyb).2 (hTb (x - a - y) hrest0 hrestb).2
    have hlower : cS + cT ≤ g (x - a) := by
      have hzmem : S 0 + T (x - a) ∈ rkSet (x - a) :=
        ⟨0, le_rfl, hxa, by rw [sub_zero]⟩
      have hle : cS + cT ≤ S 0 + T (x - a) :=
        add_le_add (hSb 0 le_rfl hab).1 (hTb (x - a) hxa hxab).1
      exact hle.trans ((hspec_pos hxa).1 hzmem)
    refine ⟨?_, ?_⟩
    · calc
        cS + cT + U a = U a + (cS + cT) := by abel
        _ ≤ U a + g (x - a) := add_le_add le_rfl hlower
    · calc
        U a + g (x - a) ≤ U a + (dS + dT) := add_le_add le_rfl hupper
        _ = dS + dT + U a := by abel
  refine ⟨U, hord, hdom, hleast, ?_⟩
  intro x hx
  rw [hUon hx]
  exact hspec_pos hx

end CKMA
