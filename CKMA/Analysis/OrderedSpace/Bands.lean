/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.OrderedSpace.Bands.Lattice
public import CKMA.Analysis.OrderedSpace.Bands.Freudenthal
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Tactic.Abel

/-!
# Riesz ideals, band projections, and order approximation

A Riesz ideal is a real linear subspace solid under domination by lattice absolute values.
Bands are closed under existing positive suprema. Dedekind completeness is stated on the
chosen vector-lattice order, and the Archimedean predicate is the vector-lattice axiom rather
than positive-element domination in a linear order.

Band projections, Freudenthal component approximation, and Riesz–Kantorovich suprema are
formulated through their order characterizations. Positive maps reuse Mathlib's monotonicity
criterion; regular maps are differences of positive maps. Sources: GAPS 19.5, 19.8, and 19.20.

## Main definitions

* `CKMA.RieszIdeal`: solid linear subspace of a Riesz space.
* `CKMA.RieszIdeal.IsBand`: ideal closed under existing suprema of nonempty positive subsets.
* `CKMA.IsPositiveLinearMap`: positive linear operator between ordered real vector spaces.
* `CKMA.IsRegularLinearMap`: difference of two positive linear operators.
* `CKMA.IsOrderBoundedLinearMap`: linear operator preserving order boundedness on intervals.
* `CKMA.IsDedekindCompleteRieszSpace`: Dedekind completeness of a Riesz space.
* `CKMA.IsArchimedeanRieszSpace`: the Archimedean axiom of a vector lattice.
* `CKMA.IsLatticeComponent`: component of a positive vector, disjoint from its remainder.
* `CKMA.HasPrincipalBandProjections`: principal band projection property.
* `CKMA.principalOrderIdeal`, `CKMA.orderUnitGauge`: principal order ideal of a vector and its
  order-unit gauge. On the ideal the gauge is the least admissible scalar; `Real.sInf` of the
  empty set of scalars is `0`, so the gauge is used on the principal ideal.

## Main results

* `CKMA.isPositiveLinearMap_iff_monotone`: positive linear maps are the monotone linear maps.
* `CKMA.exists_bandProjection`: existence of the band projection onto a band in a Dedekind-complete
  Riesz space.
* `CKMA.freudenthal_approximation`: Freudenthal spectral theorem from principal band projections.
* `CKMA.orderBounded_iff_regular`: Riesz–Kantorovich theorem characterizing order-bounded operators
  as regular operators.
* `CKMA.exists_rieszKantorovich_sup`: the supremum of two order-bounded operators into a
  Dedekind-complete Riesz space, given on the positive cone by the Riesz–Kantorovich formula
  `(S ⊔ T) x = sup {S y + T (x - y) | 0 ≤ y ≤ x}`.
* `CKMA.abs_le_gauge_smul`, `CKMA.gauge_le_iff`: the gauge attains `|x| ≤ c • u` and is the
  least such scalar.
* `CKMA.gauge_smul`, `CKMA.gauge_add`: absolute homogeneity and subadditivity of the gauge.
-/

public section

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
@[expose]
def RieszIdeal.IsBand (B : RieszIdeal E) : Prop :=
  ∀ s : Set E, s.Nonempty → (∀ x ∈ s, 0 ≤ x ∧ x ∈ B.toSubmodule) →
    ∀ x : E, IsLUB s x → x ∈ B.toSubmodule

section PositiveMaps

variable {E₁ E₂ : Type*} [AddCommGroup E₁] [PartialOrder E₁] [Module ℝ E₁]
    [IsOrderedAddMonoid E₁] [AddCommGroup E₂] [PartialOrder E₂] [Module ℝ E₂]
    [IsOrderedAddMonoid E₂]

/-- Positivity of an algebraic linear operator on ordered real vector spaces. -/
@[expose]
def IsPositiveLinearMap (T : E₁ →ₗ[ℝ] E₂) : Prop := ∀ x, 0 ≤ x → 0 ≤ T x

omit [IsOrderedAddMonoid E₁] in
/-- The identity is positive. -/
private theorem isPositiveLinearMap_id : IsPositiveLinearMap (LinearMap.id : E₁ →ₗ[ℝ] E₁) :=
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
@[expose]
def IsRegularLinearMap (T : E₁ →ₗ[ℝ] E₂) : Prop :=
  ∃ S U : E₁ →ₗ[ℝ] E₂, IsPositiveLinearMap S ∧ IsPositiveLinearMap U ∧ T = S - U

/-- Order boundedness is tested on every closed order interval. -/
@[expose]
def IsOrderBoundedLinearMap (T : E₁ →ₗ[ℝ] E₂) : Prop :=
  ∀ a b : E₁, ∃ c d : E₂, ∀ x : E₁, a ≤ x → x ≤ b → c ≤ T x ∧ T x ≤ d

/-- Every positive operator maps an order interval into the interval of its endpoint images. -/
private theorem IsPositiveLinearMap.isOrderBounded {T : E₁ →ₗ[ℝ] E₂} (hT : IsPositiveLinearMap T) :
    IsOrderBoundedLinearMap T := by
  intro a b
  exact ⟨T a, T b, fun _ ha hb ↦ ⟨hT.monotone ha, hT.monotone hb⟩⟩

/-- Every regular operator is order bounded, without a Dedekind-completeness hypothesis. -/
private theorem IsRegularLinearMap.isOrderBounded {T : E₁ →ₗ[ℝ] E₂} (hT : IsRegularLinearMap T) :
    IsOrderBoundedLinearMap T := by
  obtain ⟨S, U, hS, hU, rfl⟩ := hT
  intro a b
  refine ⟨S a - U b, S b - U a, ?_⟩
  intro x ha hb
  exact ⟨sub_le_sub (hS.monotone ha) (hU.monotone hb),
    sub_le_sub (hS.monotone hb) (hU.monotone ha)⟩

end PositiveMaps

/-- Dedekind completeness stated on the already chosen Riesz order. -/
@[expose]
def IsDedekindCompleteRieszSpace (E : Type*) [Lattice E] : Prop :=
  ∀ s : Set E, s.Nonempty → BddAbove s → ∃ x : E, IsLUB s x

/-- Suprema of a family of sets over the positive cone that is additive and positively
homogeneous for the Minkowski operations, and has `0` as the supremum at `0`, are the values of a
linear map in a Dedekind-complete target. -/
private theorem exists_linearMap_isLUB (hcomplete : IsDedekindCompleteRieszSpace F)
    (A : E → Set F) (hne : ∀ x, 0 ≤ x → (A x).Nonempty) (hbdd : ∀ x, 0 ≤ x → BddAbove (A x))
    (hzero : IsLUB (A 0) 0)
    (hadd : ∀ x y, 0 ≤ x → 0 ≤ y → A (x + y) = {z | ∃ a b, a ∈ A x ∧ b ∈ A y ∧ z = a + b})
    (hsmul : ∀ (c : ℝ) (x : E), 0 < c → 0 ≤ x → A (c • x) = (fun w : F ↦ c • w) '' A x) :
    ∃ U : E →ₗ[ℝ] F, ∀ x, 0 ≤ x → IsLUB (A x) (U x) := by
  have hexists : ∀ x : E, ∃ z : F, IsLUB (A x⁺) z := fun x ↦
    hcomplete _ (hne _ (posPart_nonneg x)) (hbdd _ (posPart_nonneg x))
  choose g hg using hexists
  have hg_pos : ∀ {x : E}, 0 ≤ x → IsLUB (A x) (g x) := by
    intro x hx
    simpa only [posPart_eq_self.2 hx] using hg x
  have hgadd : ∀ x y : E, 0 ≤ x → 0 ≤ y → g (x + y) = g x + g y := by
    intro x y hx hy
    have hlub := isLUB_add (hg_pos hx) (hg_pos hy)
    rw [← hadd x y hx hy] at hlub
    exact (hg_pos (add_nonneg hx hy)).unique hlub
  have hgsmul : ∀ (c : ℝ) (x : E), 0 ≤ c → 0 ≤ x → g (c • x) = c • g x := by
    intro c x hc hx
    rcases hc.eq_or_lt with rfl | hcpos
    · rw [zero_smul, zero_smul]
      exact (hg_pos le_rfl).unique hzero
    · have hlub := isLUB_smul_of_pos hcpos (hg_pos hx)
      rw [← hsmul c x hcpos hx] at hlub
      exact (hg_pos (smul_nonneg hcpos.le hx)).unique hlub
  refine ⟨coneAdditiveLinearMap g hgadd hgsmul, fun x hx ↦ ?_⟩
  rw [coneAdditiveLinearMap_apply_of_nonneg g hgadd hgsmul hx]
  exact hg_pos hx

/-- The vectors of a Riesz ideal in the order interval `[0, x]`. -/
private def bandSlice (B : RieszIdeal E) (x : E) : Set E :=
  {y | y ∈ B.toSubmodule ∧ 0 ≤ y ∧ y ≤ x}

omit [IsOrderedModule ℝ E] in
/-- A Riesz ideal contains every positive vector below one of its elements. -/
private theorem RieszIdeal.mem_of_nonneg_of_le (B : RieszIdeal E) {w z : E} (hw : 0 ≤ w)
    (hwz : w ≤ z) (hz : z ∈ B.toSubmodule) : w ∈ B.toSubmodule :=
  B.solid (by rw [abs_of_nonneg hw, abs_of_nonneg (hw.trans hwz)]; exact hwz) hz

omit [IsOrderedModule ℝ E] in
/-- The slice of a Riesz ideal below a sum of positive vectors is the sum of the slices, by the
Riesz decomposition property. -/
private theorem bandSlice_add (B : RieszIdeal E) {x y : E} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    bandSlice B (x + y) = {z | ∃ a b, a ∈ bandSlice B x ∧ b ∈ bandSlice B y ∧ z = a + b} := by
  ext w
  constructor
  · rintro ⟨hwB, hw0, hwxy⟩
    obtain ⟨w1, w2, hw, hw10, hw1x, hw20, hw2y⟩ := exists_add_eq_of_le_add hw0 hx hy hwxy
    have hw1 : w1 ≤ w := hw ▸ le_add_of_nonneg_right hw20
    have hw2 : w2 ≤ w := hw ▸ le_add_of_nonneg_left hw10
    exact ⟨w1, w2, ⟨B.mem_of_nonneg_of_le hw10 hw1 hwB, hw10, hw1x⟩,
      ⟨B.mem_of_nonneg_of_le hw20 hw2 hwB, hw20, hw2y⟩, hw⟩
  · rintro ⟨a, b, ⟨haB, ha0, hax⟩, ⟨hbB, hb0, hby⟩, rfl⟩
    exact ⟨B.toSubmodule.add_mem haB hbB, add_nonneg ha0 hb0, add_le_add hax hby⟩

omit [IsOrderedAddMonoid E] in
/-- The slice of a Riesz ideal below a positive multiple is the rescaled slice. -/
private theorem bandSlice_smul (B : RieszIdeal E) {c : ℝ} (hc : 0 < c) (x : E) :
    bandSlice B (c • x) = (fun y ↦ c • y) '' bandSlice B x := by
  ext z
  constructor
  · intro hz
    have hinv : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
    refine ⟨c⁻¹ • z, ⟨B.toSubmodule.smul_mem c⁻¹ hz.1, smul_nonneg hinv hz.2.1, ?_⟩, ?_⟩
    · calc
        c⁻¹ • z ≤ c⁻¹ • (c • x) := smul_le_smul_of_nonneg_left hz.2.2 hinv
        _ = x := by rw [← mul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    · simp only [← mul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  · rintro ⟨y, hy, rfl⟩
    exact ⟨B.toSubmodule.smul_mem c hy.1, smul_nonneg hc.le hy.2.1,
      smul_le_smul_of_nonneg_left hy.2.2 hc.le⟩

omit [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] in
/-- A positive element of a Riesz ideal is the greatest element of its own slice. -/
private theorem isLUB_bandSlice_self (B : RieszIdeal E) {z : E} (hzB : z ∈ B.toSubmodule)
    (hz : 0 ≤ z) : IsLUB (bandSlice B z) z :=
  ⟨fun _y hy ↦ hy.2.2, fun _b hb ↦ hb ⟨hzB, hz, le_rfl⟩⟩

omit [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] in
/-- In a band, the supremum of a slice lies in that slice. -/
private theorem mem_bandSlice_of_isLUB {B : RieszIdeal E} (hB : B.IsBand) {x z : E} (hx : 0 ≤ x)
    (hL : IsLUB (bandSlice B x) z) : z ∈ bandSlice B x :=
  ⟨hB (bandSlice B x) ⟨0, B.toSubmodule.zero_mem, le_rfl, hx⟩ (fun _y hy ↦ ⟨hy.2.1, hy.1⟩) z hL,
    hL.1 ⟨B.toSubmodule.zero_mem, le_rfl, hx⟩, hL.2 fun _y hy ↦ hy.2.2⟩

omit [IsOrderedModule ℝ E] in
/-- A positive vector whose slice in a Riesz ideal has supremum `0` is disjoint from every
element of the ideal. -/
private theorem inf_abs_eq_zero_of_isLUB_bandSlice {B : RieszIdeal E} {z y : E} (hz : 0 ≤ z)
    (hL : IsLUB (bandSlice B z) 0) (hy : y ∈ B.toSubmodule) : z ⊓ |y| = 0 := by
  have hw0 : 0 ≤ z ⊓ |y| := le_inf hz (abs_nonneg y)
  have habs : |y| ∈ B.toSubmodule := B.solid (le_of_eq (abs_abs y)) hy
  exact le_antisymm
    (hL.1 ⟨B.mem_of_nonneg_of_le hw0 inf_le_right habs, hw0, inf_le_left⟩) hw0

omit [IsOrderedModule ℝ E] in
/-- A linear map whose values on the positive cone are the suprema of the slices of a band is
the band projection: it is the identity on the band and its kernel is the disjoint
complement. -/
private theorem bandProjection_spec {B : RieszIdeal E} (hB : B.IsBand) {P : E →ₗ[ℝ] E}
    (hP : ∀ x, 0 ≤ x → IsLUB (bandSlice B x) (P x)) :
    LinearMap.range P = B.toSubmodule ∧ (∀ x, P (P x) = P x) ∧
      ∀ x, P x = 0 ↔ x ∈ latticeDisjointComplement (B.toSubmodule : Set E) := by
  have hsplit : ∀ x, P x = P x⁺ - P x⁻ := fun x ↦ by rw [← map_sub, posPart_sub_negPart]
  have hposle : ∀ z : E, z⁺ ≤ |z| := fun z ↦
    (le_add_of_nonneg_right (negPart_nonneg z)).trans_eq (posPart_add_negPart z)
  have hnegle : ∀ z : E, z⁻ ≤ |z| := fun z ↦
    (le_add_of_nonneg_left (posPart_nonneg z)).trans_eq (posPart_add_negPart z)
  have hmem : ∀ {x}, 0 ≤ x → P x ∈ bandSlice B x := fun hx ↦ mem_bandSlice_of_isLUB hB hx (hP _ hx)
  have hmemB : ∀ x, P x ∈ B.toSubmodule := fun x ↦ by
    rw [hsplit x]
    exact B.toSubmodule.sub_mem (hmem (posPart_nonneg x)).1 (hmem (negPart_nonneg x)).1
  have hfixB : ∀ z ∈ B.toSubmodule, P z = z := by
    intro z hz
    have habs : |z| ∈ B.toSubmodule := B.solid (le_of_eq (abs_abs z)) hz
    have hfix : ∀ w, 0 ≤ w → w ≤ |z| → P w = w := fun w hw hwz ↦
      (hP w hw).unique (isLUB_bandSlice_self B (B.mem_of_nonneg_of_le hw hwz habs) hw)
    rw [hsplit z, hfix _ (posPart_nonneg z) (hposle z),
      hfix _ (negPart_nonneg z) (hnegle z), posPart_sub_negPart]
  refine ⟨Submodule.ext fun z ↦ ⟨?_, fun hz ↦ ⟨z, hfixB z hz⟩⟩, fun x ↦ hfixB _ (hmemB x),
    fun x ↦ ⟨fun hPx y hy ↦ ?_, fun hx ↦ ?_⟩⟩
  · rintro ⟨y, rfl⟩
    exact hmemB y
  · have heq : P x⁺ = P x⁻ := sub_eq_zero.mp (by rw [← hsplit, hPx])
    have hpos0 : P x⁺ = 0 := by
      have hle : P x⁺ ≤ x⁺ ⊓ x⁻ :=
        le_inf (hmem (posPart_nonneg x)).2.2 (heq ▸ (hmem (negPart_nonneg x)).2.2)
      rw [posPart_inf_negPart_eq_zero] at hle
      exact le_antisymm hle (hmem (posPart_nonneg x)).2.1
    have hzero : ∀ w, 0 ≤ w → P w = 0 → w ⊓ |y| = 0 := fun w hw hPw ↦
      inf_abs_eq_zero_of_isLUB_bandSlice hw (hPw ▸ hP w hw) hy
    have h1 : |y| ⊓ x⁺ = 0 := by rw [inf_comm]; exact hzero _ (posPart_nonneg x) hpos0
    have h2 : |y| ⊓ x⁻ = 0 := by
      rw [inf_comm]; exact hzero _ (negPart_nonneg x) (heq ▸ hpos0)
    have hle : |y| ⊓ |x| ≤ 0 := by
      have hsum := inf_add_le_add_inf (abs_nonneg y) (posPart_nonneg x) (negPart_nonneg x)
      rwa [posPart_add_negPart, h1, h2, add_zero] at hsum
    rw [LatticeDisjoint]
    exact le_antisymm (by rw [inf_comm]; exact hle) (le_inf (abs_nonneg x) (abs_nonneg y))
  · have hzero : ∀ w, 0 ≤ w → w ≤ |x| → P w = 0 := by
      intro w hw hwx
      have hmemw := hmem hw
      have hdisj : |x| ⊓ P w = 0 := by
        have hL := hx (P w) hmemw.1
        rwa [LatticeDisjoint, abs_of_nonneg hmemw.2.1] at hL
      rw [← inf_eq_right.2 (hmemw.2.2.trans hwx)]
      exact hdisj
    rw [hsplit, hzero _ (posPart_nonneg x) (hposle x),
      hzero _ (negPart_nonneg x) (hnegle x), sub_zero]

/-- **19.5**: every band in a Dedekind-complete vector lattice admits its band projection.
The positive-vector supremum characterization and the disjoint-complement kernel are included. -/
theorem exists_bandProjection (hcomplete : IsDedekindCompleteRieszSpace E)
    (B : RieszIdeal E) (hB : B.IsBand) : ∃ P : E →ₗ[ℝ] E,
      LinearMap.range P = B.toSubmodule ∧
      (∀ x, P (P x) = P x) ∧
      (∀ x, P x = 0 ↔ x ∈ latticeDisjointComplement (B.toSubmodule : Set E)) ∧
      ∀ x : E, 0 ≤ x → 0 ≤ P x ∧ P x ≤ x ∧
        IsLUB {y | y ∈ B.toSubmodule ∧ 0 ≤ y ∧ y ≤ x} (P x) := by
  have hzero : IsLUB (bandSlice B 0) 0 := isLUB_bandSlice_self B B.toSubmodule.zero_mem le_rfl
  obtain ⟨P, hP⟩ := exists_linearMap_isLUB hcomplete (bandSlice B)
    (fun x hx ↦ ⟨0, B.toSubmodule.zero_mem, le_rfl, hx⟩) (fun x _ ↦ ⟨x, fun _y hy ↦ hy.2.2⟩)
    hzero (fun _x _y hx hy ↦ bandSlice_add B hx hy) (fun _c x hc _ ↦ bandSlice_smul B hc x)
  obtain ⟨hrange, hidem, hker⟩ := bandProjection_spec hB hP
  refine ⟨P, hrange, hidem, hker, fun x hx ↦ ?_⟩
  have hmem := mem_bandSlice_of_isLUB hB hx (hP x hx)
  exact ⟨hmem.2.1, hmem.2.2, hP x hx⟩

/-- The Archimedean axiom appropriate to a partially ordered vector lattice. -/
@[expose]
def IsArchimedeanRieszSpace (E : Type*) [AddCommGroup E] [Lattice E] [Module ℝ E] : Prop :=
  ∀ x y : E, (∀ n : ℕ, (n : ℝ) • x ≤ y) → x ≤ 0

/-- An element is a component of a nonnegative order unit when it is disjoint from its remainder. -/
@[expose]
def IsLatticeComponent (v u : E) : Prop := 0 ≤ v ∧ v ≤ u ∧ v ⊓ (u - v) = 0

/-- The principal projection property is recorded by positive contractive order projections
onto double disjoint complements, rather than by arbitrary assumed theorem predicates. -/
@[expose]
def HasPrincipalBandProjections (E : Type*) [AddCommGroup E] [Lattice E] [Module ℝ E] : Prop :=
  ∀ u : E, ∃ P : E →ₗ[ℝ] E,
    (LinearMap.range P : Set E) = latticeDisjointComplement (latticeDisjointComplement {u}) ∧
    (∀ x, P (P x) = P x) ∧ ∀ x, 0 ≤ x → 0 ≤ P x ∧ P x ≤ x

/-- The principal order ideal as a concrete carrier. -/
@[expose]
def principalOrderIdeal (u : E) : Set E := {x | ∃ c : ℝ, 0 ≤ c ∧ |x| ≤ c • u}

/-- The order-unit gauge, used only on the principal ideal when `u` is nonnegative. -/
@[expose]
def orderUnitGauge (u x : E) : ℝ := sInf {c : ℝ | 0 ≤ c ∧ |x| ≤ c • u}

/-- **19.8**, Freudenthal approximation in the equivalent order-error form from the principal
projection property. -/
theorem freudenthal_approximation
    (hp : HasPrincipalBandProjections E) {u x : E} (hu : 0 ≤ u)
    (hx : x ∈ principalOrderIdeal u) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (a : Fin n → ℝ) (v : Fin n → E),
      (∀ i, IsLatticeComponent (v i) u) ∧
      (∀ i j, i ≠ j → LatticeDisjoint (v i) (v j)) ∧
      |x - ∑ i, a i • v i| ≤ ε • u :=
  freudenthal_components hp hu hx hε

/-- The Riesz–Kantorovich set `{S y + T (x - y) | 0 ≤ y ≤ x}`, whose supremum is `(S ⊔ T) x`. -/
private def rieszKantorovichSet (S T : E →ₗ[ℝ] F) (x : E) : Set F :=
  {z | ∃ y, 0 ≤ y ∧ y ≤ x ∧ z = S y + T (x - y)}

omit [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [Lattice F] [IsOrderedAddMonoid F]
  [IsOrderedModule ℝ F] in
/-- The Riesz–Kantorovich set of a positive vector is nonempty. -/
private theorem rieszKantorovichSet_nonempty (S T : E →ₗ[ℝ] F) {x : E} (hx : 0 ≤ x) :
    (rieszKantorovichSet S T x).Nonempty :=
  ⟨T x, 0, le_rfl, hx, by rw [map_zero S, sub_zero, zero_add]⟩

omit [IsOrderedModule ℝ E] [IsOrderedModule ℝ F] in
/-- For order-bounded operators the Riesz–Kantorovich sets are bounded above. -/
private theorem rieszKantorovichSet_bddAbove {S T : E →ₗ[ℝ] F} (hS : IsOrderBoundedLinearMap S)
    (hT : IsOrderBoundedLinearMap T) (x : E) : BddAbove (rieszKantorovichSet S T x) := by
  obtain ⟨_cS, dS, hSb⟩ := hS 0 x
  obtain ⟨_cT, dT, hTb⟩ := hT 0 x
  refine ⟨dS + dT, ?_⟩
  rintro z ⟨y, hy0, hyx, rfl⟩
  exact add_le_add (hSb y hy0 hyx).2 (hTb (x - y) (sub_nonneg.2 hyx) (sub_le_self _ hy0)).2

omit [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [IsOrderedAddMonoid F] [IsOrderedModule ℝ F] in
/-- The Riesz–Kantorovich set at `0` has supremum `0`. -/
private theorem isLUB_rieszKantorovichSet_zero (S T : E →ₗ[ℝ] F) :
    IsLUB (rieszKantorovichSet S T 0) 0 := by
  refine ⟨?_, fun b hb ↦ hb ⟨0, le_rfl, le_rfl, by rw [map_zero S, sub_zero, map_zero T,
    zero_add]⟩⟩
  rintro z ⟨y, hy0, hyx, rfl⟩
  rw [le_antisymm hyx hy0, map_zero S, sub_zero, map_zero T, add_zero]

omit [IsOrderedModule ℝ E] [Lattice F] [IsOrderedAddMonoid F] [IsOrderedModule ℝ F] in
/-- The Riesz–Kantorovich set of a sum of positive vectors is the sum of the sets, by the
Riesz decomposition property. -/
private theorem rieszKantorovichSet_add (S T : E →ₗ[ℝ] F) {x y : E} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    rieszKantorovichSet S T (x + y) = {z | ∃ a b, a ∈ rieszKantorovichSet S T x ∧
      b ∈ rieszKantorovichSet S T y ∧ z = a + b} := by
  ext z
  constructor
  · rintro ⟨w, hw0, hwxy, rfl⟩
    obtain ⟨w1, w2, hw, hw10, hw1x, hw20, hw2y⟩ := exists_add_eq_of_le_add hw0 hx hy hwxy
    refine ⟨S w1 + T (x - w1), S w2 + T (y - w2),
      ⟨w1, hw10, hw1x, rfl⟩, ⟨w2, hw20, hw2y, rfl⟩, ?_⟩
    have hrest : (x + y) - w = (x - w1) + (y - w2) := by
      rw [hw]
      abel
    rw [hrest, hw, map_add, map_add]
    abel
  · rintro ⟨a, b, ⟨y1, hy10, hy1x, rfl⟩, ⟨y2, hy20, hy2y, rfl⟩, rfl⟩
    refine ⟨y1 + y2, add_nonneg hy10 hy20, add_le_add hy1x hy2y, ?_⟩
    have hrest : (x + y) - (y1 + y2) = (x - y1) + (y - y2) := by abel
    rw [hrest, map_add, map_add]
    abel

omit [IsOrderedAddMonoid E] [Lattice F] [IsOrderedAddMonoid F] [IsOrderedModule ℝ F] in
/-- The Riesz–Kantorovich set of a positive multiple is the rescaled set. -/
private theorem rieszKantorovichSet_smul (S T : E →ₗ[ℝ] F) {c : ℝ} (hc : 0 < c) (x : E) :
    rieszKantorovichSet S T (c • x) = (fun w : F ↦ c • w) '' rieszKantorovichSet S T x := by
  ext z
  constructor
  · rintro ⟨y, hy0, hyx, rfl⟩
    have hinv : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
    have hyeq : c • (c⁻¹ • y) = y := by rw [← mul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    have hle : c⁻¹ • y ≤ x := by
      calc
        c⁻¹ • y ≤ c⁻¹ • (c • x) := smul_le_smul_of_nonneg_left hyx hinv
        _ = x := by rw [← mul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    refine ⟨S (c⁻¹ • y) + T (x - c⁻¹ • y), ⟨c⁻¹ • y, smul_nonneg hinv hy0, hle, rfl⟩, ?_⟩
    simp only [smul_add, ← map_smul, smul_sub, hyeq]
  · rintro ⟨w, ⟨y, hy0, hyx, rfl⟩, rfl⟩
    refine ⟨c • y, smul_nonneg hc.le hy0, smul_le_smul_of_nonneg_left hyx hc.le, ?_⟩
    simp only [smul_add, ← map_smul, smul_sub]

/-- For order-bounded `S` and `T` in a Dedekind-complete target there is a linear map whose
value at every positive vector is the supremum of its Riesz–Kantorovich set. -/
private theorem exists_isLUB_rieszKantorovichSet (hcomplete : IsDedekindCompleteRieszSpace F)
    {S T : E →ₗ[ℝ] F} (hS : IsOrderBoundedLinearMap S) (hT : IsOrderBoundedLinearMap T) :
    ∃ U : E →ₗ[ℝ] F, ∀ x, 0 ≤ x → IsLUB (rieszKantorovichSet S T x) (U x) :=
  exists_linearMap_isLUB hcomplete (rieszKantorovichSet S T)
    (fun _x hx ↦ rieszKantorovichSet_nonempty S T hx)
    (fun x _ ↦ rieszKantorovichSet_bddAbove hS hT x) (isLUB_rieszKantorovichSet_zero S T)
    (fun _x _y hx hy ↦ rieszKantorovichSet_add S T hx hy)
    (fun _c x hc _ ↦ rieszKantorovichSet_smul S T hc x)

omit [IsOrderedModule ℝ E] [IsOrderedModule ℝ F] in
/-- A linear map given on the positive cone by the suprema of the Riesz–Kantorovich sets of two
order-bounded operators is order bounded. -/
private theorem isOrderBoundedLinearMap_of_isLUB_rieszKantorovichSet {S T U : E →ₗ[ℝ] F}
    (hS : IsOrderBoundedLinearMap S) (hT : IsOrderBoundedLinearMap T)
    (hU : ∀ x, 0 ≤ x → IsLUB (rieszKantorovichSet S T x) (U x)) :
    IsOrderBoundedLinearMap U := by
  intro a b
  obtain ⟨cS, dS, hSb⟩ := hS 0 (b - a)
  obtain ⟨cT, dT, hTb⟩ := hT 0 (b - a)
  refine ⟨cS + cT + U a, dS + dT + U a, ?_⟩
  intro x hax hxb
  have hab : 0 ≤ b - a := sub_nonneg.2 (hax.trans hxb)
  have hxa : 0 ≤ x - a := sub_nonneg.2 hax
  have hxab : x - a ≤ b - a := sub_le_sub_right hxb a
  have hsplit : U x = U (x - a) + U a := by rw [← map_add, sub_add_cancel]
  have hupper : U (x - a) ≤ dS + dT := by
    refine (hU _ hxa).2 ?_
    rintro z ⟨y, hy0, hyxa, rfl⟩
    exact add_le_add (hSb y hy0 (hyxa.trans hxab)).2
      (hTb (x - a - y) (sub_nonneg.2 hyxa) ((sub_le_self _ hy0).trans hxab)).2
  have hlower : cS + cT ≤ U (x - a) := by
    have hle : cS + cT ≤ S 0 + T (x - a) :=
      add_le_add (hSb 0 le_rfl hab).1 (hTb (x - a) hxa hxab).1
    exact hle.trans ((hU _ hxa).1 ⟨0, le_rfl, hxa, by rw [sub_zero]⟩)
  rw [hsplit]
  exact ⟨add_le_add_left hlower _, add_le_add_left hupper _⟩

/-- **19.20**, Riesz–Kantorovich: order-bounded operators into a Dedekind-complete vector
lattice are precisely differences of positive operators. -/
theorem orderBounded_iff_regular (hcomplete : IsDedekindCompleteRieszSpace F) (T : E →ₗ[ℝ] F) :
    IsOrderBoundedLinearMap T ↔ IsRegularLinearMap T := by
  refine ⟨fun hT ↦ ?_, IsRegularLinearMap.isOrderBounded⟩
  have h0 : IsOrderBoundedLinearMap (0 : E →ₗ[ℝ] F) := fun _ _ ↦
    ⟨0, 0, fun _ _ _ ↦ by simp only [LinearMap.zero_apply, le_refl, and_self]⟩
  obtain ⟨S, hS⟩ := exists_isLUB_rieszKantorovichSet hcomplete hT h0
  have hSpos : IsPositiveLinearMap S := fun x hx ↦
    (hS x hx).1 ⟨0, le_rfl, hx, by simp only [map_zero, LinearMap.zero_apply, add_zero]⟩
  have hUpos : IsPositiveLinearMap (S - T) := fun x hx ↦ by
    rw [LinearMap.sub_apply, sub_nonneg]
    exact (hS x hx).1 ⟨x, hx, le_rfl, by simp only [LinearMap.zero_apply, add_zero]⟩
  exact ⟨S, S - T, hSpos, hUpos, (sub_sub_cancel S T).symm⟩

/-- Binary Riesz–Kantorovich supremum with its actual positive-cone least-upper-bound property.
Bundling the full Dedekind-complete operator lattice is separate infrastructure. -/
theorem exists_rieszKantorovich_sup (hcomplete : IsDedekindCompleteRieszSpace F)
    (S T : E →ₗ[ℝ] F) (hS : IsOrderBoundedLinearMap S) (hT : IsOrderBoundedLinearMap T) :
    ∃ U : E →ₗ[ℝ] F, IsOrderBoundedLinearMap U ∧
      (∀ x, 0 ≤ x → S x ≤ U x ∧ T x ≤ U x) ∧
      (∀ V : E →ₗ[ℝ] F, (∀ x, 0 ≤ x → S x ≤ V x ∧ T x ≤ V x) →
        ∀ x, 0 ≤ x → U x ≤ V x) ∧
      ∀ x, 0 ≤ x → IsLUB {z | ∃ y, 0 ≤ y ∧ y ≤ x ∧ z = S y + T (x - y)} (U x) := by
  obtain ⟨U, hU⟩ := exists_isLUB_rieszKantorovichSet hcomplete hS hT
  refine ⟨U, isOrderBoundedLinearMap_of_isLUB_rieszKantorovichSet hS hT hU,
    fun x hx ↦ ⟨?_, ?_⟩, fun V hV x hx ↦ (hU x hx).2 ?_, hU⟩
  · exact (hU x hx).1 ⟨x, hx, le_rfl, by rw [sub_self, map_zero, add_zero]⟩
  · exact (hU x hx).1 ⟨0, le_rfl, hx, by rw [map_zero, sub_zero, zero_add]⟩
  · rintro z ⟨y, hy0, hyx, rfl⟩
    calc
      S y + T (x - y) ≤ V y + V (x - y) :=
        add_le_add (hV y hy0).1 (hV (x - y) (sub_nonneg.2 hyx)).2
      _ = V x := by rw [← map_add, add_sub_cancel]


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
theorem gauge_nonneg {u x : E} (hx : x ∈ principalOrderIdeal u) :
    0 ≤ orderUnitGauge u x := by
  unfold orderUnitGauge
  exact le_csInf (gaugeSet_nonempty hx) fun _ hc => hc.1

omit [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- An admissible scalar dominates the gauge. -/
theorem gauge_le_of_mem {u x : E} {c : ℝ} (hc : 0 ≤ c ∧ |x| ≤ c • u) :
    orderUnitGauge u x ≤ c := by
  unfold orderUnitGauge
  exact csInf_le (bddBelow_gaugeSet u x) hc

/-- Archimedean attainment: the absolute value is bounded by the gauge multiple. -/
theorem abs_le_gauge_smul {u x : E} (hu : 0 ≤ u) (hx : x ∈ principalOrderIdeal u) :
    |x| ≤ orderUnitGauge u x • u := by
  set p : ℝ := orderUnitGauge u x
  have hp : 0 ≤ p := gauge_nonneg hx
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
theorem gauge_le_iff {u x : E} (hu : 0 ≤ u) (hx : x ∈ principalOrderIdeal u) {c : ℝ}
    (hc : 0 ≤ c) : orderUnitGauge u x ≤ c ↔ |x| ≤ c • u := by
  constructor
  · intro hle
    exact (abs_le_gauge_smul hu hx).trans (smul_le_smul_of_nonneg_right hle hu)
  · intro habs
    exact gauge_le_of_mem ⟨hc, habs⟩

/-- The gauge is absolutely homogeneous on the principal ideal. -/
theorem gauge_smul {u x : E} (hu : 0 ≤ u) (hx : x ∈ principalOrderIdeal u) (c : ℝ) :
    orderUnitGauge u (c • x) = |c| * orderUnitGauge u x := by
  have hx' : c • x ∈ principalOrderIdeal u := by
    obtain ⟨d, hd, hxd⟩ := hx
    refine ⟨|c| * d, mul_nonneg (abs_nonneg c) hd, ?_⟩
    calc |c • x| = |c| • |x| := abs_smul c x
      _ ≤ |c| • (d • u) := smul_le_smul_of_nonneg_left hxd (abs_nonneg c)
      _ = (|c| * d) • u := by rw [mul_smul]
  have hp : 0 ≤ orderUnitGauge u x := gauge_nonneg hx
  have hq : 0 ≤ orderUnitGauge u (c • x) := gauge_nonneg hx'
  apply le_antisymm
  · have habs : |c • x| ≤ (|c| * orderUnitGauge u x) • u := by
      calc |c • x| = |c| • |x| := abs_smul c x
        _ ≤ |c| • (orderUnitGauge u x • u) :=
            smul_le_smul_of_nonneg_left (abs_le_gauge_smul hu hx) (abs_nonneg c)
        _ = (|c| * orderUnitGauge u x) • u := by rw [mul_smul]
    exact (gauge_le_iff hu hx' (mul_nonneg (abs_nonneg c) hp)).2 habs
  · rcases eq_or_ne c 0 with rfl | hc
    · simpa using hq
    · have habs : |x| ≤ (|c|⁻¹ * orderUnitGauge u (c • x)) • u := by
        have hback : x = c⁻¹ • c • x := by
          rw [← mul_smul, inv_mul_cancel₀ hc, one_smul]
        calc |x| = |c⁻¹ • c • x| := by rw [← hback]
          _ = |c|⁻¹ • |c • x| := by rw [abs_smul, abs_inv]
          _ ≤ |c|⁻¹ • (orderUnitGauge u (c • x) • u) :=
              smul_le_smul_of_nonneg_left (abs_le_gauge_smul hu hx') (inv_nonneg.mpr (abs_nonneg c))
          _ = (|c|⁻¹ * orderUnitGauge u (c • x)) • u := by rw [mul_smul]
      have hp' : orderUnitGauge u x ≤ |c|⁻¹ * orderUnitGauge u (c • x) :=
        (gauge_le_iff hu hx (mul_nonneg (inv_nonneg.mpr (abs_nonneg c)) hq)).2 habs
      have hmul := mul_le_mul_of_nonneg_left hp' (abs_nonneg c)
      rwa [← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.mpr hc), one_mul] at hmul

/-- The gauge is subadditive on the principal ideal. -/
theorem gauge_add {u x y : E} (hu : 0 ≤ u) (hx : x ∈ principalOrderIdeal u)
    (hy : y ∈ principalOrderIdeal u) :
    orderUnitGauge u (x + y) ≤ orderUnitGauge u x + orderUnitGauge u y := by
  have hxy : x + y ∈ principalOrderIdeal u := by
    obtain ⟨c, hc, hxc⟩ := hx
    obtain ⟨d, hd, hyd⟩ := hy
    refine ⟨c + d, add_nonneg hc hd, ?_⟩
    calc |x + y| ≤ |x| + |y| := abs_add_le x y
      _ ≤ c • u + d • u := add_le_add hxc hyd
      _ = (c + d) • u := by rw [add_smul]
  have habs : |x + y| ≤ (orderUnitGauge u x + orderUnitGauge u y) • u := by
    calc |x + y| ≤ |x| + |y| := abs_add_le x y
      _ ≤ orderUnitGauge u x • u + orderUnitGauge u y • u :=
          add_le_add (abs_le_gauge_smul hu hx) (abs_le_gauge_smul hu hy)
      _ = (orderUnitGauge u x + orderUnitGauge u y) • u := by rw [add_smul]
  exact (gauge_le_iff hu hxy (add_nonneg (gauge_nonneg hx) (gauge_nonneg hy))).2 habs

omit [NormedSpace ℝ E] [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- The absolute value of a supremum is dominated by the supremum of the absolute values. -/
private theorem abs_sup_le_sup_abs (x y : E) : |x ⊔ y| ≤ |x| ⊔ |y| := by
  refine sup_le ?_ ?_
  · exact sup_le_sup (le_abs_self x) (le_abs_self y)
  · rw [neg_sup]
    exact inf_le_left.trans ((neg_le_abs x).trans le_sup_left)

omit [NormedSpace ℝ E] [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- The absolute value of an infimum is dominated by the supremum of the absolute values. -/
private theorem abs_inf_le_sup_abs (x y : E) : |x ⊓ y| ≤ |x| ⊔ |y| := by
  rw [show x ⊓ y = -(-x ⊔ -y) by rw [← neg_inf, neg_neg], abs_neg]
  exact (abs_sup_le_sup_abs (-x) (-y)).trans (by simp [abs_neg])

omit [HasSolidNorm E] in
/-- Nonnegative scaling preserves a principal ideal. -/
theorem principalOrderIdeal_smul {u : E} {c : ℝ} {x : E} (hx : x ∈ principalOrderIdeal u) :
    c • x ∈ principalOrderIdeal u := by
  obtain ⟨d, hd, hxd⟩ := hx
  refine ⟨|c| * d, mul_nonneg (abs_nonneg c) hd, ?_⟩
  calc |c • x| = |c| • |x| := abs_smul c x
    _ ≤ |c| • (d • u) := smul_le_smul_of_nonneg_left hxd (abs_nonneg c)
    _ = (|c| * d) • u := by rw [mul_smul]

omit [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- Negation preserves a principal ideal. -/
theorem principalOrderIdeal_neg {u x : E} (hx : x ∈ principalOrderIdeal u) :
    -x ∈ principalOrderIdeal u := by
  obtain ⟨c, hc, hxc⟩ := hx
  exact ⟨c, hc, by simpa [abs_neg] using hxc⟩

omit [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- Addition preserves a principal ideal. -/
theorem principalOrderIdeal_add {u x y : E} (hx : x ∈ principalOrderIdeal u)
    (hy : y ∈ principalOrderIdeal u) : x + y ∈ principalOrderIdeal u := by
  obtain ⟨c, hc, hxc⟩ := hx
  obtain ⟨d, hd, hyd⟩ := hy
  refine ⟨c + d, add_nonneg hc hd, ?_⟩
  calc |x + y| ≤ |x| + |y| := abs_add_le x y
    _ ≤ c • u + d • u := add_le_add hxc hyd
    _ = (c + d) • u := by rw [add_smul]

omit [IsOrderedModule ℝ E] [HasSolidNorm E] in
/-- Subtraction preserves a principal ideal. -/
theorem principalOrderIdeal_sub {u x y : E} (hx : x ∈ principalOrderIdeal u)
    (hy : y ∈ principalOrderIdeal u) : x - y ∈ principalOrderIdeal u := by
  simpa [sub_eq_add_neg] using principalOrderIdeal_add hx (principalOrderIdeal_neg hy)

omit [HasSolidNorm E] in
/-- Natural scaling preserves a principal ideal. -/
theorem principalOrderIdeal_nsmul {u : E} {n : ℕ} {x : E} (hx : x ∈ principalOrderIdeal u) :
    n • x ∈ principalOrderIdeal u := by
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  exact principalOrderIdeal_smul hx

omit [HasSolidNorm E] in
/-- Integer scaling preserves a principal ideal. -/
theorem principalOrderIdeal_zsmul {u : E} {n : ℤ} {x : E} (hx : x ∈ principalOrderIdeal u) :
    n • x ∈ principalOrderIdeal u := by
  rw [← Int.cast_smul_eq_zsmul ℝ]
  exact principalOrderIdeal_smul hx

omit [IsOrderedModule ℝ E] [HasSolidNorm E] in
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

omit [IsOrderedModule ℝ E] [HasSolidNorm E] in
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

end OrderUnitGauge

end CKMA
