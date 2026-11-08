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

/-- Disjoint vectors in a Riesz space, using lattice absolute values. -/
def LatticeDisjoint (x y : E) : Prop := |x| ⊓ |y| = 0

omit [Module ℝ E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] in
/-- Lattice disjointness is symmetric. -/
theorem LatticeDisjoint.symm {x y : E} (h : LatticeDisjoint x y) : LatticeDisjoint y x := by
  simpa only [LatticeDisjoint, inf_comm] using h

/-- The disjoint complement of an arbitrary set of vectors. -/
def latticeDisjointComplement (s : Set E) : Set E := {x | ∀ y ∈ s, LatticeDisjoint x y}

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
  sorry

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

/-- **19.8**, Freudenthal approximation in the equivalent order-error form.
The Archimedean hypothesis is explicit, as required by the usual spectral theorem. -/
theorem freudenthal_approximation (ha : IsArchimedeanRieszSpace E)
    (hp : HasPrincipalBandProjections E) {u x : E} (hu : 0 ≤ u)
    (hx : x ∈ principalOrderIdeal u) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (a : Fin n → ℝ) (v : Fin n → E),
      (∀ i, IsLatticeComponent (v i) u) ∧
      (∀ i j, i ≠ j → LatticeDisjoint (v i) (v j)) ∧
      |x - ∑ i, a i • v i| ≤ ε • u := by
  sorry

/-- **19.20**, Riesz–Kantorovich: order-bounded operators into a Dedekind-complete vector
lattice are precisely differences of positive operators. -/
theorem orderBounded_iff_regular (hcomplete : IsDedekindCompleteRieszSpace F) (T : E →ₗ[ℝ] F) :
    IsOrderBoundedLinearMap T ↔ IsRegularLinearMap T := by
  constructor
  · intro hT
    sorry
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
  sorry

end CKMA
