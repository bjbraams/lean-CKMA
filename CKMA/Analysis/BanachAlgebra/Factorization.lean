/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Order.Directed
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Characters, norming boundaries, Tauberian density, and factorization

The character theorem concerns normalized linear functionals on complex Banach algebras;
continuity and commutativity are not assumed. Closed norming boundaries are subsets of a
compact Hausdorff carrier, including the empty carrier. The Tauberian statement uses actual
L1 equivalence classes and measure-preserving translations on the real line.

Cohen–Hewitt factorization is formulated for a continuous bilinear action of a nonunital
real or complex Banach algebra. Its bounded approximate identity is indexed by a directed set.
Sources: GAPS 20.19, 20.23, 20.41, and 20.47.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology MeasureTheory FourierTransform
open scoped FourierTransform

/-- **20.19**, Gleason–Kahane–Żelazko: a normalized complex linear functional nonzero on
units is multiplicative. Continuity and commutativity are not assumed. -/
theorem gleason_kahane_zelazko {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (F : A →ₗ[ℂ] ℂ) (hF : F 1 = 1)
    (hu : ∀ a : A, IsUnit a → F a ≠ 0) : ∀ a b : A, F (a * b) = F a * F b := by
  sorry

/-- A closed boundary for a uniform algebra, using the supremum convention that also
allows the zero algebra on the empty compact space. -/
def IsUniformAlgebraBoundary {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (A : Subalgebra ℂ C(K, ℂ)) (F : Set K) : Prop :=
  IsClosed F ∧ ∀ f : A, ‖f.1‖ = sSup ((fun x ↦ ‖f.1 x‖) '' F)

/-- **20.23**: a uniformly closed point-separating algebra has a smallest closed norming boundary.
The restriction isometry is expressed by the exact boundary-norm identity in the predicate. -/
theorem exists_shilov_boundary {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (A : Subalgebra ℂ C(K, ℂ)) (hA : IsClosed (A : Set C(K, ℂ)))
    (hsep : ∀ x y : K, x ≠ y → ∃ f : A, f.1 x ≠ f.1 y) :
    ∃ F : Set K, IsUniformAlgebraBoundary A F ∧
      ∀ G : Set K, IsUniformAlgebraBoundary A G → F ⊆ G := by
  sorry

/-- Translation of an L1 equivalence class on the real line, constructed by the actual
measure-preserving composition map. -/
def lpTranslate (f : Lp ℂ 1 (volume : Measure ℝ)) (t : ℝ) : Lp ℂ 1 (volume : Measure ℝ) :=
  Lp.compMeasurePreserving (E := ℂ) (p := 1) (fun x : ℝ ↦ x + t)
    (measurePreserving_add_right (volume : Measure ℝ) t) f

/-- **20.41**, Wiener Tauberian density on the real line. The Fourier transform is the L1
integral of an a.e. representative; the translation span is a closed submodule of L1. -/
theorem wiener_tauberian_real (f : Lp ℂ 1 (volume : Measure ℝ)) :
    (∀ ξ : ℝ, 𝓕 (fun x : ℝ ↦ f x) ξ ≠ 0) ↔
      (Submodule.span ℂ (Set.range (lpTranslate f))).topologicalClosure = ⊤ := by
  sorry

/-- A bounded left approximate identity along `atTop` on a preorder. -/
def IsBoundedLeftApproximateIdentity {ι A : Type*} [Preorder ι] [NonUnitalNormedRing A]
    (e : ι → A) : Prop :=
  (∃ M : ℝ, ∀ i, ‖e i‖ ≤ M) ∧ ∀ a : A, Tendsto (fun i ↦ e i * a) atTop (𝓝 a)

/-- **20.47**, Cohen–Hewitt factorization for a bounded directed approximate identity
acting strongly as the identity on a real or complex Banach module. The action is a continuous
bilinear map, which supports genuinely nonunital algebras without requiring a unital Module
instance. -/
theorem cohen_hewitt_factorization {𝕜 ι A X : Type*} [RCLike 𝕜] [Preorder ι]
    [IsDirected ι (· ≤ ·)] [NonUnitalNormedRing A]
    [NormedSpace 𝕜 A] [CompleteSpace A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    (act : A →L[𝕜] X →L[𝕜] X)
    (hassoc : ∀ a b x, act (a * b) x = act a (act b x))
    (e : ι → A) (he : IsBoundedLeftApproximateIdentity e)
    (hstrong : ∀ x, Tendsto (fun i ↦ act (e i) x) atTop (𝓝 x)) :
    ∀ x : X, ∃ a : A, ∃ y : X, x = act a y := by
  sorry

end CKMA
