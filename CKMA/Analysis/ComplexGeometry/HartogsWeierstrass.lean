/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
public import TauCeti.Analysis.Complex.PolynomialHull.Basic
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
import TauCeti.Analysis.Complex.Weierstrass
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Weierstrass

/-!
# Several-variable extension, preparation and approximation

Separate holomorphy implies joint holomorphy in finite-dimensional complex space.
Hartogs extension fills compact holes in dimension at least two. Distinguished
polynomials with analytic coefficient germs give Weierstrass preparation and division at any base
point `(x₀, w₀)` of `E × ℂ`, with `E` a finite-dimensional complex normed space, together with
uniqueness of the resulting germs. Polynomially convex compact sets admit Oka–Weil approximation
by multivariate polynomials.

The Weierstrass proofs use TauCeti's local analytic existence theorems
`AnalyticAt.exists_weierstrassPreparation` and `AnalyticAt.exists_weierstrassDivision_monicOfCoeff`
and the germ uniqueness theorems from its holomorphic structure sheaf. Distinguished polynomials
are TauCeti's `TauCeti.Polynomial.monicOfCoeff`, and polynomial hulls and polynomial convexity are
TauCeti's `TauCeti.polynomialHull` and `TauCeti.IsPolynomiallyConvex`.

Sources: GAPS 45.1, 45.5, 45.7, 45.8 and 45.20.

## Main definitions

* `CKMA.IsSeparatelyHolomorphicOn`: separate holomorphy in each coordinate.
* `CKMA.IsDistinguishedCoefficientFamily`, `CKMA.distinguishedPolynomial`,
  `CKMA.distinguishedRemainder`: Weierstrass polynomial and remainder data at a base point.
* `CKMA.IsWeierstrassPreparation`, `CKMA.IsWeierstrassDivision`: germ predicates for Weierstrass
  preparation and division.

## Main results

* `CKMA.IsSeparatelyHolomorphicOn.differentiableOn`: Hartogs's theorem on separate analyticity.
* `CKMA.hartogs_extension`: Hartogs's extension theorem across compact holes for `n ≥ 2`.
* `CKMA.weierstrass_preparation`: Weierstrass preparation theorem.
* `CKMA.weierstrass_division`: Weierstrass division theorem.
* `CKMA.polynomial_oka_weil`: Oka–Weil polynomial approximation theorem.
-/

public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped BigOperators

/-- Separate holomorphy on a coordinate domain: holomorphy in each coordinate with the others
fixed. No continuity or local boundedness assumption is included. -/
@[expose]
def IsSeparatelyHolomorphicOn {ι : Type*} [DecidableEq ι] (f : (ι → ℂ) → ℂ)
    (Ω : Set (ι → ℂ)) : Prop :=
  ∀ z ∈ Ω, ∀ j : ι, DifferentiableAt ℂ (fun w ↦ f (Function.update z j w)) (z j)

/-- Characterization of `IsSeparatelyHolomorphicOn` by holomorphy in each coordinate. -/
theorem isSeparatelyHolomorphicOn_iff {ι : Type*} [DecidableEq ι] {f : (ι → ℂ) → ℂ}
    {Ω : Set (ι → ℂ)} :
    IsSeparatelyHolomorphicOn f Ω ↔
      ∀ z ∈ Ω, ∀ j : ι, DifferentiableAt ℂ (fun w ↦ f (Function.update z j w)) (z j) :=
  Iff.rfl

/-- **45.1**: Hartogs's theorem on separate analyticity: a separately holomorphic function on an
open subset of `ℂ^ι`, `ι` finite, is holomorphic. The case of empty `ι` is included. -/
theorem IsSeparatelyHolomorphicOn.differentiableOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : Set (ι → ℂ)} {f : (ι → ℂ) → ℂ} (hf : IsSeparatelyHolomorphicOn f Ω) (hΩ : IsOpen Ω) :
    DifferentiableOn ℂ f Ω := by
  sorry

/-- **45.5**: extension across a compact hole in dimension at least two.
Uniqueness is equality on the domain, not equality of arbitrary functions outside it.
Connectedness of `Ω` follows from that of `Ω \ K`, since no component of `Ω` lies in `K`. -/
theorem hartogs_extension {n : ℕ} (hn : 2 ≤ n) {Ω K : Set (Fin n → ℂ)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hcomp : IsConnected (Ω \ K))
    {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (Ω \ K)) :
    ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F Ω ∧ Set.EqOn F f (Ω \ K) ∧
      ∀ G : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G Ω → Set.EqOn G f (Ω \ K) → Set.EqOn G F Ω := by
  sorry

section Weierstrass

variable {E : Type} {d : ℕ}

/-- The Weierstrass polynomial `(w - w₀)^d + ∑ⱼ aⱼ(x) (w - w₀)^j` in the last coordinate, the
evaluation of TauCeti's `TauCeti.Polynomial.monicOfCoeff`. -/
@[expose]
def distinguishedPolynomial (a : Fin d → E → ℂ) (w₀ : ℂ) (z : E × ℂ) : ℂ :=
  (TauCeti.Polynomial.monicOfCoeff fun j ↦ a j z.1).eval (z.2 - w₀)

/-- Expanded form of `distinguishedPolynomial`. -/
theorem distinguishedPolynomial_apply (a : Fin d → E → ℂ) (w₀ : ℂ) (z : E × ℂ) :
    distinguishedPolynomial a w₀ z = (z.2 - w₀) ^ d + ∑ j, a j z.1 * (z.2 - w₀) ^ j.val :=
  TauCeti.Polynomial.eval_monicOfCoeff _ _

/-- A polynomial remainder `∑ⱼ rⱼ(x) (w - w₀)^j` of degree less than `d` in the last
coordinate. -/
@[expose]
def distinguishedRemainder (r : Fin d → E → ℂ) (w₀ : ℂ) (z : E × ℂ) : ℂ :=
  ∑ j, r j z.1 * (z.2 - w₀) ^ j.val

/-- Unfolding lemma for `distinguishedRemainder`. -/
theorem distinguishedRemainder_apply (r : Fin d → E → ℂ) (w₀ : ℂ) (z : E × ℂ) :
    distinguishedRemainder r w₀ z = ∑ j, r j z.1 * (z.2 - w₀) ^ j.val :=
  rfl

variable [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Coefficients of a distinguished polynomial at `x₀`: analytic at `x₀` and vanishing there. -/
@[expose]
def IsDistinguishedCoefficientFamily (a : Fin d → E → ℂ) (x₀ : E) : Prop :=
  ∀ j, AnalyticAt ℂ (a j) x₀ ∧ a j x₀ = 0

/-- Characterization of `IsDistinguishedCoefficientFamily`. -/
theorem isDistinguishedCoefficientFamily_iff {a : Fin d → E → ℂ} {x₀ : E} :
    IsDistinguishedCoefficientFamily a x₀ ↔ ∀ j, AnalyticAt ℂ (a j) x₀ ∧ a j x₀ = 0 :=
  Iff.rfl

/-- The analytic factorization properties of Weierstrass preparation at `(x₀, w₀)`, as germ
identities. -/
@[expose]
def IsWeierstrassPreparation (f u : E × ℂ → ℂ) (a : Fin d → E → ℂ) (x₀ : E) (w₀ : ℂ) : Prop :=
  AnalyticAt ℂ u (x₀, w₀) ∧ u (x₀, w₀) ≠ 0 ∧ IsDistinguishedCoefficientFamily a x₀ ∧
    ∀ᶠ z in 𝓝 (x₀, w₀), f z = u z * distinguishedPolynomial a w₀ z

/-- Characterization of `IsWeierstrassPreparation`. -/
theorem isWeierstrassPreparation_iff {f u : E × ℂ → ℂ} {a : Fin d → E → ℂ} {x₀ : E} {w₀ : ℂ} :
    IsWeierstrassPreparation f u a x₀ w₀ ↔
      AnalyticAt ℂ u (x₀, w₀) ∧ u (x₀, w₀) ≠ 0 ∧ IsDistinguishedCoefficientFamily a x₀ ∧
        ∀ᶠ z in 𝓝 (x₀, w₀), f z = u z * distinguishedPolynomial a w₀ z :=
  Iff.rfl

/-- **45.7**: convergent complex Weierstrass preparation at `(x₀, w₀)`, unique as analytic germs.
-/
theorem weierstrass_preparation [FiniteDimensional ℂ E] {f : E × ℂ → ℂ} {x₀ : E} {w₀ : ℂ}
    (hf : AnalyticAt ℂ f (x₀, w₀)) (horder : analyticOrderAt (fun w ↦ f (x₀, w)) w₀ = (d : ℕ∞)) :
    ∃ (u : E × ℂ → ℂ) (a : Fin d → E → ℂ),
      IsWeierstrassPreparation f u a x₀ w₀ ∧
      ∀ (v : E × ℂ → ℂ) (b : Fin d → E → ℂ),
        IsWeierstrassPreparation f v b x₀ w₀ →
          u =ᶠ[𝓝 (x₀, w₀)] v ∧ ∀ j, a j =ᶠ[𝓝 x₀] b j := by
  obtain ⟨a, u, ha, ha₀, hu, hu₀, hprep⟩ := hf.exists_weierstrassPreparation horder
  have hfu : f =ᶠ[𝓝 (x₀, w₀)] fun z ↦ u z * distinguishedPolynomial a w₀ z := by
    simpa only [distinguishedPolynomial, mul_comm] using hprep
  refine ⟨u, a, ⟨hu, hu₀, fun j ↦ ⟨ha j, ha₀ j⟩, hfu⟩, ?_⟩
  rintro v b ⟨hv, hv₀, hb, hfv⟩
  have h := TauCeti.eventuallyEq_of_weierstrassPreparation
    ha ha₀ hu hu₀ (fun j ↦ (hb j).1) (fun j ↦ (hb j).2) hv hv₀
    (by simpa only [distinguishedPolynomial, mul_comm] using hfu.symm.trans hfv)
  exact ⟨h.2, h.1⟩

/-- Germ data at `(x₀, w₀)` for division by a distinguished polynomial. -/
@[expose]
def IsWeierstrassDivision (g q : E × ℂ → ℂ) (a r : Fin d → E → ℂ) (x₀ : E) (w₀ : ℂ) : Prop :=
  AnalyticAt ℂ q (x₀, w₀) ∧ (∀ j, AnalyticAt ℂ (r j) x₀) ∧
    ∀ᶠ z in 𝓝 (x₀, w₀),
      g z = q z * distinguishedPolynomial a w₀ z + distinguishedRemainder r w₀ z

/-- Characterization of `IsWeierstrassDivision`. -/
theorem isWeierstrassDivision_iff {g q : E × ℂ → ℂ} {a r : Fin d → E → ℂ} {x₀ : E} {w₀ : ℂ} :
    IsWeierstrassDivision g q a r x₀ w₀ ↔
      AnalyticAt ℂ q (x₀, w₀) ∧ (∀ j, AnalyticAt ℂ (r j) x₀) ∧
        ∀ᶠ z in 𝓝 (x₀, w₀),
          g z = q z * distinguishedPolynomial a w₀ z + distinguishedRemainder r w₀ z :=
  Iff.rfl

/-- **45.8**: convergent Weierstrass division at `(x₀, w₀)`, with a unique quotient and finite
remainder germs. -/
theorem weierstrass_division [FiniteDimensional ℂ E] {x₀ : E} {w₀ : ℂ} (a : Fin d → E → ℂ)
    (ha : IsDistinguishedCoefficientFamily a x₀) {g : E × ℂ → ℂ}
    (hg : AnalyticAt ℂ g (x₀, w₀)) :
    ∃ (q : E × ℂ → ℂ) (r : Fin d → E → ℂ),
      IsWeierstrassDivision g q a r x₀ w₀ ∧
      ∀ (q' : E × ℂ → ℂ) (r' : Fin d → E → ℂ),
        IsWeierstrassDivision g q' a r' x₀ w₀ →
          q =ᶠ[𝓝 (x₀, w₀)] q' ∧ ∀ j, r j =ᶠ[𝓝 x₀] r' j := by
  obtain ⟨q, r, hq, hr, hdiv⟩ :=
    hg.exists_weierstrassDivision_monicOfCoeff (fun j ↦ (ha j).1) (fun j ↦ (ha j).2)
  have hgq : g =ᶠ[𝓝 (x₀, w₀)]
      fun z ↦ q z * distinguishedPolynomial a w₀ z + distinguishedRemainder r w₀ z := by
    simpa only [distinguishedPolynomial, distinguishedRemainder, mul_comm] using hdiv
  refine ⟨q, r, ⟨hq, hr, hgq⟩, ?_⟩
  rintro q' r' ⟨hq', hr', hgq'⟩
  refine TauCeti.eventuallyEq_of_weierstrassDivision
    (fun j ↦ (ha j).1) (fun j ↦ (ha j).2) hq hr hq' hr' ?_
  simpa only [distinguishedPolynomial, distinguishedRemainder, mul_comm] using hgq.symm.trans hgq'

end Weierstrass

/-- **45.20**, polynomial Oka–Weil: a function holomorphic near a polynomially convex compact set
`K ⊆ ℂ^ι`, `ι` finite, is a uniform limit on `K` of polynomials. Polynomial convexity is TauCeti's
`TauCeti.IsPolynomiallyConvex`. -/
theorem polynomial_oka_weil {ι : Type*} [Fintype ι] {K U : Set (ι → ℂ)} (hK : IsCompact K)
    (hconvex : TauCeti.IsPolynomiallyConvex K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : (ι → ℂ) → ℂ} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial ι ℂ, ∀ z ∈ K, ‖f z - MvPolynomial.eval z p‖ < ε := by
  sorry

end CKMA
