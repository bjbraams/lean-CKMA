/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Several-variable extension, preparation and approximation

Separate holomorphy implies joint holomorphy in finite-dimensional complex space.
Hartogs extension fills compact holes in dimension at least two. Distinguished
polynomials with analytic coefficient germs give Weierstrass preparation and division,
with uniqueness of the resulting germs. Polynomially convex compact sets admit
Oka–Weil approximation by multivariate polynomials.

Sources: GAPS 45.1, 45.5, 45.7, 45.8 and 45.20.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped BigOperators

/-- Separate holomorphy on an open coordinate domain; no continuity assumption is included. -/
def IsSeparatelyHolomorphicOn {n : ℕ} (f : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ)) : Prop :=
  ∀ z ∈ Ω, ∀ j : Fin n, DifferentiableAt ℂ (fun w ↦ f (Function.update z j w)) (z j)

/-- **45.1**: Hartogs separate analyticity, including the vacuous zero-dimensional case. -/
theorem differentiableOn_of_separatelyHolomorphic {n : ℕ} {Ω : Set (Fin n → ℂ)}
    (hΩ : IsOpen Ω) {f : (Fin n → ℂ) → ℂ} (hf : IsSeparatelyHolomorphicOn f Ω) :
    DifferentiableOn ℂ f Ω := by
  sorry

/-- **45.5**: extension across a compact hole in dimension at least two.
Uniqueness is equality on the domain, not equality of arbitrary functions outside it. -/
theorem hartogs_extension {n : ℕ} (hn : 2 ≤ n) {Ω K : Set (Fin n → ℂ)}
    (hΩ : IsOpen Ω) (hΩconn : IsPreconnected Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hcomp : IsConnected (Ω \ K))
    {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (Ω \ K)) :
    ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F Ω ∧ Set.EqOn F f (Ω \ K) ∧
      ∀ G : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G Ω → Set.EqOn G f (Ω \ K) → Set.EqOn G F Ω := by
  sorry

/-- Holomorphic coefficients of a distinguished polynomial, all vanishing at the base origin. -/
def IsDistinguishedCoefficientFamily {n d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ) : Prop :=
  ∀ j, AnalyticAt ℂ (a j) 0 ∧ a j 0 = 0

/-- A monic Weierstrass polynomial in the final coordinate. -/
def distinguishedPolynomial {n d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ)
    (z : (Fin n → ℂ) × ℂ) : ℂ := z.2 ^ d + ∑ j, a j z.1 * z.2 ^ j.val

/-- A polynomial remainder of degree strictly less than `d` in the last coordinate. -/
def distinguishedRemainder {n d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ)
    (z : (Fin n → ℂ) × ℂ) : ℂ := ∑ j, a j z.1 * z.2 ^ j.val

/-- The analytic factorization properties of Weierstrass preparation, as germ identities. -/
def IsWeierstrassPreparation {n d : ℕ} (f u : ((Fin n → ℂ) × ℂ) → ℂ)
    (a : Fin d → (Fin n → ℂ) → ℂ) : Prop :=
  AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧ IsDistinguishedCoefficientFamily a ∧
    ∀ᶠ z in 𝓝 (0 : (Fin n → ℂ) × ℂ), f z = u z * distinguishedPolynomial a z

/-- **45.7**: convergent complex Weierstrass preparation, unique as analytic germs. -/
theorem weierstrass_preparation {n d : ℕ} {f : ((Fin n → ℂ) × ℂ) → ℂ}
    (hf : AnalyticAt ℂ f 0) (horder : analyticOrderAt (fun w ↦ f (0, w)) 0 = (d : ℕ∞)) :
    ∃ (u : ((Fin n → ℂ) × ℂ) → ℂ) (a : Fin d → (Fin n → ℂ) → ℂ),
      IsWeierstrassPreparation f u a ∧
      ∀ (v : ((Fin n → ℂ) × ℂ) → ℂ) (b : Fin d → (Fin n → ℂ) → ℂ),
        IsWeierstrassPreparation f v b →
          u =ᶠ[𝓝 (0 : (Fin n → ℂ) × ℂ)] v ∧ ∀ j, a j =ᶠ[𝓝 (0 : Fin n → ℂ)] b j := by
  sorry

/-- Germ data for division by a distinguished polynomial. -/
def IsWeierstrassDivision {n d : ℕ} (g q : ((Fin n → ℂ) × ℂ) → ℂ)
    (a r : Fin d → (Fin n → ℂ) → ℂ) : Prop :=
  AnalyticAt ℂ q 0 ∧ (∀ j, AnalyticAt ℂ (r j) 0) ∧
    ∀ᶠ z in 𝓝 (0 : (Fin n → ℂ) × ℂ),
      g z = q z * distinguishedPolynomial a z + distinguishedRemainder r z

/-- **45.8**: convergent Weierstrass division, with a unique quotient and finite remainder germs. -/
theorem weierstrass_division {n d : ℕ} (a : Fin d → (Fin n → ℂ) → ℂ)
    (ha : IsDistinguishedCoefficientFamily a) {g : ((Fin n → ℂ) × ℂ) → ℂ}
    (hg : AnalyticAt ℂ g 0) :
    ∃ (q : ((Fin n → ℂ) × ℂ) → ℂ) (r : Fin d → (Fin n → ℂ) → ℂ),
      IsWeierstrassDivision g q a r ∧
      ∀ (q' : ((Fin n → ℂ) × ℂ) → ℂ) (r' : Fin d → (Fin n → ℂ) → ℂ),
        IsWeierstrassDivision g q' a r' →
          q =ᶠ[𝓝 (0 : (Fin n → ℂ) × ℂ)] q' ∧ ∀ j, r j =ᶠ[𝓝 (0 : Fin n → ℂ)] r' j := by
  sorry

/-- The polynomial hull in affine complex space, using actual multivariate polynomial evaluations.
  -/
def complexPolynomialHull {n : ℕ} (K : Set (Fin n → ℂ)) : Set (Fin n → ℂ) :=
  {z | ∀ p : MvPolynomial (Fin n) ℂ,
    ‖MvPolynomial.eval z p‖ ≤ sSup ((fun w ↦ ‖MvPolynomial.eval w p‖) '' K)}

/-- **45.20**, polynomial Oka–Weil: approximation on polynomially convex compact sets in `ℂⁿ`.
The general Stein-manifold version remains. -/
theorem polynomial_oka_weil {n : ℕ} {K U : Set (Fin n → ℂ)} (hK : IsCompact K)
    (hconvex : complexPolynomialHull K = K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin n) ℂ, ∀ z ∈ K, ‖f z - MvPolynomial.eval z p‖ < ε := by
  sorry

end CKMA
