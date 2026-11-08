/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.OrthogonalPolynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Basic.ENNReal.Inv
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Support

/-!
# Moment existence, Jacobi recurrences and Carleman uniqueness

Finite Hankel positivity characterizes real moment existence, with once-shifted
positivity selecting half-line measures. Moment functionals express the equivalent
positivity on polynomial squares. Positive Jacobi edge coefficients determine a monic
orthogonal family and a Favard probability measure. Extended Carleman divergence
criteria give Hamburger and Stieltjes uniqueness, including zero moments.
The quadratic-form identity uses Mathlib's `Polynomial.lsum` and matrix positivity API.

Sources: GAPS 48.4, 48.32, 48.33 and 48.36.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Polynomial
open scoped BigOperators ENNReal Matrix

/-- The moment functional on real polynomials, defined by linear extension from monomials. -/
def momentFunctional (s : ℕ → ℝ) (p : ℝ[X]) : ℝ := p.sum (fun n c ↦ c * s n)

/-- A finite shifted Hankel matrix. -/
def momentHankelMatrix (s : ℕ → ℝ) (shift n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ s (i.val + j.val + shift)

/-- Positivity of every unshifted finite Hankel matrix. -/
def HasPositiveHankelMatrices (s : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, (momentHankelMatrix s 0 n).PosSemidef

/-- Hankel positivity makes every even moment nonnegative. -/
theorem HasPositiveHankelMatrices.nonneg_even {s : ℕ → ℝ}
    (hs : HasPositiveHankelMatrices s) (n : ℕ) : 0 ≤ s (2 * n) := by
  have h := (hs (n + 1)).diag_nonneg (i := Fin.last n)
  simpa [momentHankelMatrix, two_mul] using h

/-- A positive finite Borel measure represents the prescribed real moments. -/
def RepresentsRealMoments (μ : Measure ℝ) (s : ℕ → ℝ) : Prop :=
  HasFiniteMoments μ ∧ ∀ n : ℕ, ∫ x, x ^ n ∂μ = s n

/-- **48.32**: Hamburger's existence theorem; zero mass is allowed. -/
theorem hamburger_moment_iff (s : ℕ → ℝ) :
    HasPositiveHankelMatrices s ↔ ∃ μ : Measure ℝ, RepresentsRealMoments μ s := by
  sorry

/-- **48.33**: Stieltjes existence requires both unshifted and once-shifted Hankel positivity. -/
theorem stieltjes_moment_iff (s : ℕ → ℝ) :
    (HasPositiveHankelMatrices s ∧ ∀ n : ℕ, (momentHankelMatrix s 1 n).PosSemidef) ↔
      ∃ μ : Measure ℝ, RepresentsRealMoments μ s ∧ μ (Set.Ici (0 : ℝ))ᶜ = 0 := by
  sorry

/-- The moment of a finite monomial sum squared is the Hankel quadratic form of its
coefficient vector. -/
theorem momentFunctional_sum_monomial_mul_self (s : ℕ → ℝ) {n : ℕ} (x : Fin n → ℝ) :
    momentFunctional s ((∑ i, Polynomial.monomial i.val (x i)) *
      (∑ j, Polynomial.monomial j.val (x j))) =
      x ⬝ᵥ ((momentHankelMatrix s 0 n) *ᵥ x) := by
  let L : ℝ[X] →ₗ[ℝ] ℝ := Polynomial.lsum fun k ↦
    (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (s k)
  have hL : ∀ p, momentFunctional s p = L p := fun p ↦ rfl
  rw [hL, Finset.sum_mul_sum, map_sum]
  simp_rw [map_sum, Polynomial.monomial_mul_monomial]
  simp only [L, Polynomial.lsum_apply, Polynomial.sum_monomial_index,
    LinearMap.smulRight_apply, LinearMap.id_apply, smul_eq_mul, zero_mul]
  simp only [dotProduct, Matrix.mulVec, momentHankelMatrix, Nat.add_zero]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Hankel positivity is equivalently positivity of the moment functional on polynomial squares. -/
theorem positiveHankelMatrices_iff_squares (s : ℕ → ℝ) :
    HasPositiveHankelMatrices s ↔ ∀ p : ℝ[X], 0 ≤ momentFunctional s (p * p) := by
  constructor
  · intro hs p
    let n := p.natDegree + 1
    let x : Fin n → ℝ := fun i ↦ p.coeff i.val
    have hp : (∑ i : Fin n, Polynomial.monomial i.val (x i)) = p := by
      dsimp only [x]
      rw [Fin.sum_univ_eq_sum_range
        (fun i : ℕ ↦ Polynomial.monomial i (p.coeff i))]
      exact p.as_sum_range.symm
    have hh := (hs n).dotProduct_mulVec_nonneg x
    simp only [star_trivial] at hh
    rw [← momentFunctional_sum_monomial_mul_self s x, hp] at hh
    simpa only [star_trivial] using hh
  · intro h n
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · apply Matrix.isHermitian_iff_isSymm.mpr
      ext i j
      simp only [Matrix.transpose_apply, momentHankelMatrix, add_comm]
    · intro x
      simpa only [star_trivial, momentFunctional_sum_monomial_mul_self s x] using
        h (∑ i, Polynomial.monomial i.val (x i))

/-- The monic Jacobi recurrence with edge coefficients `a n` between sites `n` and `n+1`. -/
def jacobiMonicPolynomial (a b : ℕ → ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X - C (b 0)
  | n + 2 => (X - C (b (n + 1))) * jacobiMonicPolynomial a b (n + 1) -
      C (a n ^ 2) * jacobiMonicPolynomial a b n

/-- The Jacobi family starts with the constant polynomial one. -/
theorem jacobiMonicPolynomial_zero (a b : ℕ → ℝ) : jacobiMonicPolynomial a b 0 = 1 := by
  simp [jacobiMonicPolynomial]

/-- The second Jacobi polynomial is `X-b₀`. -/
theorem jacobiMonicPolynomial_one (a b : ℕ → ℝ) :
    jacobiMonicPolynomial a b 1 = X - C (b 0) := by
  simp [jacobiMonicPolynomial]

/-- The declared recurrence equation, including its normalization of the off-diagonal square. -/
theorem jacobiMonicPolynomial_recurrence (a b : ℕ → ℝ) (n : ℕ) :
    jacobiMonicPolynomial a b (n + 2) =
      (X - C (b (n + 1))) * jacobiMonicPolynomial a b (n + 1) -
        C (a n ^ 2) * jacobiMonicPolynomial a b n := by
  simp [jacobiMonicPolynomial]

/-- **48.4**: Favard's theorem in monic normalization, with a probability measure of infinite
  support. -/
theorem exists_favard_measure (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ HasFiniteMoments μ ∧ μ.support.Infinite ∧
      ∀ n m : ℕ, n ≠ m →
        ∫ x, (jacobiMonicPolynomial a b n).eval x * (jacobiMonicPolynomial a b m).eval x ∂μ = 0 :=
          by
  sorry

/-- Hamburger's Carleman divergence criterion. Extended powers give value `∞` at a zero moment,
so degenerate measures are included rather than excluded by real inverse conventions. -/
def HamburgerCarlemanCondition (s : ℕ → ℝ) : Prop :=
  (∑' n : ℕ, (ENNReal.ofReal (s (2 * (n + 1)))) ^ (-1 / (2 * (n + 1) : ℝ))) = ∞

/-- Stieltjes's corresponding Carleman condition using all positive moments. -/
def StieltjesCarlemanCondition (s : ℕ → ℝ) : Prop :=
  (∑' n : ℕ, (ENNReal.ofReal (s (n + 1))) ^ (-1 / (2 * (n + 1) : ℝ))) = ∞

/-- **48.36**: Hamburger Carleman divergence gives uniqueness among all real representing measures.
  -/
theorem measure_eq_of_hamburgerCarleman {s : ℕ → ℝ} (hs : HamburgerCarlemanCondition s)
    {μ ν : Measure ℝ} (hμ : RepresentsRealMoments μ s) (hν : RepresentsRealMoments ν s) : μ = ν :=
      by
  sorry

/-- Stieltjes Carleman divergence gives uniqueness among half-line representing measures. -/
theorem measure_eq_of_stieltjesCarleman {s : ℕ → ℝ} (hs : StieltjesCarlemanCondition s)
    {μ ν : Measure ℝ} (hμ : RepresentsRealMoments μ s) (hν : RepresentsRealMoments ν s)
    (hμ_support : μ (Set.Ici (0 : ℝ))ᶜ = 0) (hν_support : ν (Set.Ici (0 : ℝ))ᶜ = 0) : μ = ν := by
  sorry

end CKMA
