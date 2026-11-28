/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Uniform polynomial approximation on `[-1, 1]`: basic definitions

This file sets up the uniform approximation of continuous real functions on `[-1, 1]` by
polynomials of bounded degree, and the coefficient parametrization of such polynomials.

The interval is fixed to `[-1, 1]`. Results on a compact interval `[a, b]` with `a < b` follow by
the affine change of variables `x ↦ (2x - a - b) / (b - a)`, which preserves the degree of a
polynomial and the supremum norm of a residual.

## Main definitions

* `CKMA.ApproximationIntervalMap`: continuous real functions on `[-1, 1]`.
* `CKMA.polynomialOnApproximationInterval`: restriction of a polynomial to `[-1, 1]`.
* `CKMA.bestPolynomialError`: uniform approximation error at degree at most `n`.
* `CKMA.IsBestPolynomialApproximation`: best uniform polynomial approximant of degree at most `n`.
* `CKMA.HasPolynomialAlternation`: alternation of the uniform residual at `n + 2` nodes.
* `CKMA.polynomialOfCoeffs`: the polynomial of degree at most `n` with given coefficients.

## Main results

* `CKMA.coeff_polynomialOfCoeffs`, `CKMA.natDegree_polynomialOfCoeffs_le`,
  `CKMA.polynomialOfCoeffs_of_natDegree_le`, `CKMA.polynomialOfCoeffs_eq_zero_iff`: the
  coefficient parametrization is a bijection onto polynomials of degree at most `n`.
* `CKMA.polynomialOnApproximationInterval_apply`, `CKMA.bestPolynomialError_def`,
  `CKMA.isBestPolynomialApproximation_iff`, `CKMA.hasPolynomialAlternation_iff`,
  `CKMA.polynomialOfCoeffs_def`: defining lemmas.
* `CKMA.eq_zero_of_polynomialOnApproximationInterval_eq_zero`: a polynomial of degree at most
  `n` vanishing on `[-1, 1]` is zero.
-/

public section

noncomputable section

namespace CKMA

open Polynomial

/-- Real continuous functions on the standard nondegenerate compact interval. -/
abbrev ApproximationIntervalMap := C(Set.Icc (-1 : ℝ) 1, ℝ)

/-- A polynomial restricted to the standard approximation interval. -/
@[expose]
def polynomialOnApproximationInterval (p : ℝ[X]) : ApproximationIntervalMap :=
  ⟨fun x ↦ p.eval x.1, p.continuous.comp continuous_subtype_val⟩

/-- Best uniform polynomial approximation error at degree at most `n`. -/
@[expose]
def bestPolynomialError (f : ApproximationIntervalMap) (n : ℕ) : ℝ :=
  sInf {r | ∃ p : ℝ[X], p.natDegree ≤ n ∧ r = ‖f - polynomialOnApproximationInterval p‖}

/-- A best uniform polynomial approximant, with the degree bound included. -/
@[expose]
def IsBestPolynomialApproximation (f : ApproximationIntervalMap) (n : ℕ) (p : ℝ[X]) : Prop :=
  p.natDegree ≤ n ∧ ∀ q : ℝ[X], q.natDegree ≤ n →
    ‖f - polynomialOnApproximationInterval p‖ ≤ ‖f - polynomialOnApproximationInterval q‖

/-- Alternation of the uniform residual at `n+2` strictly increasing points. -/
@[expose]
def HasPolynomialAlternation (f : ApproximationIntervalMap) (p : ℝ[X]) (n : ℕ) : Prop :=
  ∃ x : Fin (n + 2) → Set.Icc (-1 : ℝ) 1,
    StrictMono (fun i ↦ (x i).1) ∧ ∃ σ : ℝ, |σ| = 1 ∧ ∀ i,
      f (x i) - p.eval (x i).1 = σ * (-1) ^ i.val * ‖f - polynomialOnApproximationInterval p‖

/-- The polynomial of degree at most `n` with the supplied coefficients. -/
@[expose]
def polynomialOfCoeffs (n : ℕ) (c : Fin (n + 1) → ℝ) : ℝ[X] :=
  ∑ i, monomial i.val (c i)

/-- Evaluation of a restricted polynomial. -/
@[simp]
lemma polynomialOnApproximationInterval_apply (p : ℝ[X]) (x : Set.Icc (-1 : ℝ) 1) :
    polynomialOnApproximationInterval p x = p.eval x.1 :=
  rfl

/-- The best error is the infimum of the residual norms over polynomials of degree at most
`n`. -/
lemma bestPolynomialError_def (f : ApproximationIntervalMap) (n : ℕ) :
    bestPolynomialError f n =
      sInf {r | ∃ p : ℝ[X], p.natDegree ≤ n ∧ r = ‖f - polynomialOnApproximationInterval p‖} :=
  rfl

/-- Characterization of a best uniform polynomial approximant. -/
lemma isBestPolynomialApproximation_iff {f : ApproximationIntervalMap} {n : ℕ} {p : ℝ[X]} :
    IsBestPolynomialApproximation f n p ↔ p.natDegree ≤ n ∧ ∀ q : ℝ[X], q.natDegree ≤ n →
      ‖f - polynomialOnApproximationInterval p‖ ≤ ‖f - polynomialOnApproximationInterval q‖ :=
  Iff.rfl

/-- Characterization of alternation of the uniform residual. -/
lemma hasPolynomialAlternation_iff {f : ApproximationIntervalMap} {p : ℝ[X]} {n : ℕ} :
    HasPolynomialAlternation f p n ↔ ∃ x : Fin (n + 2) → Set.Icc (-1 : ℝ) 1,
      StrictMono (fun i ↦ (x i).1) ∧ ∃ σ : ℝ, |σ| = 1 ∧ ∀ i,
        f (x i) - p.eval (x i).1 = σ * (-1) ^ i.val * ‖f - polynomialOnApproximationInterval p‖ :=
  Iff.rfl

/-- The coefficient polynomial is the sum of its monomials. -/
lemma polynomialOfCoeffs_def (n : ℕ) (c : Fin (n + 1) → ℝ) :
    polynomialOfCoeffs n c = ∑ i, monomial i.val (c i) :=
  rfl

/-- Each stored coefficient is recovered from `polynomialOfCoeffs`. -/
lemma coeff_polynomialOfCoeffs (n : ℕ) (c : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (polynomialOfCoeffs n c).coeff i.val = c i := by
  classical
  simp only [polynomialOfCoeffs, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
    simp [hval]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- A coefficient polynomial has degree at most `n`. -/
lemma natDegree_polynomialOfCoeffs_le (n : ℕ) (c : Fin (n + 1) → ℝ) :
    (polynomialOfCoeffs n c).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro m hm
  simp only [polynomialOfCoeffs, finsetSum_coeff, coeff_monomial]
  refine Finset.sum_eq_zero ?_
  intro i _
  have hine : i.val ≠ m := ne_of_lt (lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) hm)
  simp [hine]

/-- Every polynomial of degree at most `n` arises from its coefficients. -/
lemma polynomialOfCoeffs_of_natDegree_le (n : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ n) :
    polynomialOfCoeffs n (fun i => p.coeff i.val) = p := by
  conv_rhs => rw [p.as_sum_range' (n + 1) (Nat.lt_succ_of_le hp)]
  unfold polynomialOfCoeffs
  exact Fin.sum_univ_eq_sum_range (fun i => monomial i (p.coeff i)) (n + 1)

/-- Vanishing of the coefficient vector is equivalent to the zero polynomial. -/
lemma polynomialOfCoeffs_eq_zero_iff (n : ℕ) (c : Fin (n + 1) → ℝ) :
    polynomialOfCoeffs n c = 0 ↔ c = 0 := by
  constructor
  · intro h
    ext i
    rw [← coeff_polynomialOfCoeffs n c i, h]
    simp
  · intro h
    unfold polynomialOfCoeffs
    simp [h, monomial_zero_right]

/-- Distinct sample points in `(-1,1)`, one for each coefficient. -/
private def coefficientTestPoint (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  (i.val : ℝ) / (n + 1)

/-- The sample points lie in `[-1,1]`. -/
private lemma coefficientTestPoint_mem (n : ℕ) (i : Fin (n + 1)) :
    coefficientTestPoint n i ∈ Set.Icc (-1 : ℝ) 1 := by
  unfold coefficientTestPoint
  have hden : (0 : ℝ) < n + 1 := by positivity
  have hnonneg : 0 ≤ (i.val : ℝ) / (n + 1) := div_nonneg (Nat.cast_nonneg _) hden.le
  have hle : (i.val : ℝ) / (n + 1) ≤ 1 := by
    rw [div_le_one hden]
    have hi : (i.val : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    linarith
  exact ⟨le_trans (by norm_num) hnonneg, hle⟩

/-- Distinct indices give distinct sample points. -/
private lemma coefficientTestPoint_injective (n : ℕ) :
    Function.Injective (coefficientTestPoint n) := by
  intro i j hij
  unfold coefficientTestPoint at hij
  have hden : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hval : (i.val : ℝ) = j.val := (div_left_inj₀ hden).mp hij
  exact Fin.ext (Nat.cast_injective hval)

/-- A polynomial of degree at most `n` that vanishes on `[-1,1]` is zero. -/
lemma eq_zero_of_polynomialOnApproximationInterval_eq_zero {n : ℕ} (p : ℝ[X])
    (hp : p.natDegree ≤ n) (h : polynomialOnApproximationInterval p = 0) : p = 0 := by
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero p (coefficientTestPoint_injective n)
  · intro i
    have hx := coefficientTestPoint_mem n i
    have happ : polynomialOnApproximationInterval p ⟨coefficientTestPoint n i, hx⟩ = 0 := by
      simp [h]
    simpa [polynomialOnApproximationInterval, IsRoot] using happ
  · simpa using Nat.lt_succ_of_le hp


end CKMA
