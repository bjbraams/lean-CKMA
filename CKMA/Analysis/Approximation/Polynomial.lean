/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Nat.Find
public import Mathlib.Tactic

/-!
# Uniform polynomial and rational approximation

Continuous real functions on `[-1,1]` have best approximation errors measured in the
supremum norm. The interfaces cover existence and uniqueness of best polynomials,
Chebyshev alternation including zero residual, sharp Markov derivative bounds,
Müntz–Szász density, and polynomial and rational approximation rates for the cusp `|x|`.
Rational approximants have denominators without zeros on the interval.

Sources: GAPS 47.6, 47.13, 47.24 and 47.40.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Metric Topology Polynomial
open scoped BigOperators

/-- Real continuous functions on the standard nondegenerate compact interval. -/
abbrev ApproximationIntervalMap := C(Set.Icc (-1 : ℝ) 1, ℝ)

/-- A polynomial restricted to the standard approximation interval. -/
def polynomialOnApproximationInterval (p : ℝ[X]) : ApproximationIntervalMap :=
  ⟨fun x ↦ p.eval x.1, p.continuous.comp continuous_subtype_val⟩

/-- Best uniform polynomial approximation error at degree at most `n`. -/
def bestPolynomialError (f : ApproximationIntervalMap) (n : ℕ) : ℝ :=
  sInf {r | ∃ p : ℝ[X], p.natDegree ≤ n ∧ r = ‖f - polynomialOnApproximationInterval p‖}

/-- A best uniform polynomial approximant, with the degree bound included. -/
def IsBestPolynomialApproximation (f : ApproximationIntervalMap) (n : ℕ) (p : ℝ[X]) : Prop :=
  p.natDegree ≤ n ∧ ∀ q : ℝ[X], q.natDegree ≤ n →
    ‖f - polynomialOnApproximationInterval p‖ ≤ ‖f - polynomialOnApproximationInterval q‖

/-- Alternation of the uniform residual at `n+2` strictly increasing points. -/
def HasPolynomialAlternation (f : ApproximationIntervalMap) (p : ℝ[X]) (n : ℕ) : Prop :=
  ∃ x : Fin (n + 2) → Set.Icc (-1 : ℝ) 1,
    StrictMono (fun i ↦ (x i).1) ∧ ∃ σ : ℝ, |σ| = 1 ∧ ∀ i,
      f (x i) - p.eval (x i).1 = σ * (-1) ^ i.val * ‖f - polynomialOnApproximationInterval p‖

/-- The polynomial of degree at most `n` with the supplied coefficients. -/
def polynomialOfCoeffs (n : ℕ) (c : Fin (n + 1) → ℝ) : ℝ[X] :=
  ∑ i, monomial i.val (c i)

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
def coefficientTestPoint (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  (i.val : ℝ) / (n + 1)

/-- The sample points lie in `[-1,1]`. -/
lemma coefficientTestPoint_mem (n : ℕ) (i : Fin (n + 1)) :
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
lemma coefficientTestPoint_injective (n : ℕ) :
    Function.Injective (coefficientTestPoint n) := by
  intro i j hij
  unfold coefficientTestPoint at hij
  have hden : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hval : (i.val : ℝ) = j.val := (div_left_inj' hden).mp hij
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

/-- The coefficient parametrization of polynomial functions on `[-1,1]`. -/
def coeffToApproximationMap (n : ℕ) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] ApproximationIntervalMap where
  toFun c := polynomialOnApproximationInterval (polynomialOfCoeffs n c)
  map_add' c d := by
    ext x
    have hpoly : polynomialOfCoeffs n (c + d) =
        polynomialOfCoeffs n c + polynomialOfCoeffs n d := by
      unfold polynomialOfCoeffs
      simp [map_add, Finset.sum_add_distrib]
    simp [polynomialOnApproximationInterval, hpoly, eval_add]
  map_smul' r c := by
    ext x
    have hpoly : polynomialOfCoeffs n (r • c) = r • polynomialOfCoeffs n c := by
      unfold polynomialOfCoeffs
      simp [smul_monomial, Finset.smul_sum]
    simp [polynomialOnApproximationInterval, hpoly, eval_smul, smul_eq_mul]

/-- Distinct coefficient vectors give distinct continuous functions. -/
lemma coeffToApproximationMap_injective (n : ℕ) :
    Function.Injective (coeffToApproximationMap n) := by
  intro c d hcd
  rw [← sub_eq_zero, ← LinearMap.map_sub] at hcd
  have hp : polynomialOfCoeffs n (c - d) = 0 :=
    eq_zero_of_polynomialOnApproximationInterval_eq_zero
      (polynomialOfCoeffs n (c - d)) (natDegree_polynomialOfCoeffs_le n (c - d)) hcd
  exact sub_eq_zero.mp ((polynomialOfCoeffs_eq_zero_iff n (c - d)).mp hp)

/-- The coefficient embedding is anti-Lipschitz for the supremum norm. -/
lemma exists_antilipschitz_coeffToApproximationMap (n : ℕ) :
    ∃ K : NNReal, 0 < K ∧ AntilipschitzWith K (coeffToApproximationMap n) := by
  simpa using (coeffToApproximationMap n).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.mpr (coeffToApproximationMap_injective n))

/-- A minimizing coefficient vector exists for the uniform error. -/
lemma exists_isBestPolynomialApproximation (f : ApproximationIntervalMap) (n : ℕ) :
    ∃ p : ℝ[X], IsBestPolynomialApproximation f n p := by
  obtain ⟨K, hKpos, hK⟩ := exists_antilipschitz_coeffToApproximationMap n
  let err : (Fin (n + 1) → ℝ) → ℝ := fun c => ‖f - coeffToApproximationMap n c‖
  have herr : Continuous err := by
    unfold err
    exact continuous_norm.comp
      ((continuous_const.sub (coeffToApproximationMap n).continuous_of_finiteDimensional))
  let R : ℝ := 2 * (K : ℝ) * ‖f‖
  have hR : 0 ≤ R := by positivity
  let B := closedBall (0 : Fin (n + 1) → ℝ) R
  obtain ⟨c, hc, hmin⟩ := (isCompact_closedBall (0 : Fin (n + 1) → ℝ) R).exists_isMinOn
    ⟨0, mem_closedBall_self hR⟩ herr.continuousOn
  refine ⟨polynomialOfCoeffs n c, natDegree_polynomialOfCoeffs_le n c, ?_⟩
  intro q hq
  let d : Fin (n + 1) → ℝ := fun i => q.coeff i.val
  have hqeq : polynomialOfCoeffs n d = q := polynomialOfCoeffs_of_natDegree_le n q hq
  have herrq : ‖f - polynomialOnApproximationInterval q‖ = err d := by
    simp [err, hqeq, coeffToApproximationMap]
  by_cases hd : ‖d‖ ≤ R
  · have hdB : d ∈ B := by simpa [B, mem_closedBall, dist_zero_right] using hd
    have hmin' := hmin hdB
    simpa [err, coeffToApproximationMap, hqeq] using hmin'
  · have hdlt : R < ‖d‖ := lt_of_not_ge hd
    have hanti := ZeroHomClass.bound_of_antilipschitz (coeffToApproximationMap n) hK d
    have h1 : R < (K : ℝ) * ‖coeffToApproximationMap n d‖ := lt_of_lt_of_le hdlt hanti
    have hK0 : (0 : ℝ) < K := NNReal.coe_pos.mpr hKpos
    have h2 : 2 * ‖f‖ < ‖coeffToApproximationMap n d‖ := by
      have h1' : (K : ℝ) * (2 * ‖f‖) < (K : ℝ) * ‖coeffToApproximationMap n d‖ := by
        simpa [R, mul_left_comm, mul_assoc] using h1
      exact lt_of_mul_lt_mul_left h1' hK0.le
    have hdiff : ‖coeffToApproximationMap n d‖ - ‖f‖ ≤ err d := by
      have hsub := (le_abs_self _).trans
        (abs_norm_sub_norm_le (coeffToApproximationMap n d) f)
      simpa [err, norm_sub_rev] using hsub
    have herrd : ‖f‖ < err d := by
      have : ‖f‖ < ‖coeffToApproximationMap n d‖ - ‖f‖ := by linarith
      linarith
    have herr0 : err c ≤ err 0 := hmin (mem_closedBall_self hR)
    have herr0' : err 0 = ‖f‖ := by simp [err, map_zero]
    have hle : err c < err d := lt_of_le_of_lt (by simpa [herr0'] using herr0) herrd
    simpa [err, coeffToApproximationMap, herrq] using hle.le

/-- Equidistant nodes from `-1` to `1`, including the endpoints. -/
def alternationNode (n : ℕ) (i : Fin (n + 2)) : Set.Icc (-1 : ℝ) 1 :=
  ⟨-1 + 2 * (i.val : ℝ) / (n + 1), by
    have hden : (0 : ℝ) < n + 1 := by positivity
    have hratio_nonneg : 0 ≤ (i.val : ℝ) / (n + 1) :=
      div_nonneg (Nat.cast_nonneg _) hden.le
    have hratio_le : (i.val : ℝ) / (n + 1) ≤ 1 := by
      rw [div_le_one hden]
      exact_mod_cast Nat.le_of_lt_succ i.isLt
    refine ⟨?_, ?_⟩
    · have : 0 ≤ 2 * (i.val : ℝ) / (n + 1) := by positivity
      linarith
    · have hmul : 2 * ((i.val : ℝ) / (n + 1)) ≤ 2 := by nlinarith [hratio_le]
      have heq : 2 * (i.val : ℝ) / (n + 1) = 2 * ((i.val : ℝ) / (n + 1)) := by ring
      linarith [hmul, heq]⟩

/-- The equidistant nodes are strictly increasing. -/
lemma strictMono_alternationNode (n : ℕ) :
    StrictMono (fun i : Fin (n + 2) => (alternationNode n i).1) := by
  intro i j hij
  have hden : (0 : ℝ) < n + 1 := by positivity
  have hval : (i.val : ℝ) < j.val := by exact_mod_cast hij
  unfold alternationNode
  have : 2 * (i.val : ℝ) / (n + 1) < 2 * (j.val : ℝ) / (n + 1) := by
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hval (by norm_num)) hden
  linarith

/-- A zero residual alternates at every ordered node set. -/
lemma hasPolynomialAlternation_of_norm_eq_zero (f : ApproximationIntervalMap) (p : ℝ[X])
    (n : ℕ) (h : ‖f - polynomialOnApproximationInterval p‖ = 0) :
    HasPolynomialAlternation f p n := by
  refine ⟨alternationNode n, strictMono_alternationNode n, 1, abs_one, ?_⟩
  intro i
  have hfun : f - polynomialOnApproximationInterval p = 0 := norm_eq_zero.mp h
  have hpt : f (alternationNode n i) - p.eval (alternationNode n i).1 = 0 := by
    have := congrArg (fun g => g (alternationNode n i)) hfun
    simpa [sub_apply, polynomialOnApproximationInterval] using this
  rw [hpt, h]
  simp

/-- Opposite strict signs of a polynomial produce a root between them. -/
lemma exists_eval_eq_zero_Ioo {a b : ℝ} (hab : a < b) (p : ℝ[X])
    (hsign : p.eval a * p.eval b < 0) : ∃ t ∈ Set.Ioo a b, p.eval t = 0 := by
  have hcont : ContinuousOn p.eval (Set.Icc a b) := p.continuous.continuousOn
  rcases mul_neg_iff.mp hsign with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨t, ht, ht0⟩ :=
      (intermediate_value_Ioo' hab.le hcont) (⟨hb, ha⟩ : (0 : ℝ) ∈ Set.Ioo (p.eval b) (p.eval a))
    exact ⟨t, ht, ht0⟩
  · obtain ⟨t, ht, ht0⟩ :=
      (intermediate_value_Ioo hab.le hcont) (⟨ha, hb⟩ : (0 : ℝ) ∈ Set.Ioo (p.eval a) (p.eval b))
    exact ⟨t, ht, ht0⟩

/-- A unit multiple of an alternation sign still squares to one. -/
lemma sq_eq_one_of_alternationSign {σ : ℝ} (hσ : |σ| = 1) (i : ℕ) :
    (σ * (-1) ^ i) ^ 2 = 1 := by
  have hσsq : σ ^ 2 = 1 := by simpa [hσ] using (sq_abs σ).symm
  have hpow : ((-1 : ℝ) ^ i) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    simp
  calc
    (σ * (-1) ^ i) ^ 2 = σ ^ 2 * ((-1) ^ i) ^ 2 := by ring
    _ = 1 := by rw [hσsq, hpow, mul_one]

/-- Equioscillation prevents every strictly better polynomial of degree at most `n`. -/
lemma isBestPolynomialApproximation_of_hasPolynomialAlternation
    (f : ApproximationIntervalMap) (n : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ n)
    (halt : HasPolynomialAlternation f p n) : IsBestPolynomialApproximation f n p := by
  refine ⟨hp, ?_⟩
  intro q hq
  by_contra hlt
  have hlt : ‖f - polynomialOnApproximationInterval q‖ <
      ‖f - polynomialOnApproximationInterval p‖ := lt_of_not_ge hlt
  set E : ℝ := ‖f - polynomialOnApproximationInterval p‖
  have hEpos : 0 < E := lt_of_le_of_lt (norm_nonneg _) hlt
  obtain ⟨x, hxmono, σ, hσ, hx⟩ := halt
  set d : ℝ[X] := p - q
  have hddeg : d.natDegree ≤ n := (natDegree_sub_le p q).trans (max_le hp hq)
  have hnode : ∀ i : Fin (n + 2), (σ * (-1) ^ i.val) * d.eval (x i).1 < 0 := by
    intro i
    have hs : |(f - polynomialOnApproximationInterval q) (x i)| < E :=
      lt_of_le_of_lt
        ((f - polynomialOnApproximationInterval q).norm_coe_le_norm (x i)) hlt
    have hdeval : d.eval (x i).1 =
        (f - polynomialOnApproximationInterval q) (x i) -
          (f - polynomialOnApproximationInterval p) (x i) := by
      simp [d, polynomialOnApproximationInterval, eval_sub]
    have hres : (f - polynomialOnApproximationInterval p) (x i) =
        σ * (-1) ^ i.val * E := hx i
    set ε : ℝ := σ * (-1) ^ i.val
    set s : ℝ := (f - polynomialOnApproximationInterval q) (x i)
    have hεsq : ε ^ 2 = 1 := sq_eq_one_of_alternationSign hσ i.val
    have hεabs : |ε| = 1 := by
      simpa [abs_one] using (sq_eq_sq_iff_abs_eq_abs ε 1).mp (by simpa using hεsq)
    have hcalc : ε * d.eval (x i).1 = ε * s - E := by
      have hdeval' : d.eval (x i).1 = s - ε * E := by rw [hdeval, hres]
      calc
        ε * d.eval (x i).1 = ε * (s - ε * E) := by rw [hdeval']
        _ = ε * s - ε * ε * E := by ring
        _ = ε * s - E := by rw [← sq, hεsq, one_mul]
    have hsle : ε * s ≤ |s| := by
      calc
        ε * s ≤ |ε * s| := le_abs_self _
        _ = |ε| * |s| := abs_mul _ _
        _ = |s| := by rw [hεabs, one_mul]
    have hs' : |s| < E := by simpa [s] using hs
    linarith
  have hprod : ∀ i : Fin (n + 1),
      d.eval (x i.castSucc).1 * d.eval (x i.succ).1 < 0 := by
    intro i
    set ε1 : ℝ := σ * (-1) ^ (i.castSucc).val
    set ε2 : ℝ := σ * (-1) ^ (i.succ).val
    have hε2 : ε2 = -ε1 := by
      simp only [ε1, ε2, Fin.val_succ, Fin.val_castSucc, pow_succ]
      ring
    have h1 : ε1 * d.eval (x i.castSucc).1 < 0 := by simpa [ε1] using hnode i.castSucc
    have h2 : ε2 * d.eval (x i.succ).1 < 0 := by simpa [ε2] using hnode i.succ
    have hε1sq : ε1 ^ 2 = 1 := sq_eq_one_of_alternationSign hσ (i.castSucc).val
    set A : ℝ := d.eval (x i.castSucc).1
    set B : ℝ := d.eval (x i.succ).1
    have hAB : A * B = (ε1 * A) * (ε1 * B) := by
      have hmul : ε1 * ε1 = 1 := by simpa [sq] using hε1sq
      calc
        A * B = (ε1 * ε1) * (A * B) := by rw [hmul, one_mul]
        _ = (ε1 * A) * (ε1 * B) := by ring
    have hBpos : 0 < ε1 * B := by
      have : ε2 * B = -(ε1 * B) := by rw [hε2]; ring
      linarith
    have : (ε1 * A) * (ε1 * B) < 0 := mul_neg_of_neg_of_pos h1 hBpos
    simpa [hAB] using this
  choose root hroot using fun i : Fin (n + 1) =>
    exists_eval_eq_zero_Ioo (hxmono i.castSucc_lt_succ) d (hprod i)
  have hinj : Function.Injective root := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hijlt | hjilt
    · have hle : (x i.succ).1 ≤ (x j.castSucc).1 :=
        hxmono.monotone (by
          rw [Fin.le_iff_val_le_val]
          simp only [Fin.val_succ, Fin.val_castSucc]
          exact Nat.succ_le_of_lt hijlt)
      have : root i < root j :=
        lt_of_lt_of_le (hroot i).1.2 (le_trans hle (hroot j).1.1.le)
      exact lt_irrefl _ (hij ▸ this)
    · have hle : (x j.succ).1 ≤ (x i.castSucc).1 :=
        hxmono.monotone (by
          rw [Fin.le_iff_val_le_val]
          simp only [Fin.val_succ, Fin.val_castSucc]
          exact Nat.succ_le_of_lt hjilt)
      have : root j < root i :=
        lt_of_lt_of_le (hroot j).1.2 (le_trans hle (hroot i).1.1.le)
      exact lt_irrefl _ (hij ▸ this)
  have hd0 : d = 0 :=
    eq_zero_of_natDegree_lt_card_of_eval_eq_zero d hinj (fun i => (hroot i).2)
      (by simpa [Fintype.card_fin] using Nat.lt_succ_of_le hddeg)
  have hpq : polynomialOnApproximationInterval p = polynomialOnApproximationInterval q :=
    congrArg polynomialOnApproximationInterval (sub_eq_zero.mp hd0)
  simp [E, hpq] at hlt

/-- An alternation sign has absolute value one. -/
lemma abs_alternationSign {σ : ℝ} (hσ : |σ| = 1) (i : ℕ) : |σ * (-1) ^ i| = 1 := by
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, hσ, mul_one]

/-- The next alternation sign is the negative of the current one. -/
lemma alternationSign_succ {σ : ℝ} (i : ℕ) :
    σ * (-1) ^ (i + 1) = -(σ * (-1) ^ i) := by
  rw [pow_succ]
  ring

/-- A nonzero multiple of an alternation sign differs from its successor. -/
lemma ne_alternationSign_succ {σ E : ℝ} (hσ : |σ| = 1) (hE : E ≠ 0) (i : ℕ) :
    σ * (-1) ^ i * E ≠ σ * (-1) ^ (i + 1) * E := by
  intro h
  rw [alternationSign_succ] at h
  have h0 : σ * (-1) ^ i * E = 0 := by linarith
  have hunit := abs_alternationSign hσ i
  have habs := congrArg abs h0
  rw [abs_mul, hunit, one_mul, abs_zero] at habs
  exact hE (abs_eq_zero.mp habs)

/-- Counting the factors equal to `-1` in a split alternation product. -/
lemma prod_sign_ite (k g : ℕ) (hg : g ≤ k) :
    (∏ i : Fin k, if i.val < g then (1 : ℝ) else -1) = (-1) ^ (k - g) := by
  induction k generalizing g with
  | zero =>
    have hg0 : g = 0 := Nat.eq_zero_of_le_zero hg
    simp [hg0]
  | succ k ih =>
    rw [Fin.prod_univ_castSucc]
    by_cases hgk : g ≤ k
    · have hlast : ¬ (Fin.last k).val < g := by
        simp only [Fin.val_last]
        omega
      have hlastv : (if (Fin.last k).val < g then (1 : ℝ) else -1) = -1 :=
        ite_eq_right hlast
      rw [hlastv]
      have hfront :
          (∏ i : Fin k, if (i.castSucc).val < g then (1 : ℝ) else -1) =
            (-1) ^ (k - g) := by
        have hcast : ∀ i : Fin k, (i.castSucc).val = i.val := fun i => Fin.val_castSucc i
        simp only [hcast]
        exact ih g hgk
      rw [hfront]
      have hsub : k + 1 - g = k - g + 1 := by omega
      rw [hsub, pow_succ]
    · have hg' : g = k + 1 := by omega
      have hcast : ∀ i : Fin k, (i.castSucc).val < g := by
        intro i
        simp only [Fin.val_castSucc, hg']
        omega
      have hlast : (Fin.last k).val < g := by
        simp only [Fin.val_last, hg']
        exact Nat.lt_succ_self k
      have hfront :
          (∏ i : Fin k, if (i.castSucc).val < g then (1 : ℝ) else -1) = 1 := by
        refine Eq.trans (Finset.prod_congr rfl ?_) Finset.prod_const_one
        intro i _
        exact ite_eq_left (hcast i)
      rw [hfront]
      have hlastv : (if (Fin.last k).val < g then (1 : ℝ) else -1) = 1 :=
        ite_eq_left hlast
      rw [hlastv, hg']
      simp

/-- The signed node product is positive when `g` roots lie to the left of `t`. -/
lemma alternation_factor_pos {k g : ℕ} (hg : g ≤ k) (z : Fin k → ℝ) (t : ℝ)
    (hleft : ∀ i : Fin k, i.val < g → z i < t)
    (hright : ∀ i : Fin k, g ≤ i.val → t < z i) :
    0 < (-1) ^ (k - g) * ∏ i : Fin k, (t - z i) := by
  have hsplit : ∀ i : Fin k, t - z i =
      (if i.val < g then (1 : ℝ) else -1) *
        (if i.val < g then t - z i else z i - t) := by
    intro i
    rcases lt_or_ge i.val g with h | h
    · rw [ite_eq_left h, ite_eq_left h]
      ring
    · have hlt : ¬ i.val < g := not_lt_of_ge h
      rw [ite_eq_right hlt, ite_eq_right hlt]
      ring
  have hprod : (∏ i : Fin k, (t - z i)) =
      (∏ i : Fin k, if i.val < g then (1 : ℝ) else -1) *
        ∏ i : Fin k, if i.val < g then t - z i else z i - t := by
    calc
      (∏ i : Fin k, (t - z i)) =
          ∏ i : Fin k, ((if i.val < g then (1 : ℝ) else -1) *
            (if i.val < g then t - z i else z i - t)) := by
        refine Finset.prod_congr rfl ?_
        intro i _
        exact hsplit i
      _ = (∏ i : Fin k, if i.val < g then (1 : ℝ) else -1) *
          ∏ i : Fin k, if i.val < g then t - z i else z i - t :=
        Finset.prod_mul_distrib
  rw [hprod, prod_sign_ite k g hg]
  have hpos : 0 < ∏ i : Fin k, if i.val < g then t - z i else z i - t := by
    refine Finset.prod_pos ?_
    intro i _
    by_cases h : i.val < g
    · simpa [h] using sub_pos.mpr (hleft i h)
    · simpa [h] using sub_pos.mpr (hright i (Nat.le_of_not_lt h))
  have hsq : (-1 : ℝ) ^ (k - g) * (-1) ^ (k - g) = 1 := by
    rw [← sq, ← pow_mul, mul_comm, pow_mul]
    simp
  calc
    (-1) ^ (k - g) * (((-1) ^ (k - g)) *
        ∏ i : Fin k, if i.val < g then t - z i else z i - t)
        = ((-1) ^ (k - g) * (-1) ^ (k - g)) *
            ∏ i : Fin k, if i.val < g then t - z i else z i - t := by ring
    _ = ∏ i : Fin k, if i.val < g then t - z i else z i - t := by rw [hsq, one_mul]
    _ > 0 := hpos

/-- A product of `k` real linear factors has degree at most `k`. -/
lemma natDegree_nodeProduct_le (k : ℕ) (z : Fin k → ℝ) :
    (∏ i : Fin k, (X - C (z i))).natDegree ≤ k := by
  induction k with
  | zero =>
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    simp
  | succ k ih =>
    rw [Fin.prod_univ_castSucc]
    calc
      ((∏ i : Fin k, (X - C (z i.castSucc))) * (X - C (z (Fin.last k)))).natDegree ≤
          (∏ i : Fin k, (X - C (z i.castSucc))).natDegree +
            (X - C (z (Fin.last k))).natDegree := natDegree_mul_le
      _ ≤ k + 1 := add_le_add (ih _) (natDegree_X_sub_C_le _)

/-- Scaling a node product does not raise its degree. -/
lemma natDegree_chebyshevCorrection_le (k : ℕ) (τ : ℝ) (z : Fin k → ℝ) :
    (C τ * ∏ i : Fin k, (X - C (z i))).natDegree ≤ k :=
  (natDegree_C_mul_le _ _).trans (natDegree_nodeProduct_le k z)

/-- A small step along a strict extremal correction lowers the supremum norm. -/
lemma norm_sub_smul_lt {e q : ApproximationIntervalMap} (hE : 0 < ‖e‖) {δ : ℝ}
    (hδ : 0 < δ) (hpos : ∀ x, ‖e x‖ = ‖e‖ → δ ≤ e x * q x) :
    ∃ ε : ℝ, 0 < ε ∧ ‖e - ε • q‖ < ‖e‖ := by
  let E := ‖e‖
  let M := ‖q‖ + 1
  have hM : 0 < M := by linarith [norm_nonneg q]
  let F : Set (Set.Icc (-1 : ℝ) 1) := {x | e x * q x ≤ δ / 2}
  have hFcl : IsClosed F := isClosed_le (e.continuous.mul q.continuous) continuous_const
  have hμ : ∃ μ : ℝ, μ < E ∧ ∀ x ∈ F, ‖e x‖ ≤ μ := by
    by_cases hne : F.Nonempty
    · obtain ⟨x0, hx0, hmax⟩ := hFcl.isCompact.exists_isMaxOn hne
        (continuous_norm.comp e.continuous).continuousOn
      have hlt : ‖e x0‖ < E := by
        by_contra hge
        have heq : ‖e x0‖ = E := le_antisymm (e.norm_coe_le_norm x0) (le_of_not_gt hge)
        linarith [hpos x0 heq, show e x0 * q x0 ≤ δ / 2 from hx0]
      exact ⟨‖e x0‖, hlt, isMaxOn_iff.mp hmax⟩
    · exact ⟨0, hE, fun x hx => (hne ⟨x, hx⟩).elim⟩
  obtain ⟨μ, hμE, hμle⟩ := hμ
  let ε := min ((E - μ) / (2 * M)) (δ / (2 * M ^ 2))
  have hεpos : 0 < ε :=
    lt_min (div_pos (by linarith) (by positivity)) (div_pos hδ (by positivity))
  have hεF : ε ≤ (E - μ) / (2 * M) := min_le_left _ _
  have hεO : ε ≤ δ / (2 * M ^ 2) := min_le_right _ _
  have hmul : ((E - μ) / (2 * M)) * M = (E - μ) / 2 := by
    field_simp
  have hmul2 : (δ / (2 * M ^ 2)) * M ^ 2 = δ / 2 := by
    field_simp
  refine ⟨ε, hεpos, ?_⟩
  rw [(e - ε • q).norm_lt_iff hE]
  intro x
  rw [Real.norm_eq_abs, ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul]
  by_cases hxF : x ∈ F
  · have hqe : |q x| ≤ M := by
      have h1 : |q x| ≤ ‖q‖ := by simpa [Real.norm_eq_abs] using q.norm_coe_le_norm x
      linarith [norm_nonneg q]
    have heμ : |e x| ≤ μ := by simpa [Real.norm_eq_abs] using hμle x hxF
    have hhalf : ε * M ≤ (E - μ) / 2 := by
      have := mul_le_mul_of_nonneg_right hεF hM.le
      linarith [hmul]
    calc
      |e x - ε * q x| ≤ |e x| + |ε * q x| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le (e x) (-(ε * q x))
      _ = |e x| + ε * |q x| := by rw [abs_mul, abs_of_pos hεpos]
      _ ≤ μ + ε * M := by
        have := mul_le_mul_of_nonneg_left hqe hεpos.le
        linarith
      _ ≤ μ + (E - μ) / 2 := by linarith
      _ < E := by linarith
  · have hgt : δ / 2 < e x * q x := lt_of_not_ge (by simpa [F] using hxF)
    have he2 : e x ^ 2 ≤ E ^ 2 := by
      have : |e x| ≤ |E| := by
        simpa [E, abs_of_pos hE, Real.norm_eq_abs] using e.norm_coe_le_norm x
      exact sq_le_sq.mpr this
    have hq2 : q x ^ 2 ≤ M ^ 2 := by
      have hqe : |q x| ≤ M := by
        have h1 : |q x| ≤ ‖q‖ := by simpa [Real.norm_eq_abs] using q.norm_coe_le_norm x
        linarith [norm_nonneg q]
      exact sq_le_sq.mpr (by simpa [abs_of_pos hM] using hqe)
    have hcross : -2 * ε * (e x * q x) < -ε * δ := by
      have hmulε : 2 * ε * (δ / 2) < 2 * ε * (e x * q x) :=
        mul_lt_mul_of_pos_left hgt (by positivity)
      have := neg_lt_neg hmulε
      have hid : 2 * ε * (δ / 2) = ε * δ := by ring
      simpa [hid] using this
    have hcube : ε ^ 2 * q x ^ 2 ≤ ε ^ 2 * M ^ 2 :=
      mul_le_mul_of_nonneg_left hq2 (by positivity)
    have hsq : (e x - ε * q x) ^ 2 < E ^ 2 - ε * δ + ε ^ 2 * M ^ 2 := by
      have hexp : (e x - ε * q x) ^ 2 =
          e x ^ 2 - 2 * ε * (e x * q x) + ε ^ 2 * q x ^ 2 := by ring
      linarith [hexp, he2, hcross, hcube]
    have hεM : ε * M ^ 2 ≤ δ / 2 := by
      have := mul_le_mul_of_nonneg_right hεO (by positivity : 0 ≤ M ^ 2)
      linarith [hmul2]
    have hdrop : E ^ 2 - ε * δ + ε ^ 2 * M ^ 2 ≤ E ^ 2 - ε * δ / 2 := by
      have : ε ^ 2 * M ^ 2 ≤ ε * (δ / 2) := by
        calc
          ε ^ 2 * M ^ 2 = ε * (ε * M ^ 2) := by ring
          _ ≤ ε * (δ / 2) := mul_le_mul_of_nonneg_left hεM hεpos.le
      linarith
    have hltE : E ^ 2 - ε * δ / 2 < E ^ 2 := by
      have : 0 < ε * δ / 2 := by positivity
      linarith
    have : (e x - ε * q x) ^ 2 < E ^ 2 :=
      lt_trans (lt_of_lt_of_le hsq hdrop) hltE
    exact abs_lt_of_sq_lt_sq this hE.le

/-- Two values in `[-E, E]` with endpoint average both equal that endpoint. -/
lemma eq_of_avg_endpoint {a b E ε : ℝ} (ha : |a| ≤ E) (hb : |b| ≤ E) (hε : |ε| = 1)
    (havg : (a + b) / 2 = ε * E) : a = ε * E ∧ b = ε * E := by
  have hσsq : ε ^ 2 = 1 := by simpa [hε] using (sq_abs ε).symm
  have hsum : a + b = 2 * (ε * E) := by linarith
  have ha' : ε * a ≤ E := by
    calc
      ε * a ≤ |ε * a| := le_abs_self _
      _ = |a| := by rw [abs_mul, hε, one_mul]
      _ ≤ E := ha
  have hb' : ε * b ≤ E := by
    calc
      ε * b ≤ |ε * b| := le_abs_self _
      _ = |b| := by rw [abs_mul, hε, one_mul]
      _ ≤ E := hb
  have hsum' : ε * a + ε * b = 2 * E := by
    calc
      ε * a + ε * b = ε * (a + b) := by ring
      _ = ε * (2 * (ε * E)) := by rw [hsum]
      _ = 2 * (ε ^ 2) * E := by ring
      _ = 2 * E := by rw [hσsq]; ring
  have haE : ε * a = E := by linarith
  have hbE : ε * b = E := by linarith
  refine ⟨?_, ?_⟩
  · calc
      a = ε * (ε * a) := by rw [← mul_assoc, ← sq, hσsq, one_mul]
      _ = ε * E := by rw [haE]
  · calc
      b = ε * (ε * b) := by rw [← mul_assoc, ← sq, hσsq, one_mul]
      _ = ε * E := by rw [hbE]

/-- A point of the approximation interval `[-1, 1]`. -/
abbrev IntervalPoint := Set.Icc (-1 : ℝ) 1

/-- A greedy chain of alternating residual extrema, built from the left. -/
structure ExtremalChain (e : ApproximationIntervalMap) where
  /-- Number of nodes already chosen. -/
  m : ℕ
  /-- The chain contains a node. -/
  hm : 0 < m
  /-- Nodes, used at indices strictly less than `m`. -/
  point : ℕ → IntervalPoint
  /-- Sign of the residual at the first node. -/
  σ : ℝ
  /-- The opening sign is a unit. -/
  hσ : |σ| = 1
  /-- Later nodes lie strictly to the right. -/
  mono : ∀ ⦃i j : ℕ⦄, i < j → j < m → (point i).1 < (point j).1
  /-- Each node carries the alternating extremal value. -/
  val : ∀ i, i < m → e (point i) = σ * (-1) ^ i * ‖e‖
  /-- The first node is the leftmost extremum. -/
  first : IsLeast {x | ‖e x‖ = ‖e‖} (point 0)
  /-- Each successor is the leftmost extremum of the next sign. -/
  leastNext : ∀ i, i + 1 < m →
    IsLeast {x | (point i).1 < x.1 ∧ e x = σ * (-1) ^ (i + 1) * ‖e‖} (point (i + 1))

/-- No further alternating extremum lies to the right of a stopped chain. -/
def ExtremalChain.stopped {e : ApproximationIntervalMap} (c : ExtremalChain e) : Prop :=
  ∀ x : IntervalPoint, (c.point (c.m - 1)).1 < x.1 →
    e x ≠ c.σ * (-1) ^ c.m * ‖e‖

/-- Nodes of a chain are weakly increasing. -/
lemma ExtremalChain.point_le {e : ApproximationIntervalMap} (c : ExtremalChain e)
    {i j : ℕ} (hij : i ≤ j) (hj : j < c.m) : (c.point i).1 ≤ (c.point j).1 := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · rfl
  · exact (c.mono hlt hj).le

/-- The leftmost norm-attaining point starts an alternation chain. -/
lemma exists_extremalChain_one (e : ApproximationIntervalMap) (hE : 0 < ‖e‖) :
    ∃ c : ExtremalChain e, c.m = 1 := by
  obtain ⟨x, -, hmax⟩ := isCompact_univ.exists_isMaxOn
    (⟨⟨0, by constructor <;> norm_num⟩, Set.mem_univ _⟩ :
      (Set.univ : Set IntervalPoint).Nonempty)
    (continuous_norm.comp e.continuous).continuousOn
  have hx : ‖e x‖ = ‖e‖ := by
    apply le_antisymm (e.norm_coe_le_norm x)
    exact (e.norm_le (norm_nonneg _)).2 fun y =>
      (isMaxOn_iff.mp hmax) y (Set.mem_univ y)
  have hScl : IsClosed {y : IntervalPoint | ‖e y‖ = ‖e‖} :=
    isClosed_eq (continuous_norm.comp e.continuous) continuous_const
  obtain ⟨x0, hx0⟩ := hScl.isCompact.exists_isLeast ⟨x, hx⟩
  have hx0n : ‖e x0‖ = ‖e‖ := hx0.1
  let σ := e x0 / ‖e‖
  have hσ : |σ| = 1 := by
    have habs : |e x0| = ‖e‖ := by rw [← Real.norm_eq_abs, hx0n]
    rw [abs_div, habs, abs_of_pos hE, div_self hE.ne']
  refine ⟨{
    m := 1
    hm := Nat.one_pos
    point := fun _ => x0
    σ := σ
    hσ := hσ
    mono := by
      intro i j hij hj
      have : False := by omega
      exact this.elim
    val := by
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      show e x0 = e x0 / ‖e‖ * (-1) ^ 0 * ‖e‖
      rw [pow_zero, mul_one]
      exact (div_mul_cancel₀ _ hE.ne').symm
    first := hx0
    leastNext := by
      intro i hi
      have hi1 : i + 1 < 1 := hi
      omega
  }, rfl⟩

/-- A chain that is not stopped extends by one alternation node. -/
lemma ExtremalChain.grow {e : ApproximationIntervalMap} (c : ExtremalChain e)
    (hE : 0 < ‖e‖) (hopen : ¬ c.stopped) : ∃ c' : ExtremalChain e, c'.m = c.m + 1 := by
  let pred : IntervalPoint := c.point (c.m - 1)
  let nextSign : ℝ := c.σ * (-1) ^ c.m * ‖e‖
  have hpred_ne : e pred ≠ nextSign := by
    have hm := c.hm
    have hval := c.val (c.m - 1) (by omega)
    have hexp : (c.m - 1) + 1 = c.m := by omega
    have hne := ne_alternationSign_succ c.hσ hE.ne' (c.m - 1)
    simpa [pred, nextSign, hval, hexp] using hne
  have hne : ∃ x : IntervalPoint, pred.1 < x.1 ∧ e x = nextSign := by
    by_contra hnone
    apply hopen
    intro x hxlt heq
    exact hnone ⟨x, hxlt, heq⟩
  let T : Set IntervalPoint := {x | pred.1 ≤ x.1 ∧ e x = nextSign}
  have hTeq : {x | pred.1 < x.1 ∧ e x = nextSign} = T := by
    ext x
    constructor
    · rintro ⟨hlt, he⟩
      exact ⟨hlt.le, he⟩
    · rintro ⟨hle, he⟩
      refine ⟨lt_of_le_of_ne hle ?_, he⟩
      intro heq
      exact hpred_ne (by simpa [pred, Subtype.ext heq] using he)
  have hTne : T.Nonempty := by
    obtain ⟨x0, hx0lt, hx0e⟩ := hne
    exact ⟨x0, hx0lt.le, hx0e⟩
  have hTcl : IsClosed T := by
    have hA : IsClosed {x : IntervalPoint | pred.1 ≤ x.1} :=
      isClosed_le continuous_const continuous_subtype_val
    have hB : IsClosed {x : IntervalPoint | e x = nextSign} :=
      isClosed_eq e.continuous continuous_const
    have : T = {x | pred.1 ≤ x.1} ∩ {x | e x = nextSign} := by
      ext x
      simp [T]
    simpa [this] using hA.inter hB
  obtain ⟨y, hyT⟩ := hTcl.isCompact.exists_isLeast hTne
  have hyS : IsLeast {x | pred.1 < x.1 ∧ e x = nextSign} y := by
    rw [hTeq]
    exact hyT
  let point' : ℕ → IntervalPoint := fun i => if h : i < c.m then c.point i else y
  refine ⟨{
    m := c.m + 1
    hm := Nat.succ_pos _
    point := point'
    σ := c.σ
    hσ := c.hσ
    mono := by
      intro i j hij hj
      by_cases hjc : j < c.m
      · have hic : i < c.m := lt_trans hij hjc
        have hpi : point' i = c.point i := by simp only [point', dite_eq_left hic]
        have hpj : point' j = c.point j := by simp only [point', dite_eq_left hjc]
        rw [hpi, hpj]
        exact c.mono hij hjc
      · have hjv : j = c.m := by omega
        have hic : i < c.m := by omega
        have hpi : point' i = c.point i := by simp only [point', dite_eq_left hic]
        have hpj : point' j = y := by
          simp only [point', hjv]
          exact dite_eq_right (lt_irrefl _)
        rw [hpi, hpj]
        have hi_le : (c.point i).1 ≤ pred.1 := by
          simpa [pred] using c.point_le (by omega : i ≤ c.m - 1) (by omega)
        exact lt_of_le_of_lt hi_le hyS.1.1
    val := by
      intro i hi
      by_cases hic : i < c.m
      · have hpi : point' i = c.point i := by simp only [point', dite_eq_left hic]
        rw [hpi]
        exact c.val i hic
      · have hi' : i = c.m := by omega
        have hpi : point' i = y := by
          simp only [point', hi']
          exact dite_eq_right (lt_irrefl _)
        rw [hpi]
        simpa [nextSign, hi'] using hyS.1.2
    first := by
      have h0 : point' 0 = c.point 0 := by simp only [point', dite_eq_left c.hm]
      rw [h0]
      exact c.first
    leastNext := by
      intro i hi
      by_cases hstep : i + 1 < c.m
      · have hpi : point' i = c.point i := by
          simp only [point', dite_eq_left (show i < c.m by omega)]
        have hpi1 : point' (i + 1) = c.point (i + 1) := by
          simp only [point', dite_eq_left hstep]
        rw [hpi, hpi1]
        exact c.leastNext i hstep
      · have hi0 : i = c.m - 1 := by omega
        have hexp : i + 1 = c.m := by omega
        have hpi : point' i = c.point i := by
          simp only [point', dite_eq_left (show i < c.m by omega)]
        have hpy : point' (i + 1) = y := by
          simp only [point', hexp]
          exact dite_eq_right (lt_irrefl _)
        rw [hpi, hpy, hexp, hi0]
        exact hyS
  }, rfl⟩

/-- Some alternation chain has length `N + 1`, or stops no later than that. -/
lemma exists_extremalChain_bounded (e : ApproximationIntervalMap) (hE : 0 < ‖e‖) (N : ℕ) :
    ∃ c : ExtremalChain e, c.m ≤ N + 1 ∧ (c.m = N + 1 ∨ c.stopped) := by
  induction N with
  | zero =>
    obtain ⟨c, hc⟩ := exists_extremalChain_one e hE
    exact ⟨c, by simp [hc], Or.inl hc⟩
  | succ N ih =>
    obtain ⟨c, hle, h⟩ := ih
    rcases h with hlen | hstop
    · by_cases hs : c.stopped
      · exact ⟨c, by omega, Or.inr hs⟩
      · obtain ⟨c', hc'⟩ := c.grow hE hs
        exact ⟨c', by omega, Or.inl (by omega)⟩
    · exact ⟨c, by omega, Or.inr hstop⟩

/-- Every extremum of a stopped chain lies in one greedy sign group. -/
lemma exists_extremal_group {e : ApproximationIntervalMap} (c : ExtremalChain e)
    (hE : 0 < ‖e‖) (hstop : c.stopped) {x : IntervalPoint} (hx : ‖e x‖ = ‖e‖) :
    ∃ j, j < c.m ∧ (c.point j).1 ≤ x.1 ∧ e x = c.σ * (-1) ^ j * ‖e‖ ∧
      (j + 1 < c.m → x.1 < (c.point (j + 1)).1) := by
  classical
  let P : ℕ → Prop := fun j => j < c.m ∧ (c.point j).1 ≤ x.1
  have hP0 : P 0 := ⟨c.hm, Subtype.coe_le_coe.mp (c.first.2 (Set.mem_ofPred.mpr hx))⟩
  let j := Nat.findGreatest P c.m
  have hjP : P j := Nat.findGreatest_spec (m := 0) (by omega) hP0
  have hnot : ∀ n, j < n → n ≤ c.m → ¬ P n := by
    intro n hn hle hPn
    have hle' : n ≤ j := Nat.le_findGreatest hle hPn
    omega
  set ε : ℝ := c.σ * (-1) ^ j
  have hεabs : |ε| = 1 := abs_alternationSign c.hσ j
  have hxsq : (e x) ^ 2 = (ε * ‖e‖) ^ 2 := by
    have habs : |e x| = ‖e‖ := by simpa [Real.norm_eq_abs] using hx
    have hεE : |ε * ‖e‖| = ‖e‖ := by rw [abs_mul, hεabs, one_mul, abs_of_pos hE]
    calc
      (e x) ^ 2 = |e x| ^ 2 := by rw [sq_abs]
      _ = ‖e‖ ^ 2 := by rw [habs]
      _ = |ε * ‖e‖| ^ 2 := by rw [hεE]
      _ = (ε * ‖e‖) ^ 2 := by rw [sq_abs]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxsq with hsame | hopp
  · refine ⟨j, hjP.1, hjP.2, by simpa [ε] using hsame, ?_⟩
    intro hnext
    by_contra hge
    have hle : (c.point (j + 1)).1 ≤ x.1 := not_lt.mp hge
    exact hnot (j + 1) (by omega) (by omega) ⟨hnext, hle⟩
  · have hopp' : e x = c.σ * (-1) ^ (j + 1) * ‖e‖ := by
      calc
        e x = -(ε * ‖e‖) := hopp
        _ = c.σ * (-1) ^ (j + 1) * ‖e‖ := by
          rw [alternationSign_succ]
          ring
    have hxlt : (c.point j).1 < x.1 := by
      apply lt_of_le_of_ne hjP.2
      intro heq
      have hxeq : x = c.point j := Subtype.ext heq.symm
      have hopp'' : e (c.point j) = c.σ * (-1) ^ (j + 1) * ‖e‖ := by
        simpa [hxeq] using hopp'
      have hval := c.val j hjP.1
      exact ne_alternationSign_succ c.hσ hE.ne' j (hval.symm.trans hopp'')
    by_cases hnext : j + 1 < c.m
    · have hmem : (c.point j).1 < x.1 ∧ e x = c.σ * (-1) ^ (j + 1) * ‖e‖ := ⟨hxlt, hopp'⟩
      have hle := (c.leastNext j hnext).2 hmem
      exact (hnot (j + 1) (by omega) (by omega)
        ⟨hnext, Subtype.coe_le_coe.mp hle⟩).elim
    · have hjlast : j = c.m - 1 := by omega
      have hadd : c.m - 1 + 1 = c.m := by
        have hm := c.hm
        omega
      have hpred : (c.point (c.m - 1)).1 < x.1 := by simpa [hjlast] using hxlt
      exact (hstop x hpred (by simpa [hjlast, hadd] using hopp')).elim

/-- A separator sits strictly between one sign group and the next chain node. -/
lemma exists_chainSeparator (e : ApproximationIntervalMap) (c : ExtremalChain e)
    (hE : 0 < ‖e‖) (_hstop : c.stopped) (i : ℕ) (hi : i + 1 < c.m) :
    ∃ z : ℝ, (c.point i).1 < z ∧ z < (c.point (i + 1)).1 ∧
      ∀ x : IntervalPoint, ‖e x‖ = ‖e‖ → e x = c.σ * (-1) ^ i * ‖e‖ →
        (c.point i).1 ≤ x.1 → x.1 < (c.point (i + 1)).1 → x.1 < z := by
  let sign : ℝ := c.σ * (-1) ^ i * ‖e‖
  let G : Set IntervalPoint := {x | ‖e x‖ = ‖e‖ ∧ (c.point i).1 ≤ x.1 ∧
    x.1 ≤ (c.point (i + 1)).1 ∧ e x = sign}
  have hmem : c.point i ∈ G := by
    refine ⟨?_, le_rfl, (c.mono (by omega) hi).le, c.val i (by omega)⟩
    have hv := c.val i (by omega)
    have : |e (c.point i)| = ‖e‖ := by
      rw [hv, abs_mul, abs_alternationSign c.hσ i, one_mul, abs_of_pos hE]
    simpa [Real.norm_eq_abs] using this
  have hcl : IsClosed G := by
    have hA : IsClosed {x : IntervalPoint | ‖e x‖ = ‖e‖} :=
      isClosed_eq (continuous_norm.comp e.continuous) continuous_const
    have hB : IsClosed {x : IntervalPoint | (c.point i).1 ≤ x.1} :=
      isClosed_le continuous_const continuous_subtype_val
    have hC : IsClosed {x : IntervalPoint | x.1 ≤ (c.point (i + 1)).1} :=
      isClosed_le continuous_subtype_val continuous_const
    have hD : IsClosed {x : IntervalPoint | e x = sign} :=
      isClosed_eq e.continuous continuous_const
    have hEq : G = {x | ‖e x‖ = ‖e‖} ∩ {x | (c.point i).1 ≤ x.1} ∩
        {x | x.1 ≤ (c.point (i + 1)).1} ∩ {x | e x = sign} := by
      ext x
      simp [G, Set.mem_inter_iff]
      tauto
    rw [hEq]
    exact ((hA.inter hB).inter hC).inter hD
  obtain ⟨w, hw⟩ := hcl.isCompact.exists_isGreatest ⟨c.point i, hmem⟩
  have hwlt : w.1 < (c.point (i + 1)).1 := by
    rcases lt_or_eq_of_le hw.1.2.2.1 with hlt | heq
    · exact hlt
    · have hwpt : w = c.point (i + 1) := Subtype.ext heq
      have hsame : sign = c.σ * (-1) ^ (i + 1) * ‖e‖ := by
        have hleft : e w = sign := hw.1.2.2.2
        have hright := c.val (i + 1) hi
        calc
          sign = e w := hleft.symm
          _ = e (c.point (i + 1)) := by rw [hwpt]
          _ = c.σ * (-1) ^ (i + 1) * ‖e‖ := hright
      exact (ne_alternationSign_succ c.hσ hE.ne' i hsame).elim
  let z : ℝ := (w.1 + (c.point (i + 1)).1) / 2
  have hwz : w.1 < z := by
    change w.1 < (w.1 + (c.point (i + 1)).1) / 2
    linarith
  have hzn : z < (c.point (i + 1)).1 := by
    change (w.1 + (c.point (i + 1)).1) / 2 < (c.point (i + 1)).1
    linarith
  refine ⟨z, lt_of_le_of_lt hw.1.2.1 hwz, hzn, ?_⟩
  intro x hx hsign hxge hxlt
  have hxG : x ∈ G := ⟨hx, hxge, hxlt.le, by simpa [sign] using hsign⟩
  exact lt_of_le_of_lt (Subtype.coe_le_coe.mp (hw.2 hxG)) hwz

/-- The chosen separator between sign group `i` and the next chain node. -/
noncomputable def chainSeparator (e : ApproximationIntervalMap) (c : ExtremalChain e)
    (hE : 0 < ‖e‖) (hstop : c.stopped) (i : ℕ) (hi : i + 1 < c.m) : ℝ :=
  Classical.choose (exists_chainSeparator e c hE hstop i hi)

/-- Separators lie between a sign group and the following chain node. -/
lemma chainSeparator_spec (e : ApproximationIntervalMap) (c : ExtremalChain e)
    (hE : 0 < ‖e‖) (hstop : c.stopped) (i : ℕ) (hi : i + 1 < c.m) :
    (c.point i).1 < chainSeparator e c hE hstop i hi ∧
      chainSeparator e c hE hstop i hi < (c.point (i + 1)).1 ∧
      ∀ x : IntervalPoint, ‖e x‖ = ‖e‖ → e x = c.σ * (-1) ^ i * ‖e‖ →
        (c.point i).1 ≤ x.1 → x.1 < (c.point (i + 1)).1 →
        x.1 < chainSeparator e c hE hstop i hi :=
  Classical.choose_spec (exists_chainSeparator e c hE hstop i hi)

/-- A chain of length `n + 2` is a polynomial alternation. -/
lemma hasPolynomialAlternation_of_extremalChain (f : ApproximationIntervalMap) (p : ℝ[X])
    (n : ℕ) (c : ExtremalChain (f - polynomialOnApproximationInterval p))
    (hm : c.m = n + 2) : HasPolynomialAlternation f p n := by
  refine ⟨fun i => c.point i.val, ?_, c.σ, c.hσ, ?_⟩
  · intro i j hij
    exact c.mono (by exact_mod_cast hij) (by omega)
  · intro i
    have hv := c.val i.val (by omega)
    simpa [sub_apply, polynomialOnApproximationInterval] using hv

/-- A best polynomial residual of positive norm equioscillates, or a correction exists. -/
lemma hasPolynomialAlternation_of_isBestPolynomialApproximation
    (f : ApproximationIntervalMap) (n : ℕ) (p : ℝ[X])
    (hp : IsBestPolynomialApproximation f n p) : HasPolynomialAlternation f p n := by
  set e : ApproximationIntervalMap := f - polynomialOnApproximationInterval p
  by_cases hE0 : ‖e‖ = 0
  · exact hasPolynomialAlternation_of_norm_eq_zero f p n hE0
  · have hE : 0 < ‖e‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hE0)
    obtain ⟨c, hle, hgrow⟩ := exists_extremalChain_bounded e hE (n + 1)
    rcases eq_or_ne c.m (n + 2) with hm | hm
    · exact hasPolynomialAlternation_of_extremalChain f p n c hm
    · have hstop : c.stopped := by
        rcases hgrow with hlen | hstop
        · exact (hm hlen).elim
        · exact hstop
      have hmle : c.m ≤ n + 1 := by omega
      let k := c.m - 1
      have hk : k ≤ n := by omega
      have hsep : ∀ i : Fin k, i.val + 1 < c.m := fun i => by have h := i.isLt; omega
      let z : Fin k → ℝ := fun i => chainSeparator e c hE hstop i.val (hsep i)
      let τ : ℝ := c.σ * (-1) ^ k
      let q : ℝ[X] := C τ * ∏ i : Fin k, (X - C (z i))
      have hqdeg : q.natDegree ≤ n := (natDegree_chebyshevCorrection_le k τ z).trans hk
      have hpos : ∀ x : IntervalPoint, ‖e x‖ = ‖e‖ → 0 < e x * q.eval x.1 := by
        intro x hx
        obtain ⟨j, hj, hjle, hjval, hjnext⟩ := exists_extremal_group c hE hstop hx
        have hjk : j ≤ k := by omega
        have hleft : ∀ i : Fin k, i.val < j → z i < x.1 := by
          intro i hi
          have hspec := chainSeparator_spec e c hE hstop i.val (hsep i)
          have hpt : (c.point (i.val + 1)).1 ≤ x.1 :=
            (c.point_le (by omega) (by omega)).trans hjle
          exact lt_of_lt_of_le hspec.2.1 hpt
        have hright : ∀ i : Fin k, j ≤ i.val → x.1 < z i := by
          intro i hi
          have hspec := chainSeparator_spec e c hE hstop i.val (hsep i)
          by_cases heq : i.val = j
          · exact hspec.2.2 x hx (by simpa [heq] using hjval)
              (by simpa [heq] using hjle) (by simpa [heq] using hjnext (by omega))
          · have hxlt := hjnext (by omega)
            have hpt : (c.point (j + 1)).1 ≤ (c.point i.val).1 :=
              c.point_le (by omega) (by have h := i.isLt; omega)
            exact lt_of_lt_of_le (lt_of_lt_of_le hxlt hpt) hspec.1.le
        have hfac := alternation_factor_pos hjk z x.1 hleft hright
        have heval : q.eval x.1 = τ * ∏ i : Fin k, (x.1 - z i) := by
          simp only [q, τ, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
        have hpow : (-1 : ℝ) ^ (j + k) = (-1) ^ (k - j) := by
          have hsum : j + k = (k - j) + 2 * j := by omega
          rw [hsum, pow_add, pow_mul, pow_two, neg_one_mul, neg_neg, one_pow, mul_one]
        have hσsq : c.σ ^ 2 = 1 := by simpa [c.hσ] using (sq_abs c.σ).symm
        have hident : e x * q.eval x.1 =
            ((-1) ^ (k - j) * ∏ i : Fin k, (x.1 - z i)) * ‖e‖ := by
          rw [hjval, heval]
          calc
            (c.σ * (-1) ^ j * ‖e‖) * (τ * ∏ i : Fin k, (x.1 - z i)) =
                c.σ * c.σ * ((-1) ^ j * (-1) ^ k) * ‖e‖ *
                  ∏ i : Fin k, (x.1 - z i) := by
              simp only [τ]
              ring
            _ = ((-1) ^ (k - j) * ∏ i : Fin k, (x.1 - z i)) * ‖e‖ := by
              rw [← sq, hσsq, ← pow_add, hpow]
              ring
        rw [hident]
        exact mul_pos hfac hE
      let qf : ApproximationIntervalMap := polynomialOnApproximationInterval q
      have hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ x, ‖e x‖ = ‖e‖ → δ ≤ e x * qf x := by
        let S : Set IntervalPoint := {x | ‖e x‖ = ‖e‖}
        have hSne : S.Nonempty := by
          refine ⟨c.point 0, ?_⟩
          rw [Set.mem_ofPred_eq, Real.norm_eq_abs]
          have hv := c.val 0 c.hm
          rw [hv, abs_mul, abs_alternationSign c.hσ 0, one_mul, abs_of_pos hE]
        have hScl : IsClosed S :=
          isClosed_eq (continuous_norm.comp e.continuous) continuous_const
        let φ : IntervalPoint → ℝ := fun x => e x * qf x
        have hφ : Continuous φ := e.continuous.mul qf.continuous
        obtain ⟨x0, hx0, hmin⟩ := hScl.isCompact.exists_isMinOn hSne hφ.continuousOn
        have hx0e : ‖e x0‖ = ‖e‖ := by simpa [S] using hx0
        refine ⟨φ x0, by simpa [φ, qf, polynomialOnApproximationInterval] using hpos x0 hx0e, ?_⟩
        intro x hx
        exact (isMinOn_iff.mp hmin) x (by simpa [S] using hx)
      obtain ⟨δ, hδ0, hδle⟩ := hδ
      have hδqf : ∀ x, ‖e x‖ = ‖e‖ → δ ≤ e x * qf x := hδle
      obtain ⟨ε, hε, hεnorm⟩ := norm_sub_smul_lt hE hδ0 hδqf
      have hdeg : (p + ε • q).natDegree ≤ n :=
        (natDegree_add_le _ _).trans (max_le hp.1 ((natDegree_smul_le _ _).trans hqdeg))
      have hmap : f - polynomialOnApproximationInterval (p + ε • q) = e - ε • qf := by
        ext x
        simp only [e, qf, polynomialOnApproximationInterval, ContinuousMap.sub_apply,
          ContinuousMap.smul_apply, ContinuousMap.coe_mk, eval_add, eval_smul, smul_eq_mul]
        ring_nf
      have hlt : ‖f - polynomialOnApproximationInterval (p + ε • q)‖ <
          ‖f - polynomialOnApproximationInterval p‖ := by
        simpa [hmap, e] using hεnorm
      exact (not_lt_of_ge (hp.2 (p + ε • q) hdeg) hlt).elim

/-- Two best approximations of degree at most `n` are the same polynomial. -/
lemma eq_of_isBestPolynomialApproximation (f : ApproximationIntervalMap) (n : ℕ)
    (p q : ℝ[X]) (hp : IsBestPolynomialApproximation f n p)
    (hq : IsBestPolynomialApproximation f n q) : p = q := by
  have hEq : ‖f - polynomialOnApproximationInterval p‖ =
      ‖f - polynomialOnApproximationInterval q‖ :=
    le_antisymm (hp.2 q hq.1) (hq.2 p hp.1)
  let r : ℝ[X] := (1 / 2 : ℝ) • (p + q)
  have hrdeg : r.natDegree ≤ n :=
    (natDegree_smul_le _ _).trans ((natDegree_add_le _ _).trans (max_le hp.1 hq.1))
  have herr : f - polynomialOnApproximationInterval r =
      (1 / 2 : ℝ) • ((f - polynomialOnApproximationInterval p) +
        (f - polynomialOnApproximationInterval q)) := by
    ext x
    simp only [r, polynomialOnApproximationInterval, ContinuousMap.sub_apply,
      ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.coe_mk,
      eval_smul, eval_add, smul_eq_mul]
    ring_nf
  have hle : ‖f - polynomialOnApproximationInterval r‖ ≤
      ‖f - polynomialOnApproximationInterval p‖ := by
    rw [herr]
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 ?_
    intro x
    rw [ContinuousMap.smul_apply, ContinuousMap.add_apply, smul_eq_mul, Real.norm_eq_abs]
    have hu := (f - polynomialOnApproximationInterval p).norm_coe_le_norm x
    have hv := (f - polynomialOnApproximationInterval q).norm_coe_le_norm x
    rw [Real.norm_eq_abs] at hu hv
    rw [← hEq] at hv
    have habs : |(1 / 2 : ℝ) * ((f - polynomialOnApproximationInterval p) x +
        (f - polynomialOnApproximationInterval q) x)| ≤
        (1 / 2) * (|(f - polynomialOnApproximationInterval p) x| +
          |(f - polynomialOnApproximationInterval q) x|) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    linarith
  have heqr : ‖f - polynomialOnApproximationInterval r‖ =
      ‖f - polynomialOnApproximationInterval p‖ :=
    le_antisymm hle (hp.2 r hrdeg)
  have hrbest : IsBestPolynomialApproximation f n r :=
    ⟨hrdeg, fun s hs => by simpa [heqr] using hp.2 s hs⟩
  obtain ⟨x, hxmono, σ, hσ, hx⟩ :=
    hasPolynomialAlternation_of_isBestPolynomialApproximation f n r hrbest
  set E : ℝ := ‖f - polynomialOnApproximationInterval r‖
  have hagree : ∀ i : Fin (n + 2), (p - q).eval (x i).1 = 0 := by
    intro i
    have hres : (f - polynomialOnApproximationInterval r) (x i) = σ * (-1) ^ i.val * E := by
      simpa [E, sub_apply, polynomialOnApproximationInterval] using hx i
    have havg : ((f - polynomialOnApproximationInterval p) (x i) +
        (f - polynomialOnApproximationInterval q) (x i)) / 2 =
        (f - polynomialOnApproximationInterval r) (x i) := by
      have h := congrArg (fun g : ApproximationIntervalMap => g (x i)) herr
      rw [ContinuousMap.smul_apply, ContinuousMap.add_apply, smul_eq_mul] at h
      linarith
    have ha : |(f - polynomialOnApproximationInterval p) (x i)| ≤ E := by
      have h := (f - polynomialOnApproximationInterval p).norm_coe_le_norm (x i)
      rw [Real.norm_eq_abs] at h
      simpa [E, heqr] using h
    have hb : |(f - polynomialOnApproximationInterval q) (x i)| ≤ E := by
      have hnorm : ‖f - polynomialOnApproximationInterval q‖ = E := by rw [← hEq, ← heqr]
      have h := (f - polynomialOnApproximationInterval q).norm_coe_le_norm (x i)
      rw [Real.norm_eq_abs] at h
      simpa [hnorm] using h
    obtain ⟨haE, hbE⟩ := eq_of_avg_endpoint ha hb (abs_alternationSign hσ i.val) (by
      rw [havg, hres])
    have hpq : p.eval (x i).1 = q.eval (x i).1 := by
      have haq : (f - polynomialOnApproximationInterval p) (x i) =
          (f - polynomialOnApproximationInterval q) (x i) := by rw [haE, hbE]
      rw [ContinuousMap.sub_apply, ContinuousMap.sub_apply] at haq
      simp only [polynomialOnApproximationInterval, ContinuousMap.coe_mk] at haq
      linarith
    rw [eval_sub, hpq, sub_self]
  have hinj : Function.Injective (fun i : Fin (n + 2) => (x i).1) := hxmono.injective
  have hdeg : (p - q).natDegree < Fintype.card (Fin (n + 2)) := by
    have hle : (p - q).natDegree ≤ n := (natDegree_sub_le p q).trans (max_le hp.1 hq.1)
    have hlt : (p - q).natDegree < n + 2 := by omega
    simpa [Fintype.card_fin] using hlt
  exact sub_eq_zero.mp
    (eq_zero_of_natDegree_lt_card_of_eval_eq_zero (p - q) hinj hagree hdeg)

/-- Finite-dimensional polynomial approximation has a unique uniform minimizer. -/
theorem existsUnique_bestPolynomialApproximation (f : ApproximationIntervalMap) (n : ℕ) :
    ∃! p : ℝ[X], IsBestPolynomialApproximation f n p := by
  obtain ⟨p, hp⟩ := exists_isBestPolynomialApproximation f n
  exact ⟨p, hp, fun q hq => (eq_of_isBestPolynomialApproximation f n p q hp hq).symm⟩

/-- **47.6**: Chebyshev's alternation criterion on `[-1,1]`.
The generalized Haar-space criterion is a separate target. -/
theorem isBestPolynomialApproximation_iff_alternation (f : ApproximationIntervalMap)
    (n : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ n) :
    IsBestPolynomialApproximation f n p ↔ HasPolynomialAlternation f p n := by
  constructor
  · intro h
    exact hasPolynomialAlternation_of_isBestPolynomialApproximation f n p h
  · intro h
    exact isBestPolynomialApproximation_of_hasPolynomialAlternation f n p hp h

/-- Polynomial approximation errors are nonnegative. -/
theorem bestPolynomialError_nonneg (f : ApproximationIntervalMap) (n : ℕ) :
    0 ≤ bestPolynomialError f n := by
  apply le_csInf
  · exact ⟨‖f - polynomialOnApproximationInterval 0‖, 0, by simp, rfl⟩
  · rintro r ⟨p, hp, rfl⟩
    exact norm_nonneg _

/-- Any admissible polynomial gives an upper bound on best approximation error. -/
theorem bestPolynomialError_le (f : ApproximationIntervalMap) (n : ℕ) (p : ℝ[X])
    (hp : p.natDegree ≤ n) : bestPolynomialError f n ≤ ‖f - polynomialOnApproximationInterval p‖ :=
      by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨q, hq, rfl⟩
    exact norm_nonneg _
  · exact ⟨p, hp, rfl⟩

/-- Increasing the admissible polynomial degree cannot increase best approximation error. -/
theorem bestPolynomialError_antitone (f : ApproximationIntervalMap) :
    Antitone (bestPolynomialError f) := by
  intro m n hmn
  apply le_csInf
  · exact ⟨‖f - polynomialOnApproximationInterval 0‖, 0, by simp, rfl⟩
  · rintro r ⟨p, hp, rfl⟩
    exact bestPolynomialError_le f n p (hp.trans hmn)

/-- **47.24**: Markov's sharp first-derivative bound, including interior points. -/
theorem polynomial_markov {n : ℕ} (p : ℝ[X]) (hp : p.natDegree ≤ n)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |p.derivative.eval x| ≤ (n : ℝ) ^ 2 * ‖polynomialOnApproximationInterval p‖ := by
  sorry

/-- The `n²` Markov constant is attained by a nonzero polynomial of degree `n`. -/
theorem polynomial_markov_sharp (n : ℕ) : ∃ p : ℝ[X], p.natDegree = n ∧ p ≠ 0 ∧
    ‖polynomialOnApproximationInterval p.derivative‖ =
      (n : ℝ) ^ 2 * ‖polynomialOnApproximationInterval p‖ := by
  sorry

/-- A nonnegative real power as a continuous function on `[0,1]`. -/
def muntzMonomial (a : ℝ) (ha : 0 ≤ a) : C(Set.Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun x ↦ x.1 ^ a, (Real.continuous_rpow_const ha).comp continuous_subtype_val⟩

/-- The Müntz span includes the constant function as well as all prescribed powers. -/
def muntzSpan (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) :
    Submodule ℝ C(Set.Icc (0 : ℝ) 1, ℝ) :=
  Submodule.span ℝ (insert 1 (Set.range (fun n ↦ muntzMonomial (a n) (ha n))))

/-- **47.13**: Müntz–Szász for strictly increasing positive exponents tending to infinity.
Nonsummability of the positive reciprocal sequence expresses divergence to `+∞`. -/
theorem muntz_szasz (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (hmono : StrictMono a)
    (hlim : Tendsto a atTop atTop) :
    Dense (muntzSpan a (fun n ↦ (ha n).le) : Set C(Set.Icc (0 : ℝ) 1, ℝ)) ↔
      ¬ Summable (fun n ↦ (a n)⁻¹) := by
  sorry

/-- A rational function on the interval whose denominator has no interval zeros. -/
def rationalOnApproximationInterval (p q : ℝ[X])
    (hq : ∀ x : Set.Icc (-1 : ℝ) 1, q.eval x.1 ≠ 0) : ApproximationIntervalMap :=
  ⟨fun x ↦ p.eval x.1 / q.eval x.1,
    (p.continuous.comp continuous_subtype_val).div
      (q.continuous.comp continuous_subtype_val) hq⟩

/-- Best type-`(n,n)` rational approximation error, with poles excluded from the interval. -/
def bestRationalError (f : ApproximationIntervalMap) (n : ℕ) : ℝ :=
  sInf {r | ∃ (p q : ℝ[X]) (hq : ∀ x : Set.Icc (-1 : ℝ) 1, q.eval x.1 ≠ 0),
    p.natDegree ≤ n ∧ q.natDegree ≤ n ∧ r = ‖f - rationalOnApproximationInterval p q hq‖}

/-- The cusp function used in Newman's theorem. -/
def absoluteValueOnApproximationInterval : ApproximationIntervalMap :=
  ⟨fun x ↦ |x.1|, continuous_subtype_val.abs⟩

/-- **47.40**: root-exponential two-sided rational approximation rates for `|x|`. -/
theorem newman_rational_approximation : ∃ c₁ c₂ c₃ c₄ : ℝ,
    0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < c₄ ∧ ∀ n : ℕ, 0 < n →
      c₁ * Real.exp (-c₂ * Real.sqrt n) ≤
        bestRationalError absoluteValueOnApproximationInterval n ∧
      bestRationalError absoluteValueOnApproximationInterval n ≤
        c₃ * Real.exp (-c₄ * Real.sqrt n) := by
  sorry

/-- The polynomial approximation rate for the same cusp is only of order `1/n`. -/
theorem absoluteValue_polynomial_approximation : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ n : ℕ, 0 < n → c / n ≤ bestPolynomialError absoluteValueOnApproximationInterval n ∧
      bestPolynomialError absoluteValueOnApproximationInterval n ≤ C / n := by
  sorry

end CKMA
