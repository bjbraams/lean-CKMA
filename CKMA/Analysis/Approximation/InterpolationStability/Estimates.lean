/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Approximation.InterpolationStability.Basic

import CKMA.Analysis.Approximation.InterpolationStability.ElementaryBounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Chebyshev-extrema nodal estimates

The nodal polynomial, the angular formula for the cardinal polynomials, and the endpoint
correction for the Lebesgue function of the Chebyshev extrema. The elementary real bounds used
here are in `CKMA.Analysis.Approximation.InterpolationStability.ElementaryBounds`. These
estimates feed the logarithmic bound on the Lebesgue constant.

## Main definitions

* `CKMA.chebyshevAngleSign`: sign of an off-node angle relative to a node angle.
* `CKMA.chebyshevLebesgueMain`: cotangent main term in the angular formula for a cardinal
  polynomial.
* `CKMA.chebyshevLebesgueCorrection`: cotangent correction term in the angular formula for a
  cardinal polynomial.

## Main results

* `CKMA.lebesgueFunction_cos_eq`: off the nodes, the Lebesgue function is the sum of main and
  correction terms.
* `CKMA.sum_chebyshevLebesgueMain_le`: sum of the cotangent main terms compared with
  `(2 / π) log (n + 1)`.
* `CKMA.chebyshevAngleSign_def`, `CKMA.chebyshevLebesgueMain_def`,
  `CKMA.chebyshevLebesgueCorrection_def`: defining lemmas.
* `CKMA.chebyshevLebesgueCorrection_zero_le`, `CKMA.chebyshevLebesgueCorrection_last_le`:
  endpoint correction estimates on `(0, π / 2]`.
-/

public section

noncomputable section

namespace CKMA

open Polynomial Real Polynomial.Chebyshev Finset Lagrange
open scoped BigOperators

/-- The nodal polynomial vanishes at every extremal node. -/
private lemma isRoot_chebyshevExtremalNodal {n : ℕ} (hn : 1 ≤ n) (i : Fin (n + 1)) :
    IsRoot (chebyshevExtremalNodal n) (chebyshevExtremalNodes n i) := by
  rw [IsRoot.def, chebyshevExtremalNodes_eq_cos, eval_chebyshevExtremalNodal hn]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hangle : (n : ℝ) * chebyshevNodeAngle n i = (i.val : ℝ) * π := by
    unfold chebyshevNodeAngle
    field_simp
  rw [hangle, sin_nat_mul_pi, mul_zero]

/-- Division by a simple nodal factor reproduces the derivative at the root. -/
private lemma eval_divByMonic_derivative (φ : ℝ[X]) (a : ℝ) (ha : IsRoot φ a) :
    (φ.divByMonic (X - C a)).eval a = φ.derivative.eval a := by
  have hmul : (X - C a) * φ.divByMonic (X - C a) = φ :=
    (mul_divByMonic_eq_iff_isRoot).2 ha
  have hder := congrArg derivative hmul
  rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul] at hder
  have heval := congrArg (eval a) hder
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul,
    add_zero] at heval
  exact heval

/-- Cardinal polynomials are the scaled monic quotients of the nodal polynomial. -/
private lemma lagrangeCardinal_eq_scaled_divByMonic {n : ℕ} (hn : 1 ≤ n)
    (i : Fin (n + 1)) :
    lagrangeCardinalPolynomial (chebyshevExtremalNodes n) i =
      C (1 / (chebyshevExtremalNodal n).derivative.eval (chebyshevExtremalNodes n i)) *
        (chebyshevExtremalNodal n).divByMonic
          (X - C (chebyshevExtremalNodes n i)) := by
  let x := chebyshevExtremalNodes n
  let φ := chebyshevExtremalNodal n
  let a := x i
  have hvs : Set.InjOn x (univ : Finset (Fin (n + 1))) :=
    (chebyshevExtremalNodes_injective (by omega)).injOn
  have hroot : IsRoot φ a := isRoot_chebyshevExtremalNodal hn i
  have hne : φ.derivative.eval a ≠ 0 := by
    intro hzero
    have habs := abs_derivative_chebyshevExtremalNodal hn i
    rw [hzero, abs_zero] at habs
    have hpos : (0 : ℝ) < (n : ℝ) * chebyshevExtremalWeight n i :=
      mul_pos (by exact_mod_cast (by omega : 0 < n)) (chebyshevExtremalWeight_pos n i)
    linarith
  let q0 := φ.divByMonic (X - C a)
  let q := C (1 / φ.derivative.eval a) * q0
  have hprod : (X - C a) * q0 = φ := (mul_divByMonic_eq_iff_isRoot).2 hroot
  have hq0ne : q0 ≠ 0 := by
    intro hq
    have hφ : φ = 0 := by simpa [q0, hq] using hprod.symm
    have hdeg : φ.natDegree = n + 1 := natDegree_chebyshevExtremalNodal hn
    rw [hφ, natDegree_zero] at hdeg
    omega
  have hnat : q0.natDegree = n := by
    have hmul := natDegree_mul' (p := X - C a) (q := q0)
      (mul_ne_zero (by simp [leadingCoeff_X_sub_C]) (leadingCoeff_ne_zero.mpr hq0ne))
    rw [hprod, natDegree_X_sub_C, natDegree_chebyshevExtremalNodal hn] at hmul
    omega
  let r : Fin (n + 1) → ℝ := fun j => if j = i then 1 else 0
  have hdegq : q.degree < #(univ : Finset (Fin (n + 1))) := by
    rw [Finset.card_univ, Fintype.card_fin]
    have hle : q.natDegree ≤ n := by
      calc q.natDegree ≤ q0.natDegree := natDegree_C_mul_le _ _
        _ = n := hnat
    have : q.degree ≤ (n : WithBot ℕ) :=
      degree_le_natDegree.trans (WithBot.coe_le_coe.mpr hle)
    exact this.trans_lt (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self n))
  have hq0a : q0.eval a = φ.derivative.eval a := eval_divByMonic_derivative φ a hroot
  have hqeval : ∀ j ∈ (univ : Finset (Fin (n + 1))), q.eval (x j) = r j := by
    intro j _
    by_cases hji : j = i
    · rw [hji]
      simp only [q, eval_mul, eval_C]
      rw [show x i = a from rfl, hq0a]
      field_simp [hne]
      simp [r]
    · have hrootj : φ.eval (x j) = 0 := isRoot_chebyshevExtremalNodal hn j
      have hdiff : x j - a ≠ 0 := by
        intro h
        exact hji ((chebyshevExtremalNodes_injective (by omega)) (sub_eq_zero.mp h))
      have heq : (x j - a) * q0.eval (x j) = φ.eval (x j) := by
        have := congrArg (eval (x j)) hprod
        simpa [q0, eval_mul, eval_sub, eval_X, eval_C] using this
      have heq0 : (x j - a) * q0.eval (x j) = 0 := by simpa [hrootj] using heq
      have hqj : q0.eval (x j) = 0 := (mul_eq_zero.mp heq0).resolve_left hdiff
      simp [q, r, hji, eval_mul, eval_C, hqj]
  have hdegB : (lagrangeCardinalPolynomial x i).degree <
      #(univ : Finset (Fin (n + 1))) := by
    rw [degree_basis hvs (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    exact WithBot.coe_lt_coe.mpr (Nat.sub_lt (Nat.succ_pos n) zero_lt_one)
  have hbasis : lagrangeCardinalPolynomial x i = Lagrange.interpolate univ x r := by
    refine eq_interpolate_of_eval_eq _ hvs hdegB ?_
    intro j _
    by_cases hji : j = i
    · rw [hji, lagrangeCardinalPolynomial, eval_basis_self hvs (Finset.mem_univ i)]
      simp [r]
    · rw [lagrangeCardinalPolynomial, eval_basis_of_ne (Ne.symm hji) (Finset.mem_univ j)]
      simp [r, hji]
  have hqint : q = Lagrange.interpolate univ x r :=
    eq_interpolate_of_eval_eq _ hvs hdegq hqeval
  simpa [q, q0, a, φ, x] using hbasis.trans hqint.symm

/-- Absolute cardinal value away from its node, in terms of the nodal polynomial. -/
private lemma abs_eval_cardinal_div {n : ℕ} (hn : 1 ≤ n) (i : Fin (n + 1)) {t : ℝ}
    (ht : t ≠ chebyshevExtremalNodes n i) :
    |(lagrangeCardinalPolynomial (chebyshevExtremalNodes n) i).eval t| =
      |(chebyshevExtremalNodal n).eval t| /
        (|t - chebyshevExtremalNodes n i| *
          |(chebyshevExtremalNodal n).derivative.eval (chebyshevExtremalNodes n i)|) := by
  let φ := chebyshevExtremalNodal n
  let a := chebyshevExtremalNodes n i
  let q0 := φ.divByMonic (X - C a)
  have hroot : IsRoot φ a := isRoot_chebyshevExtremalNodal hn i
  have hprod : (X - C a) * q0 = φ := (mul_divByMonic_eq_iff_isRoot).2 hroot
  have hdiv : (t - a) * q0.eval t = φ.eval t := by
    have := congrArg (eval t) hprod
    simpa [q0, eval_mul, eval_sub, eval_X, eval_C] using this
  have hq0 : q0.eval t = φ.eval t / (t - a) := by
    rw [eq_div_iff (sub_ne_zero.mpr ht), mul_comm]
    exact hdiv
  have hden : φ.derivative.eval a ≠ 0 := by
    intro hzero
    have habs := abs_derivative_chebyshevExtremalNodal hn i
    rw [hzero, abs_zero] at habs
    have hpos : (0 : ℝ) < (n : ℝ) * chebyshevExtremalWeight n i :=
      mul_pos (by exact_mod_cast (by omega : 0 < n)) (chebyshevExtremalWeight_pos n i)
    linarith
  rw [lagrangeCardinal_eq_scaled_divByMonic hn i]
  simp only [eval_mul, eval_C]
  rw [hq0, abs_mul, abs_div, abs_one, abs_div]
  have habsφ' : |φ.derivative.eval a| ≠ 0 := abs_ne_zero.mpr hden
  have habst : |t - a| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr ht)
  field_simp [habsφ', habst]
  ring

/-- Reflected cardinal polynomials are the originals composed with `-X`. -/
private lemma cardinal_comp_neg {n : ℕ} (hn : 1 ≤ n) (i : Fin (n + 1)) :
    (lagrangeCardinalPolynomial (chebyshevExtremalNodes n) i).comp (-X) =
      lagrangeCardinalPolynomial (chebyshevExtremalNodes n) i.rev := by
  let x := chebyshevExtremalNodes n
  have hvs : Set.InjOn x (univ : Finset (Fin (n + 1))) :=
    (chebyshevExtremalNodes_injective (by omega)).injOn
  let p := (lagrangeCardinalPolynomial x i).comp (-X)
  let target := lagrangeCardinalPolynomial x i.rev
  have hdegP : p.degree < #(univ : Finset (Fin (n + 1))) := by
    rw [degree_comp_neg_X, degree_basis hvs (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
    exact WithBot.coe_lt_coe.mpr (Nat.sub_lt (Nat.succ_pos n) zero_lt_one)
  have hdegT : target.degree < #(univ : Finset (Fin (n + 1))) := by
    rw [degree_basis hvs (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    exact WithBot.coe_lt_coe.mpr (Nat.sub_lt (Nat.succ_pos n) zero_lt_one)
  have hval : ∀ j ∈ (univ : Finset (Fin (n + 1))), p.eval (x j) = target.eval (x j) := by
    intro j _
    rw [eval_comp]
    have hnegX : (-X).eval (x j) = -x j := by simp
    rw [hnegX]
    have hneg : -x j = x j.rev :=
      (chebyshevExtremalNodes_rev (by omega) j).symm
    rw [hneg]
    by_cases hji : j.rev = i
    · have hj : j = i.rev := by
        apply_fun Fin.rev at hji
        simpa using hji
      simp [hj, target, lagrangeCardinalPolynomial,
        eval_basis_self hvs (Finset.mem_univ _)]
    · have hjr : j ≠ i.rev := by
        intro hj
        apply hji
        simp [hj]
      rw [eval_basis_of_ne (Ne.symm hji) (Finset.mem_univ _),
        eval_basis_of_ne (Ne.symm hjr) (Finset.mem_univ _)]
  have htarg : target = Lagrange.interpolate univ x (fun j => target.eval (x j)) :=
    eq_interpolate hvs hdegT
  have hp : p = Lagrange.interpolate univ x (fun j => target.eval (x j)) :=
    eq_interpolate_of_eval_eq _ hvs hdegP hval
  simpa [p, target, x] using hp.trans htarg.symm

/-- The extremal Lebesgue function is even. -/
lemma lebesgueFunction_neg {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    lebesgueFunction (chebyshevExtremalNodes n) (-t) =
      lebesgueFunction (chebyshevExtremalNodes n) t := by
  unfold lebesgueFunction
  refine Finset.sum_nbij' (s := univ) (t := univ) Fin.rev Fin.rev
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)
    (fun a _ => Fin.rev_rev a) (fun a _ => Fin.rev_rev a) ?_
  intro i _
  rw [← cardinal_comp_neg hn i, eval_comp]
  simp

/-- Sign of an off-node angle relative to a node angle. -/
@[expose]
def chebyshevAngleSign (n : ℕ) (θ : ℝ) (i : Fin (n + 1)) : ℝ :=
  if chebyshevNodeAngle n i < θ then 1 else -1

/-- Cotangent main term in the angular formula for a cardinal polynomial. -/
@[expose]
def chebyshevLebesgueMain (n : ℕ) (θ : ℝ) (i : Fin (n + 1)) : ℝ :=
  |sin ((n : ℝ) * θ)| / (2 * (n : ℝ) * chebyshevExtremalWeight n i) *
    cot (|θ - chebyshevNodeAngle n i| / 2)

/-- Cotangent correction in the angular formula for a cardinal polynomial. -/
@[expose]
def chebyshevLebesgueCorrection (n : ℕ) (θ : ℝ) (i : Fin (n + 1)) : ℝ :=
  |sin ((n : ℝ) * θ)| / (2 * (n : ℝ) * chebyshevExtremalWeight n i) *
    chebyshevAngleSign n θ i * cot ((θ + chebyshevNodeAngle n i) / 2)

/-- The angle sign is `1` when the node angle lies to the left of `θ`, and `-1` otherwise. -/
lemma chebyshevAngleSign_def (n : ℕ) (θ : ℝ) (i : Fin (n + 1)) :
    chebyshevAngleSign n θ i = if chebyshevNodeAngle n i < θ then 1 else -1 :=
  rfl

/-- The cotangent main term. -/
lemma chebyshevLebesgueMain_def (n : ℕ) (θ : ℝ) (i : Fin (n + 1)) :
    chebyshevLebesgueMain n θ i =
      |sin ((n : ℝ) * θ)| / (2 * (n : ℝ) * chebyshevExtremalWeight n i) *
        cot (|θ - chebyshevNodeAngle n i| / 2) :=
  rfl

/-- The cotangent correction term. -/
lemma chebyshevLebesgueCorrection_def (n : ℕ) (θ : ℝ) (i : Fin (n + 1)) :
    chebyshevLebesgueCorrection n θ i =
      |sin ((n : ℝ) * θ)| / (2 * (n : ℝ) * chebyshevExtremalWeight n i) *
        chebyshevAngleSign n θ i * cot ((θ + chebyshevNodeAngle n i) / 2) :=
  rfl

/-- Cosine difference in product form. -/
private lemma abs_cos_sub_cos (θ φ : ℝ) :
    |cos θ - cos φ| = 2 * |sin ((θ + φ) / 2)| * |sin ((θ - φ) / 2)| := by
  rw [Real.cos_sub_cos, abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

/-- Absolute sine is unchanged by replacing an angle with its absolute value. -/
private lemma abs_sin_div_two_abs (δ : ℝ) : |sin (δ / 2)| = |sin (|δ| / 2)| := by
  rcases le_or_gt 0 δ with hδ | hδ
  · rw [abs_of_nonneg hδ]
  · rw [abs_of_neg hδ, neg_div, sin_neg, abs_neg]

/-- Half-angle gap between an interior angle and a node angle. -/
private lemma nodeGap_mem_Ioo {θ φ : ℝ} (hθ : θ ∈ Set.Ioo 0 π) (hφ : φ ∈ Set.Icc 0 π)
    (hne : θ ≠ φ) : |θ - φ| / 2 ∈ Set.Ioo 0 (π / 2) := by
  have hlt : |θ - φ| < π := by
    have hmax : |θ - φ| ≤ max θ (π - θ) := by
      rcases le_or_gt φ θ with h | h
      · rw [abs_of_nonneg (sub_nonneg.mpr h)]
        have hφ0 : 0 ≤ φ := hφ.1
        have : θ - φ ≤ θ := by linarith
        exact le_trans this (le_max_left _ _)
      · rw [abs_of_neg (sub_neg.mpr h)]
        have : -(θ - φ) ≤ π - θ := by linarith [hφ.2]
        exact le_trans this (le_max_right _ _)
    have hstrict : max θ (π - θ) < π := by
      apply max_lt
      · exact hθ.2
      · linarith [hθ.1]
    exact lt_of_le_of_lt hmax hstrict
  refine ⟨div_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) (by norm_num), ?_⟩
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- Average of an interior angle and a node angle stays inside `(0, π)`. -/
private lemma nodeAverage_mem_Ioo {θ φ : ℝ} (hθ : θ ∈ Set.Ioo 0 π) (hφ : φ ∈ Set.Icc 0 π) :
    (θ + φ) / 2 ∈ Set.Ioo 0 π := by
  refine ⟨div_pos (by linarith [hθ.1, hφ.1]) (by norm_num), ?_⟩
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith [hθ.2, hφ.2]

/-- Sine quotient that splits a cardinal factor into cotangent terms. -/
private lemma sin_div_gap {θ φ : ℝ} (hθ : θ ∈ Set.Ioo 0 π) (hφ : φ ∈ Set.Icc 0 π)
    (hne : θ ≠ φ) :
    sin θ / (sin (|θ - φ| / 2) * sin ((θ + φ) / 2)) =
      cot (|θ - φ| / 2) + (if φ < θ then (1 : ℝ) else -1) * cot ((θ + φ) / 2) := by
  set u : ℝ := |θ - φ| / 2
  set avg : ℝ := (θ + φ) / 2
  have hu := nodeGap_mem_Ioo hθ hφ hne
  have havg := nodeAverage_mem_Ioo hθ hφ
  have hsinu : 0 < sin u := sin_pos_of_pos_of_lt_pi hu.1 (hu.2.trans (by linarith [pi_pos]))
  have hsinavg : 0 < sin avg := sin_pos_of_pos_of_lt_pi havg.1 havg.2
  by_cases hlt : φ < θ
  · have huθ : u = (θ - φ) / 2 := by
      simp [u, abs_of_nonneg (sub_nonneg.mpr hlt.le)]
    have hsum : avg + u = θ := by
      simp only [avg, u, huθ]
      ring
    have hsin : sin θ = sin avg * cos u + cos avg * sin u := by
      rw [← hsum, sin_add]
    rw [hsin, ite_eq_left hlt, cot_eq_cos_div_sin, cot_eq_cos_div_sin]
    field_simp [hsinu.ne', hsinavg.ne']
  · have hgt : θ < φ := lt_of_le_of_ne (le_of_not_gt hlt) hne
    have huθ : u = (φ - θ) / 2 := by
      simp [u, abs_of_neg (sub_neg.mpr hgt)]
    have hsum : avg - u = θ := by
      simp only [avg, u, huθ]
      ring
    have hsin : sin θ = sin avg * cos u - cos avg * sin u := by
      rw [← hsum, sin_sub]
    rw [hsin, ite_eq_right hlt, cot_eq_cos_div_sin, cot_eq_cos_div_sin]
    field_simp [hsinu.ne', hsinavg.ne']
    ring

/-- Off a node, each cardinal polynomial is the sum of its main and correction terms. -/
private lemma abs_cardinal_eq_main_add_corr {n : ℕ} (hn : 1 ≤ n) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 π) (hnode : ∀ i, θ ≠ chebyshevNodeAngle n i) (i : Fin (n + 1)) :
    |(lagrangeCardinalPolynomial (chebyshevExtremalNodes n) i).eval (cos θ)| =
      chebyshevLebesgueMain n θ i + chebyshevLebesgueCorrection n θ i := by
  have hn0 : n ≠ 0 := by omega
  have hφmem : chebyshevNodeAngle n i ∈ Set.Icc 0 π := chebyshevNodeAngle_mem_Icc hn0 i
  have hne : θ ≠ chebyshevNodeAngle n i := hnode i
  have hcosne : cos θ ≠ chebyshevExtremalNodes n i := by
    rw [chebyshevExtremalNodes_eq_cos]
    intro h
    exact hne ((strictAntiOn_cos.injOn.eq_iff ⟨hθ.1.le, hθ.2.le⟩ hφmem).mp h)
  have habs := abs_eval_cardinal_div hn i hcosne
  have heval : |(chebyshevExtremalNodal n).eval (cos θ)| =
      |sin θ| * |sin ((n : ℝ) * θ)| := by
    rw [eval_chebyshevExtremalNodal hn, abs_mul]
  have hder := abs_derivative_chebyshevExtremalNodal hn i
  have hdiff := abs_cos_sub_cos θ (chebyshevNodeAngle n i)
  have hsinθ : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hu := nodeGap_mem_Ioo hθ hφmem hne
  have havg := nodeAverage_mem_Ioo hθ hφmem
  have hsinu : 0 < sin (|θ - chebyshevNodeAngle n i| / 2) :=
    sin_pos_of_pos_of_lt_pi hu.1 (hu.2.trans (by linarith [pi_pos]))
  have hsinavg : 0 < sin ((θ + chebyshevNodeAngle n i) / 2) :=
    sin_pos_of_pos_of_lt_pi havg.1 havg.2
  have hweight : 0 < chebyshevExtremalWeight n i := chebyshevExtremalWeight_pos n i
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsplit := sin_div_gap hθ hφmem hne
  rw [habs, heval, hder, chebyshevExtremalNodes_eq_cos, hdiff, abs_of_pos hsinθ]
  rw [abs_sin_div_two_abs (θ - chebyshevNodeAngle n i), abs_of_pos hsinu, abs_of_pos hsinavg]
  unfold chebyshevLebesgueMain chebyshevLebesgueCorrection chebyshevAngleSign
  have hcomm : sin θ / (sin ((θ + chebyshevNodeAngle n i) / 2) *
      sin (|θ - chebyshevNodeAngle n i| / 2)) =
      cot (|θ - chebyshevNodeAngle n i| / 2) +
        (if chebyshevNodeAngle n i < θ then (1 : ℝ) else -1) *
          cot ((θ + chebyshevNodeAngle n i) / 2) := by
    rw [mul_comm]
    exact hsplit
  calc
      sin θ * |sin ((n : ℝ) * θ)| /
          (2 * sin ((θ + chebyshevNodeAngle n i) / 2) * sin (|θ - chebyshevNodeAngle n i| / 2) *
            ((n : ℝ) * chebyshevExtremalWeight n i))
        = |sin ((n : ℝ) * θ)| / (2 * (n : ℝ) * chebyshevExtremalWeight n i) *
            (sin θ / (sin ((θ + chebyshevNodeAngle n i) / 2) *
              sin (|θ - chebyshevNodeAngle n i| / 2))) := by
          field_simp [hsinu.ne', hsinavg.ne', hweight.ne', hnpos.ne']
    _ = |sin ((n : ℝ) * θ)| / (2 * (n : ℝ) * chebyshevExtremalWeight n i) *
          (cot (|θ - chebyshevNodeAngle n i| / 2) +
            (if chebyshevNodeAngle n i < θ then (1 : ℝ) else -1) *
              cot ((θ + chebyshevNodeAngle n i) / 2)) := by
        rw [hcomm]
    _ = |sin ((n : ℝ) * θ)| / (2 * (n : ℝ) * chebyshevExtremalWeight n i) *
          cot (|θ - chebyshevNodeAngle n i| / 2) +
        (|sin ((n : ℝ) * θ)| / (2 * (n : ℝ) * chebyshevExtremalWeight n i) *
          (if chebyshevNodeAngle n i < θ then (1 : ℝ) else -1)) *
          cot ((θ + chebyshevNodeAngle n i) / 2) := by ring

/-- Single-term upper bound for the cotangent main term. -/
private lemma chebyshevLebesgueMain_le_sin_div {n : ℕ} (hn : 1 ≤ n) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 π) (hnode : ∀ i, θ ≠ chebyshevNodeAngle n i) (i : Fin (n + 1)) :
    chebyshevLebesgueMain n θ i ≤
      |sin ((n : ℝ) * θ)| / (π * |(i.val : ℝ) - (n : ℝ) * θ / π|) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnpos : (n : ℝ) ≠ 0 := hn0.ne'
  let ν : ℝ := (n : ℝ) * θ / π
  have hφ : chebyshevNodeAngle n i ∈ Set.Icc 0 π := chebyshevNodeAngle_mem_Icc (by omega) i
  have hneθ : θ ≠ chebyshevNodeAngle n i := hnode i
  have hu := nodeGap_mem_Ioo hθ hφ hneθ
  have hαpos := chebyshevExtremalWeight_pos n i
  have hα1 := one_le_chebyshevExtremalWeight n i
  have hdpos : 0 < |(i.val : ℝ) - ν| := by
    rw [abs_pos]
    intro hzero
    have hθeq : θ = chebyshevNodeAngle n i := by
      have hiν : (i.val : ℝ) = ν := by linarith
      unfold chebyshevNodeAngle
      rw [hiν, show ν = (n : ℝ) * θ / π from rfl]
      field_simp
    exact hneθ hθeq
  have hgap : |θ - chebyshevNodeAngle n i| = π * |(i.val : ℝ) - ν| / n := by
    have hθv : θ = π * ν / n := by
      unfold ν
      field_simp
    rw [hθv, chebyshevNodeAngle]
    have hsub : π * ν / n - π * (i.val : ℝ) / n =
        π * (ν - (i.val : ℝ)) / n := by
      field_simp
    rw [hsub, abs_div, abs_mul, abs_of_pos pi_pos, abs_of_pos hn0, abs_sub_comm]
  have hu_eq : |θ - chebyshevNodeAngle n i| / 2 =
      π * |(i.val : ℝ) - ν| / (2 * n) := by
    rw [hgap]
    ring
  have hcot := cot_le_one_div hu
  have hfac : 0 ≤ |sin ((n : ℝ) * θ)| /
      (2 * (n : ℝ) * chebyshevExtremalWeight n i) := by
    positivity
  calc chebyshevLebesgueMain n θ i
      = |sin ((n : ℝ) * θ)| /
          (2 * (n : ℝ) * chebyshevExtremalWeight n i) *
          cot (|θ - chebyshevNodeAngle n i| / 2) := rfl
    _ ≤ |sin ((n : ℝ) * θ)| /
          (2 * (n : ℝ) * chebyshevExtremalWeight n i) *
          (1 / (|θ - chebyshevNodeAngle n i| / 2)) :=
        mul_le_mul_of_nonneg_left hcot hfac
    _ = |sin ((n : ℝ) * θ)| /
          (chebyshevExtremalWeight n i * π * |(i.val : ℝ) - ν|) := by
        rw [hu_eq]
        field_simp [hαpos.ne', hnpos, hdpos.ne', pi_ne_zero]
    _ ≤ |sin ((n : ℝ) * θ)| / (π * |(i.val : ℝ) - ν|) := by
        have hc : 0 < π * |(i.val : ℝ) - ν| := mul_pos pi_pos hdpos
        have hden : π * |(i.val : ℝ) - ν| ≤
            chebyshevExtremalWeight n i * π * |(i.val : ℝ) - ν| := by
          have hmul := mul_le_mul_of_nonneg_right hα1 hc.le
          rwa [one_mul, ← mul_assoc] at hmul
        exact div_le_div_of_nonneg_left (abs_nonneg _) hc hden

/-- Left-tail harmonic upper bound for the main-term sum. -/
private lemma sum_sin_div_left_le_harmonic (m : ℕ) {frac : ℝ} (hfrac_nonneg : 0 ≤ frac) :
    ∑ k ∈ range m, sin (π * frac) / (π * (((k + 1 : ℕ) : ℝ) + frac)) ≤
      (harmonic m : ℝ) / π := by
  have hle : ∑ k ∈ range m,
      sin (π * frac) / (π * (((k + 1 : ℕ) : ℝ) + frac)) ≤
      ∑ k ∈ range m, (1 : ℝ) / (π * (k + 1 : ℕ)) := by
    refine Finset.sum_le_sum fun k _ => ?_
    have hden1 : 0 < π * ((k + 1 : ℕ) : ℝ) := by positivity
    have hden2 : 0 < π * (((k + 1 : ℕ) : ℝ) + frac) := by positivity
    rw [div_le_div_iff₀ hden2 hden1]
    nlinarith [sin_le_one (π * frac), hfrac_nonneg, pi_pos]
  have hH : ∑ k ∈ range m, (1 : ℝ) / (π * (k + 1 : ℕ)) = (harmonic m : ℝ) / π := by
    calc ∑ k ∈ range m, (1 : ℝ) / (π * (k + 1 : ℕ))
        = ∑ k ∈ range m, ((k + 1 : ℕ) : ℝ)⁻¹ * π⁻¹ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          field_simp
      _ = (∑ k ∈ range m, ((k + 1 : ℕ) : ℝ)⁻¹) * π⁻¹ := by rw [← Finset.sum_mul]
      _ = (harmonic m : ℝ) * π⁻¹ := by
          simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      _ = (harmonic m : ℝ) / π := by rw [div_eq_mul_inv]
  exact hle.trans (le_of_eq hH)

/-- Right-tail harmonic upper bound for the main-term sum. -/
private lemma sum_sin_div_right_le_harmonic (l : ℕ) {frac : ℝ} (hfrac_lt : frac < 1) :
    ∑ k ∈ range l, sin (π * frac) / (π * (((k + 1 : ℕ) : ℝ) + 1 - frac)) ≤
      (harmonic l : ℝ) / π := by
  have hle : ∑ k ∈ range l,
      sin (π * frac) / (π * (((k + 1 : ℕ) : ℝ) + 1 - frac)) ≤
      ∑ k ∈ range l, (1 : ℝ) / (π * (k + 1 : ℕ)) := by
    refine Finset.sum_le_sum fun k _ => ?_
    have hden1 : 0 < π * ((k + 1 : ℕ) : ℝ) := by positivity
    have hden2 : 0 < π * (((k + 1 : ℕ) : ℝ) + 1 - frac) := by
      have : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) + 1 - frac := by
        have hk : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k
        linarith
      positivity
    rw [div_le_div_iff₀ hden2 hden1]
    nlinarith [sin_le_one (π * frac), hfrac_lt, pi_pos]
  have hH : ∑ k ∈ range l, (1 : ℝ) / (π * (k + 1 : ℕ)) = (harmonic l : ℝ) / π := by
    calc ∑ k ∈ range l, (1 : ℝ) / (π * (k + 1 : ℕ))
        = ∑ k ∈ range l, ((k + 1 : ℕ) : ℝ)⁻¹ * π⁻¹ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          field_simp
      _ = (∑ k ∈ range l, ((k + 1 : ℕ) : ℝ)⁻¹) * π⁻¹ := by rw [← Finset.sum_mul]
      _ = (harmonic l : ℝ) * π⁻¹ := by
          simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      _ = (harmonic l : ℝ) / π := by rw [div_eq_mul_inv]
  exact hle.trans (le_of_eq hH)

/-- Harmonic bound for the sum of `sin (π frac) / (π |j - ν|)` over `j ≤ n`, where
`ν = m + frac` with `m < n` and `0 < frac < 1`. -/
private lemma sum_sin_div_abs_sub_le {n m : ℕ} {ν : ℝ} (hm_nat : m < n)
    (hm_lt_one : ν < (m : ℝ) + 1) (hfrac_pos : 0 < ν - m) :
    ∑ j ∈ range (n + 1), sin (π * (ν - m)) / (π * |(j : ℝ) - ν|) ≤
      2 + 2 * (1 + log (n : ℝ)) / π := by
  set frac : ℝ := ν - m with hfrac
  have hfrac_nonneg : 0 ≤ frac := hfrac_pos.le
  have hfrac_lt : frac < 1 := by rw [hfrac]; linarith
  have hsplit := Finset.sum_range_add
    (fun j => sin (π * frac) / (π * |(j : ℝ) - ν|)) (m + 1) (n - m)
  have hcount : m + 1 + (n - m) = n + 1 := by omega
  have hdistL (j : ℕ) (hj : j ≤ m) :
      |(j : ℝ) - ν| = ((m - j : ℕ) : ℝ) + frac := by
    have hjν : (j : ℝ) ≤ ν := by
      have : (j : ℝ) ≤ m := by exact_mod_cast hj
      linarith
    rw [abs_of_nonpos (sub_nonpos.mpr hjν), Nat.cast_sub hj]
    rw [hfrac]
    ring
  have hdistR (k : ℕ) :
      |((m + 1 + k : ℕ) : ℝ) - ν| = (k : ℝ) + 1 - frac := by
    have hlt : ν < ((m + 1 + k : ℕ) : ℝ) := by push_cast; linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hlt.le)]
    rw [hfrac]
    push_cast
    ring
  have hleftEq : ∑ j ∈ range (m + 1), sin (π * frac) / (π * |(j : ℝ) - ν|) =
      ∑ j ∈ range (m + 1), sin (π * frac) / (π * ((j : ℝ) + frac)) := by
    have hrew : ∑ j ∈ range (m + 1), sin (π * frac) / (π * |(j : ℝ) - ν|) =
        ∑ j ∈ range (m + 1),
          sin (π * frac) / (π * (((m - j : ℕ) : ℝ) + frac)) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hdistL j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
    rw [hrew, ← Finset.sum_range_reflect
      (fun j => sin (π * frac) / (π * ((j : ℝ) + frac))) (m + 1)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hidx : m + 1 - 1 - j = m - j := by have := Finset.mem_range.mp hj; omega
    rw [hidx]
  have hrightEq : ∑ k ∈ range (n - m),
        sin (π * frac) / (π * |((m + 1 + k : ℕ) : ℝ) - ν|) =
      ∑ k ∈ range (n - m), sin (π * frac) / (π * ((k : ℝ) + 1 - frac)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hdistR k]
  have hzeroL : sin (π * frac) / (π * frac) ≤ 1 := by
    rw [div_le_one (mul_pos pi_pos hfrac_pos)]
    exact sin_le (mul_nonneg pi_pos.le hfrac_nonneg)
  have honeSub : 0 < 1 - frac := by linarith
  have hsinSymm : sin (π * frac) = sin (π * (1 - frac)) := by
    rw [show π * (1 - frac) = π - π * frac by ring, sin_pi_sub]
  have hzeroR : sin (π * frac) / (π * (1 - frac)) ≤ 1 := by
    rw [hsinSymm, div_le_one (mul_pos pi_pos honeSub)]
    exact sin_le (mul_nonneg pi_pos.le honeSub.le)
  have hleftBound : ∑ j ∈ range (m + 1), sin (π * frac) / (π * ((j : ℝ) + frac)) ≤
      (harmonic m : ℝ) / π + 1 := by
    rw [Finset.sum_range_succ' (fun j => sin (π * frac) / (π * ((j : ℝ) + frac))) m]
    simp only [Nat.cast_zero, zero_add]
    exact add_le_add (sum_sin_div_left_le_harmonic m hfrac_nonneg) hzeroL
  have hrightBound : ∑ k ∈ range (n - m),
        sin (π * frac) / (π * ((k : ℝ) + 1 - frac)) ≤
      (harmonic (n - m - 1) : ℝ) / π + 1 := by
    have hlen : n - m = (n - m - 1) + 1 := by omega
    rw [hlen, Finset.sum_range_succ'
      (fun k => sin (π * frac) / (π * ((k : ℝ) + 1 - frac))) (n - m - 1)]
    simp only [Nat.cast_zero, zero_add]
    exact add_le_add (sum_sin_div_right_le_harmonic (n - m - 1) hfrac_lt) hzeroR
  have hHm : (harmonic m : ℝ) ≤ 1 + log (n : ℝ) :=
    (Rat.cast_le.mpr (harmonic_mono (Nat.le_of_lt hm_nat))).trans (harmonic_le_one_add_log n)
  have hHr : (harmonic (n - m - 1) : ℝ) ≤ 1 + log (n : ℝ) :=
    (Rat.cast_le.mpr (harmonic_mono (by omega : n - m - 1 ≤ n))).trans (harmonic_le_one_add_log n)
  rw [hcount] at hsplit
  rw [hsplit, hleftEq, hrightEq]
  calc
        (∑ j ∈ range (m + 1), sin (π * frac) / (π * ((j : ℝ) + frac))) +
          ∑ k ∈ range (n - m), sin (π * frac) / (π * ((k : ℝ) + 1 - frac))
          ≤ ((harmonic m : ℝ) / π + 1) + ((harmonic (n - m - 1) : ℝ) / π + 1) :=
            add_le_add hleftBound hrightBound
      _ = 2 + ((harmonic m : ℝ) + harmonic (n - m - 1)) / π := by ring
      _ ≤ 2 + 2 * (1 + log (n : ℝ)) / π := by
          have hHsum : (harmonic m : ℝ) + harmonic (n - m - 1) ≤
              2 * (1 + log (n : ℝ)) := by linarith
          have hdiv := div_le_div_of_nonneg_right hHsum pi_pos.le
          linarith

/-- Sum of the cotangent main terms, compared with `(2/π) log(n+1)`. -/
lemma sum_chebyshevLebesgueMain_le {n : ℕ} (hn : 1 ≤ n) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 π) (hnode : ∀ i, θ ≠ chebyshevNodeAngle n i) :
    ∑ i, chebyshevLebesgueMain n θ i ≤
      (2 / π) * log ((n : ℝ) + 1) + 2 + 2 / π := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let ν : ℝ := (n : ℝ) * θ / π
  let m : ℕ := Nat.floor ν
  let frac : ℝ := ν - m
  have hν0 : 0 < ν := div_pos (mul_pos hn0 hθ.1) pi_pos
  have hνn : ν < n := by
    unfold ν
    rw [div_lt_iff₀ pi_pos]
    nlinarith [hθ.2, hn0, pi_pos]
  have hm_le : (m : ℝ) ≤ ν := Nat.floor_le hν0.le
  have hm_lt_one : ν < (m : ℝ) + 1 := by simpa using Nat.lt_floor_add_one ν
  have hm_nat : m < n := by exact_mod_cast (hm_le.trans_lt hνn)
  have hfrac_nonneg : 0 ≤ frac := by unfold frac; linarith
  have hfrac_lt : frac < 1 := by unfold frac; linarith
  have hfrac_pos : 0 < frac := by
    apply lt_of_le_of_ne hfrac_nonneg
    intro hzero
    have hνeq : ν = m := by unfold frac at hzero; linarith
    have hθeq : θ = chebyshevNodeAngle n ⟨m, by omega⟩ := by
      unfold chebyshevNodeAngle
      rw [show (m : ℝ) = ν from hνeq.symm]
      have hνdef : ν = (n : ℝ) * θ / π := rfl
      rw [hνdef]
      field_simp
    exact hnode ⟨m, by omega⟩ hθeq
  have hsin_abs : |sin ((n : ℝ) * θ)| = sin (π * frac) := by
    have hmul : (n : ℝ) * θ = (m : ℝ) * π + π * frac := by
      have hθν : (n : ℝ) * θ = π * ν := by unfold ν; field_simp
      rw [hθν, show ν = (m : ℝ) + frac by unfold frac; ring]
      ring
    rw [hmul, add_comm, sin_add_nat_mul_pi, abs_mul]
    have habs1 : |(-1 : ℝ) ^ m| = 1 := by rw [abs_pow, abs_neg, abs_one, one_pow]
    rw [habs1, one_mul, abs_of_pos]
    exact sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hfrac_pos) (by nlinarith [hfrac_lt, pi_pos])
  have hsum1 : ∑ i, chebyshevLebesgueMain n θ i ≤
      ∑ i : Fin (n + 1), |sin ((n : ℝ) * θ)| / (π * |(i.val : ℝ) - ν|) :=
    Finset.sum_le_sum fun i _ => chebyshevLebesgueMain_le_sin_div hn hθ hnode i
  have hrange : ∑ i : Fin (n + 1),
        |sin ((n : ℝ) * θ)| / (π * |(i.val : ℝ) - ν|) =
      ∑ j ∈ range (n + 1), |sin ((n : ℝ) * θ)| / (π * |(j : ℝ) - ν|) :=
    Fin.sum_univ_eq_sum_range (fun j => |sin ((n : ℝ) * θ)| / (π * |(j : ℝ) - ν|)) (n + 1)
  rw [hsin_abs] at hsum1 hrange
  have hsumR : ∑ j ∈ range (n + 1), sin (π * frac) / (π * |(j : ℝ) - ν|) ≤
      2 + 2 * (1 + log (n : ℝ)) / π :=
    sum_sin_div_abs_sub_le hm_nat hm_lt_one hfrac_pos
  have hlog : log (n : ℝ) ≤ log ((n : ℝ) + 1) :=
    (log_le_log_iff hn0 (by positivity)).mpr (by linarith)
  have hlogMul : (2 / π) * log (n : ℝ) ≤ (2 / π) * log ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  calc ∑ i, chebyshevLebesgueMain n θ i
      ≤ ∑ i : Fin (n + 1), sin (π * frac) / (π * |(i.val : ℝ) - ν|) := hsum1
    _ = ∑ j ∈ range (n + 1), sin (π * frac) / (π * |(j : ℝ) - ν|) := hrange
    _ ≤ 2 + 2 * (1 + log (n : ℝ)) / π := hsumR
    _ = 2 + 2 / π + (2 / π) * log (n : ℝ) := by ring
    _ ≤ (2 / π) * log ((n : ℝ) + 1) + 2 + 2 / π := by linarith [hlogMul]

/-- Interior extremal weights equal one. -/
lemma chebyshevExtremalWeight_of_interior {n : ℕ} {i : Fin (n + 1)}
    (h0 : i.val ≠ 0) (hn : i.val ≠ n) : chebyshevExtremalWeight n i = 1 := by
  rw [chebyshevExtremalWeight, ite_eq_right]
  intro h
  cases h <;> contradiction

/-- The angle-comparison sign is `1` when the node lies to the left. -/
lemma chebyshevAngleSign_of_lt {n : ℕ} {θ : ℝ} {i : Fin (n + 1)}
    (h : chebyshevNodeAngle n i < θ) : chebyshevAngleSign n θ i = 1 := by
  simp [chebyshevAngleSign, h]

/-- The angle-comparison sign is `-1` when the node is not to the left. -/
lemma chebyshevAngleSign_of_not_lt {n : ℕ} {θ : ℝ} {i : Fin (n + 1)}
    (h : ¬ chebyshevNodeAngle n i < θ) : chebyshevAngleSign n θ i = -1 := by
  simp [chebyshevAngleSign, h]

/-- Left-endpoint correction on `(0, π/2]`. -/
lemma chebyshevLebesgueCorrection_zero_le {n : ℕ} (hn : 1 ≤ n) {θ : ℝ}
    (hθ : θ ∈ Set.Ioc 0 (π / 2)) :
    chebyshevLebesgueCorrection n θ ⟨0, by omega⟩ ≤ 1 / 2 := by
  have hθ0 : 0 < θ := hθ.1
  have hθ2 : θ ≤ π / 2 := hθ.2
  let i0 : Fin (n + 1) := ⟨0, by omega⟩
  have hφ : chebyshevNodeAngle n i0 = 0 := by simp [chebyshevNodeAngle, i0]
  have hsign : chebyshevAngleSign n θ i0 = 1 :=
    chebyshevAngleSign_of_lt (by simpa [hφ] using hθ0)
  have hw : chebyshevExtremalWeight n i0 = 2 := by simp [chebyshevExtremalWeight, i0]
  have hsinθ : 0 < sin θ :=
    sin_pos_of_pos_of_lt_pi hθ0 (hθ2.trans_lt (by linarith [pi_pos]))
  have hhalf0 : 0 < θ / 2 := by linarith
  have hhalfπ : θ / 2 < π / 2 := by linarith [hθ2]
  have hsinhalf : 0 < sin (θ / 2) :=
    sin_pos_of_pos_of_lt_pi hhalf0 (hhalfπ.trans (by linarith [pi_pos]))
  have hcoshalf : 0 < cos (θ / 2) :=
    cos_pos_of_mem_Ioo ⟨(by linarith [pi_pos] : -(π / 2) < 0).trans hhalf0, hhalfπ⟩
  have hdouble : sin θ = 2 * sin (θ / 2) * cos (θ / 2) := by
    have h := sin_two_mul (θ / 2)
    rwa [show 2 * (θ / 2) = θ by ring] at h
  have hmul := abs_sin_nat_mul_le n θ
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hbound : |sin ((n : ℝ) * θ)| ≤ (n : ℝ) * (2 * sin (θ / 2) * cos (θ / 2)) := by
    calc |sin ((n : ℝ) * θ)|
        ≤ (n : ℝ) * |sin θ| := hmul
      _ = (n : ℝ) * sin θ := by rw [abs_of_pos hsinθ]
      _ = (n : ℝ) * (2 * sin (θ / 2) * cos (θ / 2)) := by rw [hdouble]
  unfold chebyshevLebesgueCorrection
  rw [hsign, hw, hφ, add_zero, mul_one, cot_eq_cos_div_sin]
  have hden : (2 : ℝ) * n * 2 = 4 * n := by ring
  rw [hden]
  have hfac : 0 ≤ cos (θ / 2) / sin (θ / 2) / (4 * (n : ℝ)) := by positivity
  have hineq := mul_le_mul_of_nonneg_right hbound hfac
  have hassoc : |sin ((n : ℝ) * θ)| * (cos (θ / 2) / sin (θ / 2) / (4 * (n : ℝ))) =
      |sin ((n : ℝ) * θ)| / (4 * (n : ℝ)) * (cos (θ / 2) / sin (θ / 2)) := by ring
  have hsimp : (n : ℝ) * (2 * sin (θ / 2) * cos (θ / 2)) *
        (cos (θ / 2) / sin (θ / 2) / (4 * (n : ℝ))) = cos (θ / 2) ^ 2 / 2 := by
    field_simp [hsinhalf.ne', hnpos.ne']
    norm_num
  rw [← hassoc]
  refine (hineq.trans_eq hsimp).trans ?_
  have hcosle : cos (θ / 2) ^ 2 ≤ 1 := by
    rw [← sq_abs]
    have h1 := abs_cos_le_one (θ / 2)
    have hmul := mul_le_mul h1 h1 (abs_nonneg _) zero_le_one
    simpa [sq] using hmul
  exact (div_le_div_of_nonneg_right hcosle (by norm_num : (0 : ℝ) ≤ 2)).trans (by norm_num)

/-- Right-endpoint correction on `(0, π/2]`. -/
lemma chebyshevLebesgueCorrection_last_le {n : ℕ} (hn : 1 ≤ n) {θ : ℝ}
    (hθ : θ ∈ Set.Ioc 0 (π / 2)) :
    chebyshevLebesgueCorrection n θ ⟨n, by omega⟩ ≤ π / 8 := by
  have hθ0 : 0 < θ := hθ.1
  have hθ2 : θ ≤ π / 2 := hθ.2
  let iN : Fin (n + 1) := ⟨n, by omega⟩
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hφ : chebyshevNodeAngle n iN = π := by
    simp [chebyshevNodeAngle, iN]
    field_simp
  have hsign : chebyshevAngleSign n θ iN = -1 :=
    chebyshevAngleSign_of_not_lt (by
      rw [hφ]
      linarith [hθ2, pi_pos])
  have hw : chebyshevExtremalWeight n iN = 2 := by simp [chebyshevExtremalWeight, iN]
  have hcot : cot ((θ + π) / 2) = -tan (θ / 2) := by
    have harg : (θ + π) / 2 = π / 2 + θ / 2 := by ring
    have hcos : 0 < cos (θ / 2) :=
      cos_pos_of_mem_Ioo ⟨(by linarith [pi_pos] : -(π / 2) < 0).trans (by linarith : 0 < θ / 2),
        by linarith [hθ2]⟩
    rw [harg, cot_eq_cos_div_sin, tan_eq_sin_div_cos, cos_add, sin_add, cos_pi_div_two,
      sin_pi_div_two]
    field_simp [hcos.ne']
    ring
  unfold chebyshevLebesgueCorrection
  rw [hsign, hw, hφ, hcot]
  have habs : |sin ((n : ℝ) * θ)| ≤ (n : ℝ) * θ := by
    calc |sin ((n : ℝ) * θ)|
        ≤ |(n : ℝ) * θ| := abs_sin_le_abs
      _ = (n : ℝ) * θ := by rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hθ0.le)]
  have htan : tan (θ / 2) ≤ 1 := by
    have hmono := strictMonoOn_tan.monotoneOn
    have hmem1 : θ / 2 ∈ Set.Ioo (-(π / 2)) (π / 2) :=
      ⟨by linarith [pi_pos], by linarith [hθ2]⟩
    have hmem2 : π / 4 ∈ Set.Ioo (-(π / 2)) (π / 2) := by
      constructor <;> linarith [pi_pos]
    have hle := hmono hmem1 hmem2 (by linarith [hθ2])
    simpa [tan_pi_div_four] using hle
  have hprod : |sin ((n : ℝ) * θ)| / (4 * (n : ℝ)) * tan (θ / 2) ≤ θ / 4 := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hcoef : 0 ≤ tan (θ / 2) / (4 * (n : ℝ)) := by
      have : 0 ≤ tan (θ / 2) :=
        tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith [hθ2])
      positivity
    have hineq := mul_le_mul_of_nonneg_right habs hcoef
    have hleft : |sin ((n : ℝ) * θ)| * (tan (θ / 2) / (4 * (n : ℝ))) =
        |sin ((n : ℝ) * θ)| / (4 * (n : ℝ)) * tan (θ / 2) := by ring
    rw [← hleft]
    have hright : (n : ℝ) * θ * (tan (θ / 2) / (4 * (n : ℝ))) = θ / 4 * tan (θ / 2) := by
      field_simp [hnpos.ne']
    rw [hright] at hineq
    have htan1 : θ / 4 * tan (θ / 2) ≤ θ / 4 := by
      have hθ4 : 0 ≤ θ / 4 := by linarith
      simpa [mul_one] using mul_le_mul_of_nonneg_left htan hθ4
    exact hineq.trans htan1
  have hneg : |sin ((n : ℝ) * θ)| / (2 * (n : ℝ) * 2) * (-1) * (-tan (θ / 2)) =
      |sin ((n : ℝ) * θ)| / (4 * (n : ℝ)) * tan (θ / 2) := by ring
  rw [hneg]
  exact hprod.trans (by linarith [hθ2])

/-- Off the nodes, the Lebesgue function is the sum of main and correction terms. -/
lemma lebesgueFunction_cos_eq {n : ℕ} (hn : 1 ≤ n) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 π) (hnode : ∀ i, θ ≠ chebyshevNodeAngle n i) :
    lebesgueFunction (chebyshevExtremalNodes n) (cos θ) =
      (∑ i, chebyshevLebesgueMain n θ i) + ∑ i, chebyshevLebesgueCorrection n θ i := by
  unfold lebesgueFunction
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => abs_cardinal_eq_main_add_corr hn hθ hnode i

end CKMA
