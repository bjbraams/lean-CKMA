/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Rademacher chaos and the Johnson–Lindenstrauss lemma

Counting averages of Rademacher sign matrices, Laplace transform bounds for squared Rademacher
projections, and the Johnson–Lindenstrauss finite-set dimension reduction theorem.

## Main results

* `CKMA.johnson_lindenstrauss_explicit`: explicit dimension reduction bound via scaled Rademacher
  sign matrices.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped NNReal ENNReal BigOperators
open MeasureTheory ProbabilityTheory

section JohnsonLindenstrauss

attribute [local instance] Classical.propDecidable
open Real Matrix WithLp

/-- Every coordinate space of signs is inhabited, including a row of length zero. -/
private instance rdotNonempty (d : ℕ) : Nonempty (Fin d → Bool) := ⟨fun _ => false⟩

/-- A Rademacher sign, with `true` sent to `1` and `false` sent to `-1`. -/
private def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- Each Rademacher sign is a square root of one. -/
private lemma sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by cases b <;> simp [sgn]

/-- Flipping a Boolean negates the corresponding Rademacher sign. -/
private lemma sgn_not (b : Bool) : sgn (!b) = -sgn b := by cases b <;> simp [sgn]

/-- The signed dot product of a vector against one row of signs. -/
private def rdot {d : ℕ} (a : Fin d → ℝ) (ε : Fin d → Bool) : ℝ := ∑ j, sgn (ε j) * a j

/-- Normalized counting average on a finite type. -/
private def avg {α : Type*} [Fintype α] (f : α → ℝ) : ℝ := (∑ a, f a) / (Fintype.card α : ℝ)

/-- A constant function averages to that constant on a nonempty finite type. -/
private lemma avg_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    avg (fun _ : α => c) = c := by
  have hC : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [avg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

/-- Counting averages are additive. -/
private lemma avg_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    avg (fun a => f a + g a) = avg f + avg g := by
  unfold avg; rw [Finset.sum_add_distrib, add_div]

/-- Scalars factor out of a counting average. -/
private lemma avg_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    avg (fun a => c * f a) = c * avg f := by
  unfold avg; rw [← Finset.mul_sum, ← mul_div_assoc]

/-- Negation passes through a counting average. -/
private lemma avg_neg {α : Type*} [Fintype α] (f : α → ℝ) :
    avg (fun a => -f a) = -avg f := by
  simp [avg, Finset.sum_neg_distrib, neg_div]

/-- A pointwise inequality passes to counting averages on a nonempty type. -/
private lemma avg_le {α : Type*} [Fintype α] [Nonempty α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : avg f ≤ avg g := by
  have hC : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  unfold avg; exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) hC.le

/-- Nonnegative functions have a nonnegative counting average. -/
private lemma avg_nonneg {α : Type*} [Fintype α] {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    0 ≤ avg f := by
  unfold avg; exact div_nonneg (Finset.sum_nonneg fun a _ => hf a) (Nat.cast_nonneg _)

/-- A coordinatewise product averages to the product of the averages. -/
private lemma avg_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)] (f : ∀ i, α i → ℝ) :
    avg (fun x : ∀ i, α i => ∏ i, f i (x i)) = ∏ i, avg (f i) := by
  simp only [avg]; rw [← Fintype.prod_sum, Fintype.card_pi, Nat.cast_prod]
  exact (Finset.prod_div_distrib
    (fun i => ∑ j, f i j) (fun i => (Fintype.card (α i) : ℝ))).symm

/-- The mean of one Rademacher row vanishes by a global sign flip. -/
private lemma rdot_mean {d : ℕ} (a : Fin d → ℝ) : avg (fun ε => rdot a ε) = 0 := by
  let e : (Fin d → Bool) ≃ (Fin d → Bool) := Equiv.piCongrRight fun _ =>
    ⟨not, not, fun b => by cases b <;> rfl, fun b => by cases b <;> rfl⟩
  have hdot : ∀ ε, rdot a (e ε) = -rdot a ε := by
    intro ε; simp only [rdot, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (e ε) j = !(ε j) by simp [e, Equiv.piCongrRight_apply], sgn_not, neg_mul]
  have hsym : avg (fun ε => rdot a ε) = avg (fun ε => rdot a (e ε)) := by
    simp only [avg]; congr 1; exact (Equiv.sum_comp e (fun ε => rdot a ε)).symm
  have hfun : (fun ε => rdot a (e ε)) = fun ε => -rdot a ε := by funext ε; exact hdot ε
  rw [← CharZero.eq_neg_self_iff]; conv_lhs => rw [hsym, hfun, avg_neg]; rfl

/-- Separating the first sign splits a counting average into an iterated average. -/
private lemma avg_cons {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    avg f = avg (fun s : Bool => avg (fun ε : Fin n → Bool => f (Fin.cons s ε))) := by
  let e := Fin.consEquiv (fun _ : Fin (n + 1) => Bool)
  have hsum : ∑ ω : Fin (n + 1) → Bool, f ω =
      ∑ s : Bool, ∑ ε : Fin n → Bool, f (Fin.cons s ε) := by
    rw [← Equiv.sum_comp e f, ← Fintype.sum_prod_type']
    refine Finset.sum_congr rfl fun p _ => ?_; rw [show e p = Fin.cons p.1 p.2 from rfl]
  have hcard : (Fintype.card (Fin (n + 1) → Bool) : ℝ) =
      2 * (Fintype.card (Fin n → Bool) : ℝ) := by
    rw [← Fintype.card_congr e, Fintype.card_prod, Fintype.card_bool]; norm_cast
  set C : ℝ := (Fintype.card (Fin n → Bool) : ℝ)
  have hCpow : C = (2 : ℝ) ^ n := by
    simp only [C, Fintype.card_pi_const, Fintype.card_bool]; norm_cast
  rw [avg, hsum, hcard]; simp only [avg]
  have hsplit : ∑ s : Bool, (∑ ε, f (Fin.cons s ε)) / C =
      (∑ s, ∑ ε, f (Fin.cons s ε)) / C := by
    simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
  calc (∑ s, ∑ ε, f (Fin.cons s ε)) / (2 * C) =
        ((∑ s, ∑ ε, f (Fin.cons s ε)) / C) / 2 := by rw [mul_comm, ← div_div]
    _ = (∑ s, (∑ ε, f (Fin.cons s ε)) / C) / 2 := by rw [hsplit]
    _ = _ := by simp [hCpow, Fintype.card_bool]

/-- Second moment of one Rademacher row, by induction on the length. -/
private lemma rdot_sq {d : ℕ} (a : Fin d → ℝ) :
    avg (fun ε => (rdot a ε) ^ 2) = ∑ j, (a j) ^ 2 := by
  induction d with
  | zero => simp [avg, rdot]
  | succ n ih =>
    let b : Fin n → ℝ := fun i => a i.succ
    have hdot : ∀ s (ε : Fin n → Bool), rdot a (Fin.cons s ε) =
        rdot b ε + sgn s * a 0 := by
      intro s ε; rw [rdot, Fin.sum_univ_succ, rdot]
      simp [b, Fin.cons_zero, Fin.cons_succ, add_comm]
    rw [avg_cons]
    have hinner : ∀ s, avg (fun ε => (rdot a (Fin.cons s ε)) ^ 2) =
        ∑ i, (b i) ^ 2 + (a 0) ^ 2 := by
      intro s; simp_rw [hdot s]
      have hexp : ∀ ε, (rdot b ε + sgn s * a 0) ^ 2 =
          (rdot b ε) ^ 2 + (2 * (sgn s * a 0)) * rdot b ε + (a 0) ^ 2 := by
        intro ε; rw [add_sq, mul_pow, sgn_sq, one_mul]; ring
      simp_rw [hexp]
      rw [avg_add, avg_add, avg_mul, avg_const, rdot_mean b, ih]; ring
    simp_rw [hinner, avg_const, Fin.sum_univ_succ]; ring

/-- The moment generating function of one Rademacher row is at most Gaussian. -/
private lemma rdot_mgf {d : ℕ} (a : Fin d → ℝ) (t : ℝ) :
    avg (fun ε : Fin d → Bool => exp (t * rdot a ε)) ≤ exp (t ^ 2 * (∑ j, a j ^ 2) / 2) := by
  have hprod : ∀ ε : Fin d → Bool, exp (t * rdot a ε) = ∏ j, exp (t * sgn (ε j) * a j) := by
    intro ε; rw [rdot, Finset.mul_sum]; simp_rw [← mul_assoc]; rw [exp_sum]
  have hrewrite : avg (fun ε : Fin d → Bool => exp (t * rdot a ε)) =
      ∏ j, avg (fun b : Bool => exp (t * sgn b * a j)) := by
    have h1 : avg (fun ε : Fin d → Bool => exp (t * rdot a ε)) =
        avg (fun ε : Fin d → Bool => ∏ j, exp (t * sgn (ε j) * a j)) := by
      congr 1; ext ε; exact hprod ε
    rw [h1, avg_prod (fun j b => exp (t * sgn b * a j))]
  rw [hrewrite]
  have hcosh : ∀ j, avg (fun b : Bool => exp (t * sgn b * a j)) = cosh (t * a j) := by
    intro j; unfold avg sgn; rw [Fintype.sum_bool, Fintype.card_bool]
    simp only [Bool.false_eq_true, ↓reduceIte, cosh_eq]; ring
  simp_rw [hcosh]
  calc
    ∏ j, cosh (t * a j) ≤ ∏ j, exp ((t * a j) ^ 2 / 2) := by
      refine Finset.prod_le_prod₀ (fun j _ => (cosh_pos _).le) fun j _ => ?_
      exact cosh_le_exp_half_sq (t * a j)
    _ = exp (∑ j, (t * a j) ^ 2 / 2) := by rw [← exp_sum]
    _ = exp (t ^ 2 * (∑ j, a j ^ 2) / 2) := by
      congr 1; simp_rw [mul_pow]; rw [← Finset.sum_div, ← Finset.mul_sum]

/-- On the nonpositive reals, the exponential is bounded by its quadratic Taylor polynomial. -/
private lemma exp_le_quadratic_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    exp u ≤ 1 + u + u ^ 2 / 2 := by
  set v : ℝ := -u
  have hv : 0 ≤ v := by simpa [v] using neg_nonneg.mpr hu
  set den : ℝ := 1 - v + v ^ 2 / 2
  have hden : 0 < den := by
    have : den = (1 / 2) * ((v - 1) ^ 2 + 1) := by dsimp [den]; ring
    rw [this]; positivity
  have hprod : 1 ≤ (1 + v + v ^ 2 / 2) * den := by
    have : (1 + v + v ^ 2 / 2) * den = 1 + v ^ 4 / 4 := by dsimp [den]; ring
    linarith [sq_nonneg (v ^ 2)]
  have hexp : 1 + v + v ^ 2 / 2 ≤ exp v := quadratic_le_exp_of_nonneg hv
  have hmul : 1 ≤ exp v * den := hprod.trans (mul_le_mul_of_nonneg_right hexp hden.le)
  have hinv : exp (-v) ≤ den := by
    rw [mul_comm] at hmul; rw [← div_le_iff₀ (exp_pos v)] at hmul
    simpa [exp_neg, one_div] using hmul
  simpa [v, neg_neg, den] using hinv

/-- A Rademacher row has fourth moment at most twelve times the squared energy. -/
private lemma rdot_fourth {d : ℕ} (a : Fin d → ℝ) :
    avg (fun ε => (rdot a ε) ^ 4) ≤ 12 * (∑ j, (a j) ^ 2) ^ 2 := by
  set σ2 : ℝ := ∑ j, (a j) ^ 2
  by_cases hσ : σ2 = 0
  · have ha : ∀ j, a j = 0 := by
      intro j
      have hle : (a j) ^ 2 ≤ σ2 :=
        Finset.single_le_sum (fun i _ => sq_nonneg (a i)) (Finset.mem_univ j)
      have hle0 : (a j) ^ 2 ≤ 0 := by simpa [hσ] using hle
      exact sq_eq_zero_iff.mp (le_antisymm hle0 (sq_nonneg _))
    have h0 : ∀ ε, rdot a ε = 0 := by intro ε; simp [rdot, ha]
    simp [h0, avg, hσ, Finset.sum_const_zero]
  · have hσpos : 0 < σ2 := lt_of_le_of_ne (by positivity) (Ne.symm hσ)
    let t : ℝ := 2 / sqrt σ2
    have ht : 0 < t := by dsimp [t]; positivity
    have htσ : t ^ 2 * σ2 = 4 := by
      dsimp [t]; rw [div_pow, sq_sqrt hσpos.le, div_mul_cancel₀ _ hσpos.ne']; norm_num
    have hseries : ∀ z : ℝ, z ^ 4 / 24 ≤ cosh z := by
      intro z
      have hnn n (_ : n ∉ ({2} : Finset ℕ)) :
          0 ≤ z ^ (2 * n) / ((2 * n).factorial : ℝ) :=
        div_nonneg (Even.pow_nonneg (even_two_mul n) z) (Nat.cast_nonneg _)
      simpa [Finset.sum_singleton, show (Nat.factorial 4 : ℝ) = 24 by norm_num] using
        sum_le_hasSum ({2} : Finset ℕ) hnn (hasSum_cosh z)
    have hy : ∀ y, y ^ 4 ≤ (12 / t ^ 4) * (exp (t * y) + exp (-(t * y))) := by
      intro y
      have ht4 : 0 < t ^ 4 := by positivity
      calc y ^ 4 = (t * y) ^ 4 / t ^ 4 := by field_simp [ht.ne']
        _ ≤ 24 * cosh (t * y) / t ^ 4 := by
          rw [div_le_div_iff_of_pos_right ht4]; linarith [hseries (t * y)]
        _ = (12 / t ^ 4) * (exp (t * y) + exp (-(t * y))) := by rw [cosh_eq]; ring
    have havg : avg (fun ε => (rdot a ε) ^ 4) ≤ (12 / t ^ 4) *
        (avg (fun ε => exp (t * rdot a ε)) + avg (fun ε => exp (-(t * rdot a ε)))) := by
      simpa [avg_mul, avg_add] using avg_le (fun ε => hy (rdot a ε))
    have hsum : avg (fun ε => exp (t * rdot a ε)) + avg (fun ε => exp (-(t * rdot a ε))) ≤
        2 * exp 2 := by
      have hpow : t ^ 2 * σ2 / 2 = 2 := by rw [htσ]; ring
      simp_rw [show ∀ ε, -(t * rdot a ε) = (-t) * rdot a ε by intro ε; ring]
      simpa [hpow, σ2, neg_sq, two_mul] using add_le_add (rdot_mgf a t) (rdot_mgf a (-t))
    have hcoef : 0 ≤ 12 / t ^ 4 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hsum hcoef
    have ht4 : t ^ 4 = 16 / σ2 ^ 2 := by
      dsimp [t]; rw [div_pow, show (sqrt σ2) ^ 4 = σ2 ^ 2 by
        rw [show (sqrt σ2) ^ 4 = ((sqrt σ2) ^ 2) ^ 2 by ring, sq_sqrt hσpos.le]]; ring
    have hexp2 : exp 2 ≤ 8 := by
      have he : exp 2 = exp 1 ^ 2 := by rw [← exp_nat_mul]; congr 1; ring
      have hmul' : exp 1 * exp 1 < (28 / 10) * (28 / 10) :=
        mul_lt_mul (exp_one_lt_d9.trans (by norm_num))
          (exp_one_lt_d9.trans (by norm_num)).le (exp_pos 1) (by norm_num)
      have hnum : (28 / 10) * (28 / 10) < 8 := by norm_num
      linarith [he]
    calc avg (fun ε => (rdot a ε) ^ 4) ≤ (12 / t ^ 4) * (2 * exp 2) := havg.trans hmul
      _ = (24 * exp 2) * (σ2 ^ 2 / 16) := by rw [ht4]; ring_nf; rw [inv_inv]
      _ ≤ 12 * σ2 ^ 2 := by nlinarith [hexp2, sq_nonneg σ2]

/-- A negative quadratic exponential is controlled by the second and fourth moments. -/
private lemma rdot_neg_mgf {d : ℕ} (a : Fin d → ℝ) {ell : ℝ} (hell : 0 ≤ ell) :
    avg (fun ε => exp (-ell * (rdot a ε) ^ 2)) ≤
      exp (-ell * ∑ j, (a j) ^ 2 + 6 * ell ^ 2 * (∑ j, (a j) ^ 2) ^ 2) := by
  have h2 := rdot_sq a
  have h4 := rdot_fourth a
  have hpt : ∀ ε, exp (-ell * (rdot a ε) ^ 2) ≤
      1 + (-ell) * (rdot a ε) ^ 2 + (ell ^ 2 / 2) * (rdot a ε) ^ 4 := by
    intro ε
    have hu : -(ell * (rdot a ε) ^ 2) ≤ 0 := neg_nonpos.mpr (mul_nonneg hell (sq_nonneg _))
    convert exp_le_quadratic_of_nonpos hu using 1 <;> ring
  have havg := avg_le hpt
  rw [avg_add, avg_add, avg_mul, avg_mul, avg_const, h2] at havg
  have hcoef : 0 ≤ ell ^ 2 / 2 := by positivity
  have hbound : 1 + (-ell) * ∑ j, (a j) ^ 2 +
      (ell ^ 2 / 2) * avg (fun ε => (rdot a ε) ^ 4) ≤
      1 + (-ell * ∑ j, (a j) ^ 2 + 6 * ell ^ 2 * (∑ j, (a j) ^ 2) ^ 2) := by
    linarith [mul_le_mul_of_nonneg_left h4 hcoef]
  refine havg.trans (hbound.trans ?_)
  convert add_one_le_exp
    (-ell * ∑ j, (a j) ^ 2 + 6 * ell ^ 2 * (∑ j, (a j) ^ 2) ^ 2) using 1; ring

/-- The standard Gaussian integral, normalized so that the variance is one. -/
private lemma integral_exp_neg_half_sq :
    ∫ x : ℝ, exp (-(x ^ 2) / 2) = sqrt (2 * Real.pi) := by
  have hrew : (fun x : ℝ => exp (-(x ^ 2) / 2)) = fun x => exp (-(1 / 2) * x ^ 2) := by
    ext x; congr 1; ring
  rw [hrew, integral_gaussian]
  have : Real.pi / (1 / 2) = 2 * Real.pi := by ring
  rw [this]

/-- Translates of the standard Gaussian remain integrable. -/
private lemma integrable_exp_linear_neg_half_sq (γ : ℝ) :
    Integrable (fun x : ℝ => exp (γ * x - x ^ 2 / 2)) := by
  have hbase : Integrable (fun x : ℝ => exp (-(x ^ 2) / 2)) := by
    have h := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)
    convert h using 1; ext x; congr 1; ring
  have hshift : Integrable (fun x : ℝ => exp (-((x + -γ) ^ 2) / 2)) := hbase.comp_add_right (-γ)
  have hpt : ∀ x, exp (γ * x - x ^ 2 / 2) = exp (γ ^ 2 / 2) * exp (-((x + -γ) ^ 2) / 2) := by
    intro x; rw [← exp_add]; congr 1; ring
  simp_rw [hpt]; exact hshift.const_mul _

/-- Completing the square evaluates a linear perturbation of the standard Gaussian. -/
private lemma integral_exp_linear_neg_half_sq (γ : ℝ) :
    ∫ x : ℝ, exp (γ * x - x ^ 2 / 2) = exp (γ ^ 2 / 2) * sqrt (2 * Real.pi) := by
  have hpt : ∀ x, exp (γ * x - x ^ 2 / 2) = exp (γ ^ 2 / 2) * exp (-((x + -γ) ^ 2) / 2) := by
    intro x; rw [← exp_add]; congr 1; ring
  simp_rw [hpt, integral_const_mul]
  have hint : ∫ x, exp (-((x + -γ) ^ 2) / 2) = ∫ x, exp (-(x ^ 2) / 2) :=
    integral_add_right_eq_self (fun x : ℝ => exp (-(x ^ 2) / 2)) (-γ)
  rw [hint, integral_exp_neg_half_sq]

/-- A quadratic exponential is the normalized integral of a shifted Gaussian. -/
private lemma exp_half_sq_eq_integral (β : ℝ) :
    exp (β ^ 2 / 2) = (sqrt (2 * Real.pi))⁻¹ * ∫ x : ℝ, exp (β * x - x ^ 2 / 2) := by
  rw [integral_exp_linear_neg_half_sq]
  field_simp [sqrt_ne_zero'.mpr (by positivity : (0 : ℝ) < 2 * Real.pi)]

/-- The Bochner integral passes through a finite counting average. -/
private lemma integral_avg {α : Type*} [Fintype α] (f : α → ℝ → ℝ)
    (hf : ∀ a, Integrable (f a)) :
    ∫ x, avg (fun a => f a x) = avg (fun a => ∫ x, f a x) := by
  unfold avg; rw [integral_div, integral_finsetSum _ fun a _ => hf a]

/-- The Laplace transform of one squared Rademacher row, for a subcritical positive parameter. -/
private lemma rdot_sq_mgf {d : ℕ} (a : Fin d → ℝ) {ell : ℝ} (hell : 0 ≤ ell)
    (hρ : 2 * ell * ∑ j, (a j) ^ 2 < 1) :
    avg (fun ε : Fin d → Bool => exp (ell * (rdot a ε) ^ 2)) ≤
      (sqrt (1 - 2 * ell * ∑ j, (a j) ^ 2))⁻¹ := by
  set σ2 : ℝ := ∑ j, (a j) ^ 2
  set s : ℝ := sqrt (2 * ell)
  have hs : s ^ 2 = 2 * ell := sq_sqrt (mul_nonneg (by norm_num) hell)
  have hrepr : ∀ ε, exp (ell * (rdot a ε) ^ 2) = (sqrt (2 * Real.pi))⁻¹ *
      ∫ x, exp (s * rdot a ε * x - x ^ 2 / 2) := by
    intro ε
    rw [show ell * (rdot a ε) ^ 2 = (s * rdot a ε) ^ 2 / 2 by rw [mul_pow, hs]; ring]
    exact exp_half_sq_eq_integral (s * rdot a ε)
  simp_rw [hrepr, avg_mul]
  rw [← integral_avg (fun ε x => exp (s * rdot a ε * x - x ^ 2 / 2))
    (fun ε => integrable_exp_linear_neg_half_sq (s * rdot a ε))]
  have hker : ∀ x, avg (fun ε => exp (s * rdot a ε * x - x ^ 2 / 2)) ≤
      exp (-((1 - 2 * ell * σ2) / 2) * x ^ 2) := by
    intro x
    have hsub : ∀ ε, exp (s * rdot a ε * x - x ^ 2 / 2) =
        exp (-(x ^ 2) / 2) * exp ((s * x) * rdot a ε) := by
      intro ε; rw [← exp_add]; congr 1; ring
    simp_rw [hsub, avg_mul]
    refine (mul_le_mul_of_nonneg_left (rdot_mgf a (s * x)) (exp_pos _).le).trans ?_
    rw [← exp_add]; apply exp_le_exp.mpr
    have hident : -(x ^ 2) / 2 + (s * x) ^ 2 * σ2 / 2 =
        -((1 - 2 * ell * σ2) / 2) * x ^ 2 := by rw [mul_pow, hs]; ring
    linarith [hident]
  have hint : Integrable (fun x : ℝ => exp (-((1 - 2 * ell * σ2) / 2) * x ^ 2)) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      integrable_exp_neg_mul_sq (by linarith : (0 : ℝ) < (1 - 2 * ell * σ2) / 2)
  have hfin : Integrable (fun x => avg (fun ε => exp (s * rdot a ε * x - x ^ 2 / 2))) := by
    have hfun : (fun x => avg (fun ε => exp (s * rdot a ε * x - x ^ 2 / 2))) =
        fun x => ((Fintype.card (Fin d → Bool) : ℝ)⁻¹) *
          ∑ ε, exp (s * rdot a ε * x - x ^ 2 / 2) := by
      funext x; unfold avg; rw [div_eq_mul_inv, mul_comm]
    rw [hfun]
    exact (integrable_finsetSum _ fun ε _ => integrable_exp_linear_neg_half_sq _).const_mul _
  have hρpos : 0 < 1 - 2 * ell * σ2 := by linarith
  have hgauss : ∫ x, exp (-((1 - 2 * ell * σ2) / 2) * x ^ 2) =
      sqrt (2 * Real.pi / (1 - 2 * ell * σ2)) := by rw [integral_gaussian]; congr 1; field_simp
  have hpre : (sqrt (2 * Real.pi))⁻¹ * ∫ x, exp (-((1 - 2 * ell * σ2) / 2) * x ^ 2) =
      (sqrt (1 - 2 * ell * σ2))⁻¹ := by
    rw [hgauss, sqrt_div (by positivity : (0 : ℝ) ≤ 2 * Real.pi) (1 - 2 * ell * σ2)]
    field_simp [sqrt_ne_zero'.mpr (by positivity : (0 : ℝ) < 2 * Real.pi), sqrt_ne_zero'.mpr hρpos]
  calc (sqrt (2 * Real.pi))⁻¹ * ∫ x, avg (fun ε => exp (s * rdot a ε * x - x ^ 2 / 2)) ≤
        (sqrt (2 * Real.pi))⁻¹ * ∫ x, exp (-((1 - 2 * ell * σ2) / 2) * x ^ 2) :=
      mul_le_mul_of_nonneg_left (integral_mono hfin hint hker) (inv_nonneg.mpr (sqrt_nonneg _))
    _ = (sqrt (1 - 2 * ell * σ2))⁻¹ := hpre

/-- Independent rows multiply the Laplace transform of a squared Rademacher dot product. -/
private lemma rdot_sum_mgf {m d : ℕ} (a : Fin d → ℝ) (ell : ℝ) :
    avg (fun ε : Fin m → Fin d → Bool =>
        exp (ell * ∑ k, (rdot a (ε k)) ^ 2)) =
      avg (fun η : Fin d → Bool => exp (ell * (rdot a η) ^ 2)) ^ m := by
  have hpt : ∀ ε : Fin m → Fin d → Bool, exp (ell * ∑ k, (rdot a (ε k)) ^ 2) =
      ∏ k, exp (ell * (rdot a (ε k)) ^ 2) := by
    intro ε; rw [Finset.mul_sum, exp_sum]
  simp_rw [hpt]
  have hfac := avg_prod (fun (_ : Fin m) (η : Fin d → Bool) =>
    exp (ell * (rdot a η) ^ 2))
  simpa [Finset.prod_const, Fintype.card_fin] using hfac

/-- Markov's inequality for the counting measure, in exponential form. -/
private lemma avg_markov {α : Type*} [Fintype α] [Nonempty α] (X : α → ℝ) {t β : ℝ}
    (ht : 0 ≤ t) :
    ((Finset.univ.filter (fun a => β ≤ X a)).card : ℝ) / (Fintype.card α : ℝ) ≤
      exp (-t * β) * avg (fun a => exp (t * X a)) := by
  have : DecidableEq α := Classical.decEq α
  let S := Finset.univ.filter (fun a => β ≤ X a)
  have hC : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have hS : ∀ a ∈ S, exp (t * β) ≤ exp (t * X a) := by
    intro a ha; exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp ha).2 ht)
  have hsum : (S.card : ℝ) * exp (t * β) ≤ ∑ a ∈ S, exp (t * X a) := by
    simpa [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hS
  have hrest : ∑ a ∈ S, exp (t * X a) ≤ ∑ a, exp (t * X a) := by
    have hsub : S ⊆ Finset.univ := Finset.filter_subset _ _
    have hsplit := Finset.sum_sdiff (f := fun a => exp (t * X a)) hsub
    have hnn := Finset.sum_nonneg (fun a (_ : a ∈ Finset.univ \ S) => (exp_pos (t * X a)).le)
    linarith
  have htot := hsum.trans hrest
  have hbound : (S.card : ℝ) ≤ exp (-(t * β)) * ∑ a, exp (t * X a) := by
    have hmul := mul_le_mul_of_nonneg_left htot (exp_nonneg (-(t * β)))
    have hfac : exp (-(t * β)) * ((S.card : ℝ) * exp (t * β)) = S.card := by
      rw [mul_left_comm, ← exp_add, neg_add_cancel, exp_zero, mul_one]
    rwa [hfac] at hmul
  calc
    (S.card : ℝ) / (Fintype.card α : ℝ) ≤
        (exp (-(t * β)) * ∑ a, exp (t * X a)) / (Fintype.card α : ℝ) :=
      div_le_div_of_nonneg_right hbound hC.le
    _ = exp (-t * β) * avg (fun a => exp (t * X a)) := by
      simp only [avg, neg_mul, div_eq_mul_inv]; ring

/-- For `ε ∈ [0, 1]`, the logarithm sits below the tangent line by a quadratic gap. -/
private lemma log_one_add_le_sub_sq {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    log (1 + ε) ≤ ε - ε ^ 2 / 8 := by
  have hpos : 0 < 1 + ε := by linarith
  set u : ℝ := ε - ε ^ 2 / 8
  have hu : 0 ≤ u := by dsimp [u]; nlinarith [sq_nonneg ε]
  have hhalf : ε / 2 ≤ u := by dsimp [u]; nlinarith
  have hsq : ε ^ 2 / 4 ≤ u ^ 2 := by
    calc
      ε ^ 2 / 4 = (ε / 2) * (ε / 2) := by ring
      _ ≤ u * u := mul_self_le_mul_self (by linarith : (0 : ℝ) ≤ ε / 2) hhalf
      _ = u ^ 2 := by ring
  have hlin : 1 + ε ≤ 1 + u + u ^ 2 / 2 := by
    calc
      1 + ε = 1 + u + ε ^ 2 / 8 := by dsimp [u]; ring
      _ ≤ 1 + u + u ^ 2 / 2 := by linarith [hsq]
  exact (log_le_iff_le_exp hpos).2 (hlin.trans (quadratic_le_exp_of_nonneg hu))

/-- Matrices of independent Rademacher signs. -/
private abbrev SignMat (m d : ℕ) := Fin m → Fin d → Bool

/-- Proportion of sign matrices satisfying a predicate. -/
private abbrev signProp {m d : ℕ} (p : SignMat m d → Prop) [DecidablePred p] : ℝ :=
  ((Finset.univ.filter p).card : ℝ) / (Fintype.card (SignMat m d) : ℝ)

/-- Averaged square of one vector's Rademacher row dots. -/
private abbrev rowEnergy {m d : ℕ} (a : Fin d → ℝ) (ω : SignMat m d) : ℝ :=
  (∑ k, (rdot a (ω k)) ^ 2) / m

/-- A smaller event has a smaller proportion. -/
private lemma signProp_le {m d : ℕ} {p q : SignMat m d → Prop} [DecidablePred p]
    [DecidablePred q] (h : ∀ ω, p ω → q ω) : signProp p ≤ signProp q := by
  have hC : 0 < (Fintype.card (SignMat m d) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsub : Finset.univ.filter p ⊆ Finset.univ.filter q := by
    intro ω hω; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h _ (Finset.mem_filter.mp hω).2⟩
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) hC.le

/-- Upper tail for the average of squared Rademacher rows, relative to a positive energy. -/
private lemma rademacher_upper_tail {m d : ℕ} (hm : 0 < m) (a : Fin d → ℝ) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) (hσ : 0 < ∑ j, (a j) ^ 2) :
    signProp (fun ω : SignMat m d => (1 + ε) * ∑ j, (a j) ^ 2 < rowEnergy a ω) ≤
      exp (-(m : ℝ) * ε ^ 2 / 16) := by
  set σ2 : ℝ := ∑ j, (a j) ^ 2
  set ρ : ℝ := ε / (1 + ε)
  have hρ0 : 0 < ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ < 1 := by dsimp [ρ]; rw [div_lt_one (by linarith : (0 : ℝ) < 1 + ε)]; linarith
  set lam : ℝ := ρ / (2 * σ2)
  have hlam : 0 ≤ lam := by dsimp [lam]; positivity
  have hlamρ : 2 * lam * σ2 = ρ := by dsimp [lam]; field_simp
  have hmgf : avg (fun η : Fin d → Bool => exp (lam * (rdot a η) ^ 2)) ≤ (sqrt (1 - ρ))⁻¹ := by
    rw [← hlamρ]; simpa [σ2] using rdot_sq_mgf a hlam (by simpa [σ2] using hlamρ.symm ▸ hρ1)
  let S : SignMat m d → ℝ := fun ω => ∑ k, (rdot a (ω k)) ^ 2
  have hE : avg (fun ω => exp (lam * S ω)) ≤ ((sqrt (1 - ρ))⁻¹) ^ m := by
    rw [show avg (fun ω => exp (lam * S ω)) = avg (fun η => exp (lam * (rdot a η) ^ 2)) ^ m by
      simpa [S] using rdot_sum_mgf a lam]
    exact pow_le_pow_left₀ (avg_nonneg fun _ => (exp_pos _).le) hmgf m
  set β : ℝ := (m : ℝ) * (1 + ε) * σ2
  have hmono := signProp_le (p := fun ω => (1 + ε) * σ2 < rowEnergy a ω)
    (q := fun ω => β ≤ S ω) (fun ω hω => by
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
      dsimp [β, rowEnergy] at hω ⊢; linarith [(lt_div_iff₀ hm0).mp hω])
  have hβ : lam * β = (m : ℝ) * ε / 2 := by dsimp [lam, β, ρ]; field_simp
  have hlogρ : log (1 - ρ) = -log (1 + ε) := by
    rw [show 1 - ρ = (1 + ε)⁻¹ by dsimp [ρ]; field_simp; ring, log_inv]
  have hpow : ((sqrt (1 - ρ))⁻¹) ^ m = exp ((m : ℝ) * (-(1 / 2) * log (1 - ρ))) := by
    have h1ρ : 0 < 1 - ρ := by linarith
    rw [← exp_log (inv_pos.mpr (sqrt_pos.2 h1ρ)), ← exp_nat_mul]
    congr 1; rw [log_inv, log_sqrt h1ρ.le]; ring
  have hexp : exp (-lam * β) * ((sqrt (1 - ρ))⁻¹) ^ m ≤ exp (-(m : ℝ) * ε ^ 2 / 16) := by
    rw [hpow, ← exp_add]; apply exp_le_exp.mpr; rw [show -lam * β = -(lam * β) by ring, hβ, hlogρ]
    nlinarith [show (0 : ℝ) < m by exact_mod_cast hm, log_one_add_le_sub_sq hε0.le hε1.le]
  calc signProp (fun ω => (1 + ε) * σ2 < rowEnergy a ω) ≤ signProp (fun ω => β ≤ S ω) := hmono
    _ ≤ exp (-lam * β) * avg (fun ω => exp (lam * S ω)) := by
      simpa [signProp, S] using avg_markov S hlam (β := β)
    _ ≤ exp (-lam * β) * ((sqrt (1 - ρ))⁻¹) ^ m := mul_le_mul_of_nonneg_left hE (exp_pos _).le
    _ ≤ exp (-(m : ℝ) * ε ^ 2 / 16) := hexp

/-- Lower tail for the average of squared Rademacher rows, relative to a positive energy. -/
private lemma rademacher_lower_tail {m d : ℕ} (hm : 0 < m) (a : Fin d → ℝ) {ε : ℝ}
    (hε0 : 0 < ε) (hσ : 0 < ∑ j, (a j) ^ 2) :
    signProp (fun ω : SignMat m d => rowEnergy a ω < (1 - ε) * ∑ j, (a j) ^ 2) ≤
      exp (-(m : ℝ) * ε ^ 2 / 24) := by
  set σ2 : ℝ := ∑ j, (a j) ^ 2
  set t : ℝ := ε / (12 * σ2)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrow := rdot_neg_mgf a ht
  let S : SignMat m d → ℝ := fun ω => ∑ k, (rdot a (ω k)) ^ 2
  have hE : avg (fun ω => exp (-t * S ω)) ≤
      exp ((m : ℝ) * (-t * σ2 + 6 * t ^ 2 * σ2 ^ 2)) := by
    rw [show avg (fun ω => exp (-t * S ω)) = avg (fun η => exp (-t * (rdot a η) ^ 2)) ^ m by
      simpa [S] using rdot_sum_mgf a (-t)]
    refine (pow_le_pow_left₀ (avg_nonneg fun _ => (exp_pos _).le)
      (by simpa [σ2] using hrow) m).trans ?_
    rw [← exp_nat_mul]; exact exp_le_exp.mpr (le_of_eq (by ring))
  set γ : ℝ := (m : ℝ) * (1 - ε) * σ2
  have hmono := signProp_le (p := fun ω => rowEnergy a ω < (1 - ε) * σ2)
    (q := fun ω => -γ ≤ -S ω) (fun ω hω => by
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
      dsimp [γ, rowEnergy] at hω ⊢; linarith [(div_lt_iff₀ hm0).mp hω])
  have hexp : exp (-t * -γ) * exp ((m : ℝ) * (-t * σ2 + 6 * t ^ 2 * σ2 ^ 2)) ≤
      exp (-(m : ℝ) * ε ^ 2 / 24) := by
    rw [← exp_add]; apply exp_le_exp.mpr
    have hident : -t * -γ + (m : ℝ) * (-t * σ2 + 6 * t ^ 2 * σ2 ^ 2) =
        -(m : ℝ) * ε ^ 2 / 24 := by
      dsimp [γ, t]; field_simp [hσ.ne']; ring
    rw [hident]
  calc signProp (fun ω => S ω / m < (1 - ε) * σ2) ≤ signProp (fun ω => -γ ≤ -S ω) := by
        simpa [rowEnergy] using hmono
    _ ≤ exp (-t * -γ) * avg (fun ω => exp (t * -S ω)) := by
      simpa [signProp] using avg_markov (fun ω => -S ω) ht (β := -γ)
    _ ≤ exp (-t * -γ) * exp ((m : ℝ) * (-t * σ2 + 6 * t ^ 2 * σ2 ^ 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le; simp_rw [mul_neg, ← neg_mul]; exact hE
    _ ≤ exp (-(m : ℝ) * ε ^ 2 / 24) := hexp

/-- A union of two events is no larger than the sum of their counting measures. -/
private lemma card_filter_or_le {α : Type*} [Fintype α] {p q : α → Prop} [DecidablePred p]
    [DecidablePred q] : (Finset.univ.filter (fun a => p a ∨ q a)).card ≤
      (Finset.univ.filter p).card + (Finset.univ.filter q).card := by
  have : DecidableEq α := Classical.decEq α
  have hsub : Finset.univ.filter (fun a => p a ∨ q a) ⊆
      Finset.univ.filter p ∪ Finset.univ.filter q := by
    intro a ha; rcases (Finset.mem_filter.mp ha).2 with hp | hq
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- Deviation of one averaged squared norm, including the zero vector. -/
private lemma rademacher_deviation {m d : ℕ} (hm : 0 < m) (a : Fin d → ℝ) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    signProp (fun ω : SignMat m d => (1 + ε) * ∑ j, (a j) ^ 2 < rowEnergy a ω ∨
      rowEnergy a ω < (1 - ε) * ∑ j, (a j) ^ 2) ≤ 2 * exp (-(m : ℝ) * ε ^ 2 / 24) := by
  set σ2 : ℝ := ∑ j, (a j) ^ 2
  by_cases hσ : σ2 = 0
  · have ha : ∀ j, a j = 0 := by
      intro j
      have hle : a j ^ 2 ≤ σ2 :=
        Finset.single_le_sum (fun i _ => sq_nonneg (a i)) (Finset.mem_univ j)
      have hle0 : a j ^ 2 ≤ 0 := by simpa [hσ] using hle
      exact sq_eq_zero_iff.mp (le_antisymm hle0 (sq_nonneg _))
    have hempty : Finset.univ.filter (fun ω : SignMat m d => (1 + ε) * σ2 < rowEnergy a ω ∨
        rowEnergy a ω < (1 - ε) * σ2) = ∅ := by
      ext ω; simp [rowEnergy, rdot, ha, hσ]
    simp [signProp, hempty]; positivity
  · have hσpos : 0 < σ2 := lt_of_le_of_ne (by dsimp [σ2]; positivity) (Ne.symm hσ)
    have hup := rademacher_upper_tail hm a hε0 hε1 hσpos
    have hdown := rademacher_lower_tail hm a hε0 hσpos
    have hC : 0 < (Fintype.card (SignMat m d) : ℝ) := by exact_mod_cast Fintype.card_pos
    have hor : ((Finset.univ.filter (fun ω : SignMat m d =>
        (1 + ε) * σ2 < rowEnergy a ω ∨ rowEnergy a ω < (1 - ε) * σ2)).card : ℝ) ≤
        ((Finset.univ.filter (fun ω : SignMat m d =>
          (1 + ε) * σ2 < rowEnergy a ω)).card : ℝ) +
          ((Finset.univ.filter (fun ω : SignMat m d =>
            rowEnergy a ω < (1 - ε) * σ2)).card : ℝ) := by
      exact_mod_cast card_filter_or_le (p := fun ω : SignMat m d => (1 + ε) * σ2 < rowEnergy a ω)
        (q := fun ω : SignMat m d => rowEnergy a ω < (1 - ε) * σ2)
    calc signProp (fun ω => (1 + ε) * σ2 < rowEnergy a ω ∨ rowEnergy a ω < (1 - ε) * σ2) ≤
          signProp (fun ω => (1 + ε) * σ2 < rowEnergy a ω) +
            signProp (fun ω => rowEnergy a ω < (1 - ε) * σ2) := by
              simpa [signProp, add_div] using div_le_div_of_nonneg_right hor hC.le
      _ ≤ exp (-(m : ℝ) * ε ^ 2 / 16) + exp (-(m : ℝ) * ε ^ 2 / 24) := add_le_add hup hdown
      _ ≤ 2 * exp (-(m : ℝ) * ε ^ 2 / 24) := by
        have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
        linarith [exp_le_exp.mpr
          (show -(m : ℝ) * ε ^ 2 / 16 ≤ -(m : ℝ) * ε ^ 2 / 24 by nlinarith [hm0, sq_nonneg ε])]

/-- The counting measure of an existential event is at most the sum of the fiber measures. -/
private lemma card_filter_exists_le {α ι : Type*} [Fintype α] [Fintype ι] {p : ι → α → Prop}
    [DecidablePred fun a => ∃ i, p i a] [∀ i, DecidablePred (p i)] :
    (Finset.univ.filter (fun a => ∃ i, p i a)).card ≤ ∑ i, (Finset.univ.filter (p i)).card := by
  have hpoint : ∀ a, (if ∃ i, p i a then 1 else 0) ≤ ∑ i, if p i a then 1 else 0 := by
    intro a; by_cases h : ∃ i, p i a
    · rcases h with ⟨i, hi⟩; rw [ite_eq_left ⟨i, hi⟩]
      calc (1 : ℕ) = (if p i a then 1 else 0) := (ite_eq_left hi).symm
        _ ≤ ∑ j, if p j a then 1 else 0 := Finset.single_le_sum
          (fun j _ => Nat.zero_le (if p j a then 1 else 0)) (Finset.mem_univ i)
    · rw [ite_eq_right h]; exact Nat.zero_le _
  calc (Finset.univ.filter (fun a => ∃ i, p i a)).card =
        ∑ a, if ∃ i, p i a then 1 else 0 := by simp [Finset.sum_boole]
    _ ≤ ∑ a, ∑ i, if p i a then 1 else 0 := Finset.sum_le_sum fun a _ => hpoint a
    _ = ∑ i, ∑ a, if p i a then 1 else 0 := Finset.sum_comm
    _ = ∑ i, (Finset.univ.filter (p i)).card := by
      refine Finset.sum_congr rfl fun i _ => ?_; exact Finset.sum_boole (p i) Finset.univ

/-- The scaled sign matrix, as a Euclidean linear map. -/
private def jlMap (m d : ℕ) (ω : SignMat m d) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) where
  toFun v := toLp 2 fun k => (sqrt (m : ℝ))⁻¹ * rdot (fun j => v j) (ω k)
  map_add' v w := by ext k; simp only [PiLp.add_apply, rdot, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  map_smul' c v := by
    ext k; simp only [PiLp.smul_apply, rdot, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_; ring

/-- The squared Euclidean norm of a sign projection is the averaged square of the row dots. -/
private lemma norm_sq_jlMap {m d : ℕ} (ω : SignMat m d)
    (v : EuclideanSpace ℝ (Fin d)) : ‖jlMap m d ω v‖ ^ 2 = rowEnergy (fun j => v j) ω := by
  have hsqrt : ((sqrt (m : ℝ))⁻¹) ^ 2 = (m : ℝ)⁻¹ := by rw [inv_pow, sq_sqrt (Nat.cast_nonneg m)]
  have hcoord : ∀ i, (jlMap m d ω v) i =
      (sqrt (m : ℝ))⁻¹ * rdot (fun j => v j) (ω i) := by intro i; unfold jlMap; dsimp
  rw [EuclideanSpace.real_norm_sq_eq]
  have hterm : ∀ i, ((jlMap m d ω v) i) ^ 2 = (rdot (fun j => v j) (ω i)) ^ 2 / m := by
    intro i; rw [hcoord, mul_pow, hsqrt, mul_comm, ← div_eq_mul_inv]
  simp_rw [hterm, ← Finset.sum_div]

/-- At most one point: the zero map in dimension zero preserves every distance. -/
private lemma jl_few_points {d N : ℕ} (hN : N ≤ 1) (x : Fin N → EuclideanSpace ℝ (Fin d))
    (ε : ℝ) :
    ∃ (m : ℕ) (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)),
      (m : ℝ) ≤ 64 * ε⁻¹ ^ 2 * log (2 * (max N 1 : ℕ)) ∧
      ∀ i j, (1 - ε) * ‖x i - x j‖ ^ 2 ≤ ‖T (x i - x j)‖ ^ 2 ∧
        ‖T (x i - x j)‖ ^ 2 ≤ (1 + ε) * ‖x i - x j‖ ^ 2 := by
  have hsub : Subsingleton (Fin N) := (Fintype.card_le_one_iff_subsingleton).mp (by simpa using hN)
  have hlog : 0 < log (2 * (max N 1 : ℕ)) := by
    refine log_pos ?_; exact_mod_cast (by omega : (1 : ℕ) < 2 * max N 1)
  refine ⟨0, 0, ?_, ?_⟩
  · nlinarith [hlog, sq_nonneg (ε⁻¹)]
  · intro i j; have hij : i = j := Subsingleton.elim i j; subst hij; simp

/-- At least two points: one finite sign matrix meets the Johnson–Lindenstrauss bound. -/
private lemma jl_many_points {d N : ℕ} (hN : 2 ≤ N) (x : Fin N → EuclideanSpace ℝ (Fin d))
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ (m : ℕ) (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)),
      (m : ℝ) ≤ 64 * ε⁻¹ ^ 2 * log (2 * (N : ℕ)) ∧
      ∀ i j, (1 - ε) * ‖x i - x j‖ ^ 2 ≤ ‖T (x i - x j)‖ ^ 2 ∧
        ‖T (x i - x j)‖ ^ 2 ≤ (1 + ε) * ‖x i - x j‖ ^ 2 := by
  let θ : ℝ := 24 * log (2 * (N : ℝ) ^ 2) / ε ^ 2
  let m : ℕ := Nat.ceil θ + 1
  have hθ0 : 0 ≤ θ := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    exact div_nonneg (mul_nonneg (by norm_num) (log_nonneg (by nlinarith))) (sq_nonneg _)
  have hm0 : 0 < m := by dsimp [m]; omega
  have hmcast : (m : ℝ) = (Nat.ceil θ : ℝ) + 1 := by simp [m]
  have hmθ : θ < (m : ℝ) := by linarith [hmcast, Nat.le_ceil θ]
  have hm2 : (m : ℝ) < θ + 2 := by linarith [hmcast, Nat.ceil_lt_add_one hθ0]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hgap : 24 * log (2 * (N : ℝ) ^ 2) + 2 * ε ^ 2 ≤ 64 * log (2 * (N : ℝ)) := by
    have hsq : ε ^ 2 < 1 := pow_lt_one₀ hε0.le hε1 two_ne_zero
    have hlog : 2 * ε ^ 2 ≤ 40 * log 2 := by nlinarith [log_two_gt_d9, hsq]
    have hlogN : 0 ≤ log (N : ℝ) := log_nonneg (by exact_mod_cast (by omega : (1 : ℕ) ≤ N))
    rw [log_mul (by norm_num) (by positivity : (N : ℝ) ^ 2 ≠ 0), log_pow]
    rw [log_mul (by norm_num) hN0]
    simp only [Nat.cast_ofNat]
    linarith [hlog, hlogN]
  have hmbound : (m : ℝ) ≤ 64 * ε⁻¹ ^ 2 * log (2 * (N : ℕ)) := by
    have hε2 : 0 < ε ^ 2 := by positivity
    have hθ : θ + 2 ≤ 64 * log (2 * (N : ℝ)) / ε ^ 2 := by
      dsimp [θ]; nth_rw 2 [(mul_div_cancel_right₀ (2 : ℝ) hε2.ne').symm]
      rw [← add_div, div_le_div_iff_of_pos_right hε2]; simpa [add_comm] using hgap
    rw [show log (2 * (N : ℕ)) = log (2 * (N : ℝ)) by congr 1]
    calc (m : ℝ) ≤ 64 * log (2 * (N : ℝ)) / ε ^ 2 := (le_of_lt hm2).trans hθ
      _ = 64 * ε⁻¹ ^ 2 * log (2 * (N : ℝ)) := by rw [div_eq_mul_inv, inv_pow]; ring
  have htail : (N : ℝ) ^ 2 * 2 * exp (-(m : ℝ) * ε ^ 2 / 24) < 1 := by
    have hlogpos : 0 < 2 * (N : ℝ) ^ 2 := by positivity
    have hcmp : -(m : ℝ) * ε ^ 2 / 24 < -log (2 * (N : ℝ) ^ 2) := by
      have hε2 : 0 < ε ^ 2 := by positivity
      nlinarith [(div_lt_iff₀ hε2).mp
        (by simpa [θ] using hmθ : 24 * log (2 * (N : ℝ) ^ 2) / ε ^ 2 < (m : ℝ))]
    have hsmall : exp (-(m : ℝ) * ε ^ 2 / 24) < (2 * (N : ℝ) ^ 2)⁻¹ := by
      calc exp (-(m : ℝ) * ε ^ 2 / 24) < exp (-log (2 * (N : ℝ) ^ 2)) := exp_lt_exp.mpr hcmp
        _ = (2 * (N : ℝ) ^ 2)⁻¹ := by rw [exp_neg, exp_log hlogpos]
    calc (N : ℝ) ^ 2 * 2 * exp (-(m : ℝ) * ε ^ 2 / 24) <
          (N : ℝ) ^ 2 * 2 * (2 * (N : ℝ) ^ 2)⁻¹ := by gcongr
      _ = 1 := by field_simp
  let bad : (Fin N × Fin N) → SignMat m d → Prop := fun q ω =>
    (1 + ε) * ‖x q.1 - x q.2‖ ^ 2 < rowEnergy (fun t => (x q.1 - x q.2) t) ω ∨
      rowEnergy (fun t => (x q.1 - x q.2) t) ω < (1 - ε) * ‖x q.1 - x q.2‖ ^ 2
  have hpair : ∀ q, signProp (bad q) ≤ 2 * exp (-(m : ℝ) * ε ^ 2 / 24) := by
    intro q
    let a : Fin d → ℝ := fun t => (x q.1 - x q.2) t
    have hdev := rademacher_deviation hm0 a hε0 hε1
    have hnorm : ∑ j, (a j) ^ 2 = ‖x q.1 - x q.2‖ ^ 2 := by simp [a, EuclideanSpace.real_norm_sq_eq]
    simp only [a, hnorm] at hdev; simpa [bad, rowEnergy] using hdev
  have hC : 0 < (Fintype.card (SignMat m d) : ℝ) := by exact_mod_cast Fintype.card_pos
  let δ : ℝ := 2 * exp (-(m : ℝ) * ε ^ 2 / 24)
  have hbad : signProp (fun ω => ∃ q, bad q ω) < 1 := by
    have hunion : ((Finset.univ.filter (fun ω => ∃ q, bad q ω)).card : ℝ) ≤
        ∑ q : Fin N × Fin N, ((Finset.univ.filter (bad q)).card : ℝ) := by
      exact_mod_cast card_filter_exists_le (p := bad)
    have hle : ∀ q, ((Finset.univ.filter (bad q)).card : ℝ) ≤
        (Fintype.card (SignMat m d) : ℝ) * δ := by
      intro q; rw [← div_le_iff₀' hC]; simpa [signProp, δ] using hpair q
    have hcard : (Fintype.card (Fin N × Fin N) : ℝ) = (N : ℝ) ^ 2 := by
      simp [Fintype.card_prod, Fintype.card_fin, pow_two]
    have hstep1 : signProp (fun ω => ∃ q, bad q ω) ≤
        (∑ q, ((Finset.univ.filter (bad q)).card : ℝ)) / (Fintype.card (SignMat m d) : ℝ) := by
      simpa [signProp] using div_le_div_of_nonneg_right hunion hC.le
    have hstep2 : (∑ q, ((Finset.univ.filter (bad q)).card : ℝ)) /
        (Fintype.card (SignMat m d) : ℝ) ≤ (N : ℝ) ^ 2 * δ := by
      calc (∑ q, ((Finset.univ.filter (bad q)).card : ℝ)) / (Fintype.card (SignMat m d) : ℝ) ≤
            (∑ q : Fin N × Fin N, (Fintype.card (SignMat m d) : ℝ) * δ) /
              (Fintype.card (SignMat m d) : ℝ) :=
          div_le_div_of_nonneg_right (Finset.sum_le_sum fun q _ => hle q) hC.le
        _ = (N : ℝ) ^ 2 * δ := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, δ]; field_simp
    exact (hstep1.trans hstep2).trans_lt (by convert htail using 1; ring)
  have hlt : (Finset.univ.filter (fun ω => ∃ q, bad q ω)).card < Fintype.card (SignMat m d) := by
    exact Nat.cast_lt.mp ((div_lt_one hC).mp (by simpa [signProp] using hbad))
  obtain ⟨ω, hω⟩ : ∃ ω : SignMat m d, ¬ ∃ q, bad q ω := by
    by_contra! hall
    have : Finset.univ.filter (fun ω => ∃ q, bad q ω) = Finset.univ := by
      ext ω; constructor
      · intro _; exact Finset.mem_univ _
      · intro _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall ω⟩
    simp only [this, Finset.card_univ] at hlt; exact lt_irrefl _ hlt
  refine ⟨m, jlMap m d ω, hmbound, fun i j => ?_⟩
  have hgood : ¬ bad (i, j) ω := fun h => hω ⟨(i, j), h⟩
  have hZ : ‖jlMap m d ω (x i - x j)‖ ^ 2 =
      rowEnergy (fun t => (x i - x j) t) ω := norm_sq_jlMap ω (x i - x j)
  have hnot : ¬ ((1 + ε) * ‖x i - x j‖ ^ 2 < rowEnergy (fun t => (x i - x j) t) ω ∨
      rowEnergy (fun t => (x i - x j) t) ω < (1 - ε) * ‖x i - x j‖ ^ 2) := by
    simpa [bad] using hgood
  simp only [not_or, not_lt] at hnot; rw [hZ]; exact ⟨hnot.2, hnot.1⟩

/-- Explicit Johnson–Lindenstrauss dimension reduction with constant `64`. -/
lemma johnson_lindenstrauss_explicit :
    ∀ (d N : ℕ) (x : Fin N → EuclideanSpace ℝ (Fin d)) (ε : ℝ), 0 < ε → ε < 1 →
    ∃ (m : ℕ) (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)),
      (m : ℝ) ≤ 64 * ε⁻¹ ^ 2 * Real.log (2 * (max N 1 : ℕ)) ∧
      ∀ i j, (1 - ε) * ‖x i - x j‖ ^ 2 ≤ ‖T (x i - x j)‖ ^ 2 ∧
        ‖T (x i - x j)‖ ^ 2 ≤ (1 + ε) * ‖x i - x j‖ ^ 2 := by
  intro d N x ε hε0 hε1
  by_cases hN : N ≤ 1
  · exact jl_few_points hN x ε
  · have hN2 : 2 ≤ N := by omega
    have hmax : max N 1 = N := max_eq_left (by omega : (1 : ℕ) ≤ N)
    obtain ⟨m, T, hm, hT⟩ := jl_many_points hN2 x hε0 hε1
    exact ⟨m, T, by simpa [hmax] using hm, hT⟩

end JohnsonLindenstrauss

end CKMA
