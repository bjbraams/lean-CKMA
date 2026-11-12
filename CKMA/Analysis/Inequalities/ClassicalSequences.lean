/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Newton–Maclaurin and discrete Hardy inequalities

Normalized elementary symmetric means of finite tuples, Newton log-concavity and
Maclaurin's chain for nonnegative entries. Cesàro averages use the first `n+1` terms;
Hardy's inequality and its optimal constant are expressed by extended nonnegative sums.
Elementary symmetric polynomials, real powers and infinite sums reuse Mathlib.
Newton's inequality is read off the derivative by Mathlib's Rolle bound
`Polynomial.card_roots_le_derivative`.
Sources: GAPS 11.9 and 11.32.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Finset Real Filter

open scoped BigOperators ENNReal Topology

/-- The elementary symmetric mean `e_k / choose(n,k)` of a finite real tuple. -/
def normalizedElementaryMean {n : ℕ} (x : Fin n → ℝ) (k : ℕ) : ℝ :=
  (Finset.univ.val.map x).esymm k / (n.choose k : ℝ)

/-- The zeroth symmetric mean is one, including the empty tuple. -/
@[simp]
theorem normalizedElementaryMean_zero {n : ℕ} (x : Fin n → ℝ) :
    normalizedElementaryMean x 0 = 1 := by
  simp [normalizedElementaryMean]

/-- Elementary symmetric sums of a nonnegative multiset are nonnegative. -/
private theorem esymm_nonneg {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x) (k : ℕ) :
    0 ≤ s.esymm k := by
  rw [Multiset.esymm]
  refine Multiset.sum_nonneg ?_
  intro t ht
  obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp ht
  exact Multiset.prod_nonneg fun x hx =>
    hs x (Multiset.mem_of_le (Multiset.mem_powersetCard.mp hu).1 hx)

/-- Pascal recurrence for an elementary symmetric sum. -/
private theorem esymm_cons (a : ℝ) (s : Multiset ℝ) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  rw [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map]
  simp_rw [Function.comp_def, Multiset.prod_cons]
  rw [Multiset.sum_map_mul_left]
  rfl

/-- The top elementary symmetric sum is the product of the entries. -/
private theorem esymm_card (s : Multiset ℝ) : s.esymm s.card = s.prod := by
  simp [Multiset.esymm, Multiset.powersetCard_self]

/-- A vanishing elementary symmetric sum of a nonnegative multiset forces all higher ones
to vanish. -/
private theorem esymm_eq_zero_of_le {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x) {k : ℕ}
    (hk : s.esymm k = 0) {m : ℕ} (hm : k ≤ m) : s.esymm m = 0 := by
  induction s using Multiset.induction generalizing k m with
  | empty =>
    cases k with
    | zero => simp [Multiset.esymm_zero] at hk
    | succ k =>
      exact Multiset.esymm_of_card_lt (by rw [Multiset.card_zero]; omega)
  | cons a s ih =>
    cases k with
    | zero => simp [Multiset.esymm_zero] at hk
    | succ k =>
      have ha : 0 ≤ a := hs a (Multiset.mem_cons_self a s)
      have hs' : ∀ x ∈ s, 0 ≤ x := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
      have hrec : s.esymm (k + 1) + a * s.esymm k = 0 := by
        rw [← esymm_cons, hk]
      have hnn1 : 0 ≤ s.esymm (k + 1) := esymm_nonneg hs' _
      have hnn2 : 0 ≤ a * s.esymm k := mul_nonneg ha (esymm_nonneg hs' _)
      obtain ⟨htail, hmul⟩ := (add_eq_zero_iff_of_nonneg hnn1 hnn2).mp hrec
      cases m with
      | zero => omega
      | succ m =>
        have hm' : k ≤ m := by omega
        rw [esymm_cons, ih hs' htail (by omega)]
        rcases mul_eq_zero.mp hmul with ha0 | hk0
        · simp [ha0]
        · simp [ih hs' hk0 hm']

/-- Binomial weight in Newton's inequality:
`(n.choose k)^2 / ((n.choose (k-1))*(n.choose (k+1))) = ((n-k+1)*(k+1))/(k*(n-k))`. -/
private theorem choose_newton_ratio (n k : ℕ) (hk : 1 ≤ k) (hkn : k < n) :
    ((n.choose k : ℝ) ^ 2) /
        ((n.choose (k - 1) : ℝ) * (n.choose (k + 1) : ℝ)) =
      ((n - k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) /
        ((k : ℝ) * ((n - k : ℕ) : ℝ)) := by
  have h1 := Nat.choose_succ_right_eq n (k - 1)
  rw [Nat.sub_add_cancel hk, show n - (k - 1) = n - k + 1 by omega] at h1
  have h2 := Nat.choose_succ_right_eq n k
  have h1R : (n.choose k : ℝ) * (k : ℝ) =
      (n.choose (k - 1) : ℝ) * ((n - k + 1 : ℕ) : ℝ) := by exact_mod_cast h1
  have h2R : (n.choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) =
      (n.choose k : ℝ) * ((n - k : ℕ) : ℝ) := by exact_mod_cast h2
  have hb : (n.choose (k - 1) : ℝ) * (n.choose (k + 1) : ℝ) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · exact_mod_cast (Nat.choose_pos (by omega : k - 1 ≤ n)).ne'
    · exact_mod_cast (Nat.choose_pos (by omega : k + 1 ≤ n)).ne'
  have hd : (k : ℝ) * ((n - k : ℕ) : ℝ) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · exact_mod_cast (by omega : k ≠ 0)
    · exact_mod_cast (by omega : n - k ≠ 0)
  rw [div_eq_div_iff hb hd]
  calc
      (n.choose k : ℝ) ^ 2 * ((k : ℝ) * ((n - k : ℕ) : ℝ))
        = ((n.choose k : ℝ) * (k : ℝ)) *
            ((n.choose k : ℝ) * ((n - k : ℕ) : ℝ)) := by ring
      _ = ((n.choose (k - 1) : ℝ) * ((n - k + 1 : ℕ) : ℝ)) *
            ((n.choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ)) := by rw [h1R, h2R]
      _ = (((n - k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)) *
            ((n.choose (k - 1) : ℝ) * (n.choose (k + 1) : ℝ)) := by ring

/-- Normalized elementary symmetric mean of a multiset, `e_k / choose(card, k)`. -/
private def elemMean (s : Multiset ℝ) (k : ℕ) : ℝ :=
  s.esymm k / (s.card.choose k : ℝ)

/-- Normalized elementary means of a nonnegative multiset are nonnegative. -/
private theorem elemMean_nonneg {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x) (k : ℕ) :
    0 ≤ elemMean s k :=
  div_nonneg (esymm_nonneg hs k) (Nat.cast_nonneg _)

/-- Vanishing of one normalized mean propagates to every higher mean up to the cardinality. -/
private theorem elemMean_eq_zero_of_le {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x) {k m : ℕ}
    (hk : elemMean s k = 0) (hm : k ≤ m) (hmn : m ≤ s.card) : elemMean s m = 0 := by
  have hC : (s.card.choose k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (hm.trans hmn)).ne'
  have he : s.esymm k = 0 := (div_eq_zero_iff.mp hk).resolve_right hC
  rw [elemMean, esymm_eq_zero_of_le hs he hm, zero_div]

section SymmetricPolynomial

open Polynomial

/-- Each linear factor `X + C r` is `X - C (-r)`. -/
private theorem X_add_C_eq_X_sub_C_neg (r : ℝ) : X + C r = X - C (-r) := by
  have h : (C r : ℝ[X]) = -C (-r) := by rw [C_neg, neg_neg]
  rw [h, sub_eq_add_neg]

/-- Degree of `∏ (X + C r)` is the number of factors. -/
private theorem prod_X_add_C_natDegree (s : Multiset ℝ) :
    (s.map fun r => X + C r).prod.natDegree = s.card := by
  have hmon : ∀ p ∈ s.map fun r => X + C r, p.Monic := by
    intro p hp
    obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp hp
    exact monic_X_add_C r
  rw [natDegree_multiset_prod_of_monic (s.map fun r => X + C r) hmon]
  simp [Multiset.map_map, Function.comp_apply, Multiset.map_const', Multiset.sum_replicate]

/-- `∏ (X + C r)` is monic. -/
private theorem prod_X_add_C_monic (s : Multiset ℝ) :
    (s.map fun r => X + C r).prod.Monic :=
  monic_multiset_prod_of_monic s (fun r => X + C r) fun r _ => monic_X_add_C r

/-- A polynomial with nonnegative coefficients and positive leading coefficient is positive
on the positive reals. -/
private theorem eval_pos_of_coeff_nonneg {p : ℝ[X]} {a : ℝ} (ha : 0 < a)
    (hcoeff : ∀ n, 0 ≤ p.coeff n) (hlead : 0 < p.leadingCoeff) : 0 < p.eval a := by
  rw [eval_eq_sum_range]
  have hmem : p.natDegree ∈ Finset.range (p.natDegree + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_self _)
  have hcoeff0 : 0 < p.coeff p.natDegree := by rwa [leadingCoeff] at hlead
  have hterm : 0 < p.coeff p.natDegree * a ^ p.natDegree :=
    mul_pos hcoeff0 (pow_pos ha _)
  exact lt_of_lt_of_le hterm <| Finset.single_le_sum (f := fun i => p.coeff i * a ^ i)
    (fun i _ => mul_nonneg (hcoeff i) (pow_nonneg ha.le _)) hmem

/-- Reversal of one positive linear factor is a constant times the inverted factor. -/
private theorem reverse_X_add_C {r : ℝ} (hr : r ≠ 0) :
    (X + C r).reverse = C r * (X + C r⁻¹) := by
  ext n
  rw [coeff_reverse, natDegree_X_add_C, coeff_C_mul, coeff_add, coeff_X, coeff_C, coeff_add,
    coeff_X, coeff_C]
  by_cases hn0 : n = 0
  · simp [hn0, revAt_le (Nat.zero_le _), mul_inv_cancel₀ hr]
  · by_cases hn1 : n = 1
    · simp [hn1, revAt_le le_rfl]
    · simp [revAt_eq_self_of_lt (by omega : 1 < n), hn0, Ne.symm hn1]

/-- Reversal of `∏ (X + C r)` for a zero-free multiset is the product constant times the
polynomial on the inverses. -/
private theorem reverse_prod_X_add_C {s : Multiset ℝ} (hs : ∀ x ∈ s, x ≠ 0) :
    ((s.map fun r => X + C r).prod).reverse =
      C s.prod * (s.map fun r => X + C r⁻¹).prod := by
  induction s using Multiset.induction with
  | empty =>
    ext n
    simp only [Multiset.map_zero, Multiset.prod_zero, map_one, one_mul, coeff_reverse,
      natDegree_one]
    by_cases hn : n = 0
    · simp [hn, revAt_le (Nat.zero_le _), coeff_one]
    · simp [hn, revAt_eq_self_of_lt (by omega : 0 < n), coeff_one]
  | cons a s ih =>
    have ha : a ≠ 0 := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ x ∈ s, x ≠ 0 := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [reverse_mul_of_domain, reverse_X_add_C ha, ih hs', map_mul]
    ring

/-- For nonnegative data of cardinality at least two, negating the roots of the derivative
produces a nonnegative multiset of cardinality one less with the same normalized means in
every degree below the original cardinality. -/
private theorem exists_derivative_elemMean {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x)
    (hn : 2 ≤ s.card) : ∃ s' : Multiset ℝ, (∀ x ∈ s', 0 ≤ x) ∧ s'.card = s.card - 1 ∧
      ∀ j, j < s.card → elemMean s' j = elemMean s j := by
  set p : ℝ[X] := (s.map fun r => X + C r).prod
  have hp_deg : p.natDegree = s.card := prod_X_add_C_natDegree s
  have hp_monic : p.Monic := prod_X_add_C_monic s
  have hp_roots : p.roots = s.map Neg.neg := by
    have hp_eq : p = ((s.map Neg.neg).map fun a => X - C a).prod := by
      rw [Multiset.map_map]
      exact congrArg Multiset.prod
        (Multiset.map_congr rfl fun r _ => X_add_C_eq_X_sub_C_neg r)
    rw [hp_eq, roots_multiset_prod_X_sub_C]
  have hcard_roots : p.roots.card = p.natDegree := by
    rw [hp_roots, Multiset.card_map, hp_deg]
  set p' : ℝ[X] := derivative p
  have hp'_deg : p'.natDegree = s.card - 1 := by rw [natDegree_derivative, hp_deg]
  have hp'_lead : p'.leadingCoeff = (s.card : ℝ) := by
    rw [leadingCoeff_derivative, hp_monic.leadingCoeff, hp_deg, one_mul]
  have hp_coeff : ∀ i, 0 ≤ p.coeff i := by
    intro i
    by_cases hi : i ≤ s.card
    · rw [Multiset.prod_X_add_C_coeff s hi]
      exact esymm_nonneg hs _
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [hp_deg]; omega)]
  have hp'_coeff : ∀ i, 0 ≤ p'.coeff i := by
    intro i
    rw [coeff_derivative]
    exact mul_nonneg (hp_coeff _) (add_nonneg (Nat.cast_nonneg _) zero_le_one)
  have hp'_ne : p' ≠ 0 := by
    rw [derivative_ne_zero, hp_deg]
    omega
  have hp'_eval : ∀ a : ℝ, 0 < a → 0 < p'.eval a := by
    intro a ha
    refine eval_pos_of_coeff_nonneg ha hp'_coeff ?_
    rw [hp'_lead]
    exact_mod_cast (by omega : 0 < s.card)
  have hp'_nonpos : ∀ a ∈ p'.roots, a ≤ 0 := by
    intro a ha
    rw [mem_roots hp'_ne] at ha
    by_contra hlt
    exact (hp'_eval a (not_le.mp hlt)).ne' (IsRoot.eq_zero ha)
  have hcard' : p'.roots.card = p'.natDegree := by
    have hle1 : p.roots.card ≤ p'.roots.card + 1 := card_roots_le_derivative p
    have hle2 : p'.roots.card ≤ p'.natDegree := card_roots' p'
    rw [hcard_roots, hp_deg] at hle1
    rw [hp'_deg] at hle2
    omega
  set s' : Multiset ℝ := p'.roots.map Neg.neg
  have hs' : ∀ x ∈ s', 0 ≤ x := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
    exact neg_nonneg.mpr (hp'_nonpos a ha)
  have hs'card : s'.card = s.card - 1 := by
    rw [Multiset.card_map, hcard', hp'_deg]
  refine ⟨s', hs', hs'card, ?_⟩
  intro j hj
  have hj' : j ≤ s.card - 1 := Nat.le_sub_one_of_lt hj
  have hidx : p'.natDegree - (p'.natDegree - j) = j := Nat.sub_sub_self (by rw [hp'_deg]; omega)
  have hcoeff := coeff_eq_esymm_roots_of_card hcard' (k := p'.natDegree - j) (Nat.sub_le _ _)
  rw [hidx, hp'_lead] at hcoeff
  have hroots' : p'.roots = s'.map Neg.neg := by
    simp [s', Multiset.map_map, neg_neg, Multiset.map_id']
  rw [hroots', Multiset.esymm_neg] at hcoeff
  have hone : (-1 : ℝ) ^ j * (-1) ^ j = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hleft : p'.coeff (p'.natDegree - j) = (s.card : ℝ) * s'.esymm j := by
    rw [hcoeff, mul_assoc]
    rw [show (-1 : ℝ) ^ j * ((-1) ^ j * s'.esymm j) = s'.esymm j by
      rw [← mul_assoc, hone, one_mul]]
  have hadd : (p'.natDegree - j) + 1 = s.card - j := by rw [hp'_deg]; omega
  have hcast : (↑(p'.natDegree - j) + 1 : ℝ) = ((s.card - j : ℕ) : ℝ) := by
    rw [← Nat.cast_add_one, hadd]
  have hright : p'.coeff (p'.natDegree - j) =
      s.esymm j * ((s.card - j : ℕ) : ℝ) := by
    rw [coeff_derivative]
    have hk : (p'.natDegree - j) + 1 ≤ s.card := by rw [hadd]; exact Nat.sub_le _ _
    rw [Multiset.prod_X_add_C_coeff s hk]
    rw [show s.card - ((p'.natDegree - j) + 1) = j by rw [hadd]; omega, hcast]
  have hrel : (s.card : ℝ) * s'.esymm j = ((s.card - j : ℕ) : ℝ) * s.esymm j := by
    rw [← hleft, hright, mul_comm]
  have hnat := Nat.choose_mul_succ_eq (s.card - 1) j
  rw [Nat.sub_add_cancel (by omega : 1 ≤ s.card)] at hnat
  have hch : ((s.card - 1).choose j : ℝ) * (s.card : ℝ) =
      (s.card.choose j : ℝ) * ((s.card - j : ℕ) : ℝ) := by exact_mod_cast hnat
  have hC' : ((s.card - 1).choose j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hj').ne'
  have hC : (s.card.choose j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hj.le).ne'
  have hn0 : (s.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : s.card ≠ 0)
  rw [elemMean, elemMean, hs'card]
  apply (div_eq_div_iff hC' hC).mpr
  apply mul_right_cancel₀ hn0
  calc
      (s'.esymm j * (s.card.choose j : ℝ)) * (s.card : ℝ)
        = ((s.card : ℝ) * s'.esymm j) * (s.card.choose j : ℝ) := by ring
      _ = (((s.card - j : ℕ) : ℝ) * s.esymm j) * (s.card.choose j : ℝ) := by rw [hrel]
      _ = s.esymm j * ((s.card.choose j : ℝ) * ((s.card - j : ℕ) : ℝ)) := by ring
      _ = s.esymm j * (((s.card - 1).choose j : ℝ) * (s.card : ℝ)) := by rw [← hch]
      _ = (s.esymm j * ((s.card - 1).choose j : ℝ)) * (s.card : ℝ) := by ring

/-- Inverting a positive multiset swaps elementary symmetric sums against the product. -/
private theorem esymm_inv {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 < x) (j : ℕ) (hj : j ≤ s.card) :
    s.esymm j = s.prod * (s.map Inv.inv).esymm (s.card - j) := by
  have hs0 : ∀ x ∈ s, x ≠ 0 := fun x hx => (hs x hx).ne'
  have hdeg : (s.map fun r => X + C r).prod.natDegree = s.card := prod_X_add_C_natDegree s
  have hrev := reverse_prod_X_add_C hs0
  have hcoe : ((s.map fun r => X + C r).prod.reverse).coeff j = s.esymm j := by
    rw [coeff_reverse, hdeg, revAt_le hj, Multiset.prod_X_add_C_coeff s (Nat.sub_le _ _)]
    rw [show s.card - (s.card - j) = j by omega]
  rw [hrev, coeff_C_mul] at hcoe
  have hmap : ((s.map Inv.inv).map fun r => X + C r) = s.map fun r => X + C r⁻¹ := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun _ _ => rfl
  rw [← hmap] at hcoe
  rw [Multiset.prod_X_add_C_coeff (s.map Inv.inv) (by rw [Multiset.card_map]; exact hj),
    Multiset.card_map] at hcoe
  exact hcoe.symm

/-- Normalized means of the inverted multiset are the reversed means divided by the product. -/
private theorem elemMean_inv {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 < x) {m : ℕ} (hm : m ≤ s.card) :
    elemMean (s.map Inv.inv) m = elemMean s (s.card - m) / s.prod := by
  have hprod : s.prod ≠ 0 := (Multiset.prod_pos hs).ne'
  have hc : (s.map Inv.inv).card = s.card := Multiset.card_map _ _
  have hsym := esymm_inv hs (s.card - m) (Nat.sub_le _ _)
  have hsub : s.card - (s.card - m) = m := Nat.sub_sub_self hm
  rw [hsub] at hsym
  rw [elemMean, elemMean, hc, Nat.choose_symm hm, hsym]
  field_simp [hprod]

end SymmetricPolynomial

/-- Newton log-concavity for the normalized elementary means of a nonnegative multiset. -/
private theorem newton_elemMean {n : ℕ} :
    ∀ s : Multiset ℝ, (∀ x ∈ s, 0 ≤ x) → s.card = n →
      ∀ k, 1 ≤ k → k < n →
        elemMean s (k - 1) * elemMean s (k + 1) ≤ (elemMean s k) ^ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs hcard k hk hkn
    have hlow : ∀ t : Multiset ℝ, (∀ x ∈ t, 0 ≤ x) → t.card = n →
        ∀ j, 1 ≤ j → j + 1 < n →
          elemMean t (j - 1) * elemMean t (j + 1) ≤ (elemMean t j) ^ 2 := by
      intro t ht hct j hj hjlt
      have hn2 : 2 ≤ t.card := by rw [hct]; omega
      obtain ⟨t', ht', hcard', hmean⟩ := exists_derivative_elemMean ht hn2
      have hcard'' : t'.card = n - 1 := by rw [hcard', hct]
      have hrec := ih (n - 1) (by omega) t' ht' hcard'' j hj (by omega)
      have hm1 := hmean (j - 1) (by omega)
      have hm2 := hmean j (by omega)
      have hm3 := hmean (j + 1) (by omega)
      simpa [hm1, hm2, hm3] using hrec
    by_cases hbd : k + 1 < n
    · exact hlow s hs hcard k hk hbd
    · have hkEq : k = n - 1 := by omega
      have hn2 : 2 ≤ n := by omega
      rw [hkEq]
      by_cases hnEq : n = 2
      · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp (hcard.trans hnEq)
        simp only [hnEq, elemMean]
        norm_num
        nlinarith [sq_nonneg (a - b)]
      · by_cases hprod : s.prod = 0
        · have htop : elemMean s n = 0 := by
            rw [elemMean, ← hcard, esymm_card, hcard, Nat.choose_self, Nat.cast_one, div_one,
              hprod]
          rw [show (n - 1) + 1 = n by omega, htop, mul_zero]
          exact sq_nonneg _
        · have hpos : ∀ x ∈ s, 0 < x := by
            intro x hx
            exact lt_of_le_of_ne (hs x hx) fun h0 =>
              hprod (Multiset.prod_eq_zero (by simpa [h0] using hx))
          set z : Multiset ℝ := s.map Inv.inv
          have hz : ∀ x ∈ z, 0 ≤ x := by
            intro x hx
            obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
            exact inv_nonneg.mpr (hs a ha)
          have hzcard : z.card = n := by rw [Multiset.card_map, hcard]
          have hlowz := hlow z hz hzcard 1 (by omega) (by omega)
          rw [elemMean_inv hpos (Nat.zero_le _),
            elemMean_inv hpos (by rw [hcard]; omega),
            elemMean_inv hpos (by rw [hcard]; omega), hcard] at hlowz
          have hP : 0 < s.prod := Multiset.prod_pos hpos
          have hEn : elemMean s n = s.prod := by
            rw [elemMean, ← hcard, esymm_card, hcard, Nat.choose_self, Nat.cast_one, div_one]
          simp only [Nat.sub_zero] at hlowz
          have htwo : (1 + 1 : ℕ) = 2 := rfl
          simp only [htwo] at hlowz
          rw [hEn, div_self hP.ne', one_mul] at hlowz
          have hmul := mul_le_mul_of_nonneg_right hlowz (sq_nonneg s.prod)
          have hclear : elemMean s (n - 2) * s.prod ≤ (elemMean s (n - 1)) ^ 2 := by
            have hleft : (elemMean s (n - 2) / s.prod) * s.prod ^ 2 =
                elemMean s (n - 2) * s.prod := by field_simp [hP.ne']
            have hright : ((elemMean s (n - 1) / s.prod) ^ 2) * s.prod ^ 2 =
                (elemMean s (n - 1)) ^ 2 := by field_simp [hP.ne']
            rw [← hleft, ← hright]
            simpa using hmul
          have hsub : (n - 1) - 1 = n - 2 := by omega
          rw [hsub, show (n - 1) + 1 = n by omega, hEn]
          exact hclear

/-- Maclaurin's comparison of normalized elementary means of a nonnegative multiset. -/
private theorem maclaurin_elemMean {n j k : ℕ} {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x)
    (hcard : s.card = n) (hj : 1 ≤ j) (hjk : j ≤ k) (hkn : k ≤ n) :
    elemMean s k ^ (1 / (k : ℝ)) ≤ elemMean s j ^ (1 / (j : ℝ)) := by
  set E : ℕ → ℝ := fun r => elemMean s r
  change E k ^ (1 / (k : ℝ)) ≤ E j ^ (1 / (j : ℝ))
  have hE0 : ∀ r, 0 ≤ E r := fun r => elemMean_nonneg hs r
  by_cases hEk : E k = 0
  · rw [hEk, Real.zero_rpow (one_div_ne_zero (Nat.cast_ne_zero.mpr (by omega : k ≠ 0)))]
    exact Real.rpow_nonneg (hE0 j) _
  · have hkns : k ≤ s.card := by rw [hcard]; exact hkn
    have hpos : ∀ r, r ≤ k → 0 < E r := by
      intro r hr
      refine lt_of_le_of_ne (hE0 r) ?_
      intro hr0
      exact hEk <| by
        simpa [E] using elemMean_eq_zero_of_le hs (by simpa [E] using hr0.symm) hr hkns
    let ρ : ℕ → ℝ := fun i => E (i + 1) / E i
    have hρ0 : ∀ i, i < k → 0 ≤ ρ i := by
      intro i hi
      exact div_nonneg (hE0 _) (hpos i hi.le).le
    have hρ_anti : ∀ i, i + 1 < k → ρ (i + 1) ≤ ρ i := by
      intro i hi
      have hNew : E (i + 2) * E i ≤ E (i + 1) * E (i + 1) := by
        have hN := newton_elemMean s hs hcard (i + 1) (by omega) (by omega)
        simpa [E, pow_two, mul_comm] using hN
      have hi0 : 0 < E i := hpos i (by omega)
      have hi1 : 0 < E (i + 1) := hpos (i + 1) (by omega)
      have hdiv : E (i + 2) / E (i + 1) ≤ E (i + 1) / E i :=
        (div_le_div_iff₀ hi1 hi0).mpr hNew
      simpa [ρ] using hdiv
    have hstep : ∀ d i, i + d < k → ρ (i + d) ≤ ρ i := by
      intro d
      induction d with
      | zero => intro i hi; simp
      | succ d ih =>
        intro i hi
        exact (hρ_anti (i + d) (by omega)).trans (ih i (by omega))
    have hupper : ∀ i, j ≤ i → i < k → ρ i ≤ ρ (j - 1) := by
      intro i hi hik
      have hid : i = (j - 1) + (i - (j - 1)) := by omega
      rw [hid]
      exact hstep (i - (j - 1)) (j - 1) (by omega)
    have hlower : ∀ i, i < j → ρ (j - 1) ≤ ρ i := by
      intro i hi
      have hid : j - 1 = i + (j - 1 - i) := by omega
      rw [hid]
      exact hstep (j - 1 - i) i (by omega)
    have hfac : ∀ m, m ≤ k → E m = ∏ i ∈ Finset.range m, ρ i := by
      intro m hm
      induction m with
      | zero => simp [E, elemMean, Multiset.esymm_zero]
      | succ m ih =>
        have hm' : m ≤ k := Nat.le_of_succ_le hm
        rw [Finset.prod_range_succ, ← ih hm']
        have hEm : E m ≠ 0 := (hpos m hm').ne'
        calc
          E (m + 1) = E (m + 1) * (E m / E m) := by rw [div_self hEm, mul_one]
          _ = E (m + 1) * E m / E m := by rw [mul_div_assoc']
          _ = E m * (E (m + 1) / E m) := by rw [mul_comm (E (m + 1)), mul_div_assoc]
          _ = E m * ρ m := by rw [show ρ m = E (m + 1) / E m from rfl]
    have hsplit : Finset.range j ∪ Finset.Ico j k = Finset.range k := by
      ext i
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
      omega
    have hdisj : Disjoint (Finset.range j) (Finset.Ico j k) := by
      rw [Finset.disjoint_left]
      intro i hi hjk'
      simp only [Finset.mem_range, Finset.mem_Ico] at hi hjk'
      omega
    have hprod : E k = E j * ∏ i ∈ Finset.Ico j k, ρ i := by
      rw [hfac k le_rfl, hfac j hjk, ← Finset.prod_union hdisj, hsplit]
    set P : ℝ := ∏ i ∈ Finset.Ico j k, ρ i
    set c : ℝ := ρ (j - 1)
    have hc0 : 0 ≤ c := hρ0 (j - 1) (by omega)
    have hP0 : 0 ≤ P := Finset.prod_nonneg fun i hi => hρ0 i (by simp [Finset.mem_Ico] at hi; omega)
    have hPle : P ≤ c ^ (k - j) := by
      calc
          P ≤ ∏ _i ∈ Finset.Ico j k, c := by
              refine Finset.prod_le_prod₀ (fun i hi => ?_) (fun i hi => ?_)
              · exact hρ0 i (by simp [Finset.mem_Ico] at hi; omega)
              · exact hupper i (by simp [Finset.mem_Ico] at hi; exact hi.1)
                  (by simp [Finset.mem_Ico] at hi; exact hi.2)
          _ = c ^ (k - j) := by rw [Finset.prod_const, Nat.card_Ico]
    have hQge : c ^ j ≤ E j := by
      calc
          c ^ j = ∏ _i ∈ Finset.range j, c := by rw [Finset.prod_const, Finset.card_range]
          _ ≤ ∏ i ∈ Finset.range j, ρ i := by
              refine Finset.prod_le_prod₀ (fun _ _ => hc0) (fun i hi => ?_)
              exact hlower i (by simpa [Finset.mem_range] using hi)
          _ = E j := (hfac j hjk).symm
    have hPpow : P ^ j ≤ (E j) ^ (k - j) := by
      have h1 : P ^ j ≤ (c ^ (k - j)) ^ j := pow_le_pow_left₀ hP0 hPle j
      have h2 : (c ^ j) ^ (k - j) ≤ (E j) ^ (k - j) :=
        pow_le_pow_left₀ (pow_nonneg hc0 j) hQge (k - j)
      have h3 : (c ^ (k - j)) ^ j = (c ^ j) ^ (k - j) := by
        rw [← pow_mul, mul_comm, pow_mul]
      exact h1.trans (h3.symm ▸ h2)
    have hnat : E k ^ j ≤ E j ^ k := by
      rw [hprod, mul_pow]
      calc
          E j ^ j * P ^ j ≤ E j ^ j * E j ^ (k - j) :=
            mul_le_mul_of_nonneg_left hPpow (pow_nonneg (hE0 j) j)
          _ = E j ^ (j + (k - j)) := by rw [← pow_add]
          _ = E j ^ k := by rw [Nat.add_sub_of_le hjk]
    have hkj : 0 < (j : ℝ) * (k : ℝ) :=
      mul_pos (by exact_mod_cast (by omega : 0 < j)) (by exact_mod_cast (by omega : 0 < k))
    apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg (hE0 k) _) (Real.rpow_nonneg (hE0 j) _)
      hkj).mp
    rw [← Real.rpow_mul (hE0 k), ← Real.rpow_mul (hE0 j)]
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
    have hL : (1 / (k : ℝ)) * ((j : ℝ) * k) = j := by field_simp [hk0]
    have hR : (1 / (j : ℝ)) * ((j : ℝ) * k) = k := by field_simp [hj0]
    rw [hL, hR, Real.rpow_natCast, Real.rpow_natCast]
    simpa using hnat

/-- **11.9**: Newton log-concavity of normalized elementary symmetric means. -/
theorem newton_normalizedElementaryMean {n k : ℕ} (x : Fin n → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hk : 1 ≤ k) (hkn : k < n) :
    normalizedElementaryMean x (k - 1) * normalizedElementaryMean x (k + 1) ≤
      normalizedElementaryMean x k ^ 2 := by
  set s : Multiset ℝ := Finset.univ.val.map x
  have hs : ∀ a ∈ s, 0 ≤ a := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp ha
    exact hx i
  have hcard : s.card = n := by
    rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
  simpa [normalizedElementaryMean, elemMean, s, hcard] using
    newton_elemMean s hs hcard k hk hkn

/-- Maclaurin's monotone chain of positive-root normalized means, allowing zero entries. -/
theorem maclaurin_normalizedElementaryMean {n j k : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hj : 1 ≤ j) (hjk : j ≤ k) (hkn : k ≤ n) :
    normalizedElementaryMean x k ^ (1 / (k : ℝ)) ≤
      normalizedElementaryMean x j ^ (1 / (j : ℝ)) := by
  set s : Multiset ℝ := Finset.univ.val.map x
  have hs : ∀ a ∈ s, 0 ≤ a := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp ha
    exact hx i
  have hcard : s.card = n := by
    rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin]
  simpa [normalizedElementaryMean, elemMean, s, hcard] using
    maclaurin_elemMean hs hcard hj hjk hkn

/-- Cesaro average of the first `n+1` entries, indexed from zero. -/
def hardyAverage (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (n + 1), a j) / (n + 1 : ℝ)

/-- Telescoping sum of successive differences on an initial segment. -/
private theorem sum_sub_succ_eq_sub {u : ℕ → ℝ} {N : ℕ} :
    ∑ n ∈ range N, (u n - u (n + 1)) = u 0 - u N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    ring

/-- If `A ≤ K * B^{1/p} * A^{(p-1)/p}` with nonnegative data and `1 < p`, then `A ≤ K^p * B`. -/
private theorem hardy_absorb_rpow {p A B K : ℝ} (hp : 1 < p) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hK : 0 ≤ K) (h : A ≤ K * B ^ (1 / p) * A ^ ((p - 1) / p)) : A ≤ K ^ p * B := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  rcases hA.eq_or_lt with hA0 | hApos
  · rw [← hA0]
    exact mul_nonneg (rpow_nonneg hK _) hB
  · have hexp : (1 / p) + (p - 1) / p = 1 := by
      field_simp
      ring
    have hsplit : A ^ (1 / p) * A ^ ((p - 1) / p) = A := by
      rw [← rpow_add hApos, hexp, rpow_one]
    have hfactor : 0 < A ^ ((p - 1) / p) := rpow_pos_of_pos hApos _
    have hle : A ^ (1 / p) ≤ K * B ^ (1 / p) := by
      have h' : A ^ (1 / p) * A ^ ((p - 1) / p) ≤
          K * B ^ (1 / p) * A ^ ((p - 1) / p) := by
        rwa [hsplit]
      exact le_of_mul_le_mul_right h' hfactor
    have hpow := rpow_le_rpow (rpow_nonneg hA _) hle hp0.le
    rw [← rpow_mul hA, one_div, inv_mul_cancel₀ hp0.ne', rpow_one] at hpow
    rw [mul_rpow hK (rpow_nonneg hB _), ← rpow_mul hB, inv_mul_cancel₀ hp0.ne',
      rpow_one] at hpow
    exact hpow

/-- One Elliott step: Young’s inequality rearranges a weighted power increment. -/
private theorem hardy_young_step {p : ℝ} (hp : 1 < p) (n : ℕ) {avg prev : ℝ} (havg : 0 ≤ avg)
    (hprev : 0 ≤ prev) :
    avg ^ p - (p / (p - 1)) * ((n + 1 : ℝ) * avg - (n : ℝ) * prev) * avg ^ (p - 1) ≤
      (n : ℝ) / (p - 1) * prev ^ p - (n + 1 : ℝ) / (p - 1) * avg ^ p := by
  set q : ℝ := p / (p - 1) with hq
  set z : ℝ := avg ^ (p - 1) with hz
  have hpq : p.HolderConjugate q := by
    rw [hq]
    exact HolderConjugate.conjExponent hp
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpm1 : 0 < p - 1 := sub_pos.mpr hp
  have hq0 : 0 < q := by
    rw [hq]
    exact div_pos hp0 hpm1
  have hmul : avg * z = avg ^ p := by
    rw [hz]
    nth_rw 1 [← rpow_one avg]
    rw [← rpow_add' havg (ne_of_gt (by linarith : (0 : ℝ) < 1 + (p - 1)))]
    congr 1
    ring
  have hconj_exp : (p - 1) * q = p := by
    rw [hq, div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ hpm1.ne', mul_one]
  have hconj : z ^ q = avg ^ p := by
    rw [hz, ← rpow_mul havg, hconj_exp]
  have hyoung : prev * z ≤ prev ^ p / p + avg ^ p / q := by
    rw [hz]
    have hraw := young_inequality_of_nonneg hprev (rpow_nonneg havg (p - 1)) hpq
    rwa [← rpow_mul havg, hconj_exp] at hraw
  have hcross : q * (n : ℝ) * (prev * z) ≤
      q * (n : ℝ) * (prev ^ p / p + avg ^ p / q) :=
    mul_le_mul_of_nonneg_left hyoung (mul_nonneg hq0.le (Nat.cast_nonneg n))
  have h1 : q * (n : ℝ) * (prev ^ p / p) = (q / p) * (n : ℝ) * prev ^ p := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ac_rfl
  have h2 : q * (n : ℝ) * (avg ^ p / q) = (n : ℝ) * avg ^ p := by
    rw [div_eq_mul_inv]
    calc
      q * ↑n * (avg ^ p * q⁻¹) = q * q⁻¹ * ↑n * avg ^ p := by ac_rfl
      _ = ↑n * avg ^ p := by rw [mul_inv_cancel₀ hq0.ne', one_mul]
  have hcross' : q * (n : ℝ) * (prev ^ p / p + avg ^ p / q) =
      (q / p) * (n : ℝ) * prev ^ p + (n : ℝ) * avg ^ p := by
    rw [mul_add, h1, h2]
  have hqp : q / p = 1 / (p - 1) := by
    rw [hq, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, one_mul]
    calc
      (p * (p - 1)⁻¹) * p⁻¹ = p * p⁻¹ * (p - 1)⁻¹ := by ac_rfl
      _ = (p - 1)⁻¹ := by rw [mul_inv_cancel₀ hp0.ne', one_mul]
  have hcoeff : (1 : ℝ) - q * ((n : ℝ) + 1) + (n : ℝ) = -(((n : ℝ) + 1) / (p - 1)) := by
    rw [hq]
    apply mul_right_cancel₀ hpm1.ne'
    field_simp
    ring
  have hmuln : (1 / (p - 1)) * (n : ℝ) = (n : ℝ) / (p - 1) := by
    rw [div_eq_mul_inv, one_mul, div_eq_mul_inv, mul_comm]
  have hlin : avg ^ p - q * ((n : ℝ) + 1) * avg ^ p =
      (1 - q * ((n : ℝ) + 1)) * avg ^ p := by
    set x : ℝ := avg ^ p
    ring
  calc
    avg ^ p - q * ((↑n + 1) * avg - ↑n * prev) * z
        = avg ^ p - (q * ((↑n + 1) * avg) - q * (↑n * prev)) * z := by
          rw [mul_sub]
    _ = avg ^ p - (q * ((↑n + 1) * avg) * z - q * (↑n * prev) * z) := by
          rw [sub_mul]
    _ = avg ^ p - q * ((↑n + 1) * avg) * z + q * (↑n * prev) * z := by
          abel
    _ = avg ^ p - q * (↑n + 1) * (avg * z) + q * ↑n * (prev * z) := by
          ring
    _ = avg ^ p - q * (↑n + 1) * avg ^ p + q * ↑n * (prev * z) := by
          rw [hmul]
    _ ≤ avg ^ p - q * (↑n + 1) * avg ^ p +
          q * ↑n * (prev ^ p / p + avg ^ p / q) := by
          exact add_le_add le_rfl hcross
    _ = avg ^ p - q * (↑n + 1) * avg ^ p +
          ((q / p) * ↑n * prev ^ p + ↑n * avg ^ p) := by
          rw [hcross']
    _ = (1 - q * (↑n + 1)) * avg ^ p + (q / p) * ↑n * prev ^ p + ↑n * avg ^ p := by
          rw [hlin, add_assoc]
    _ = (1 - q * (↑n + 1) + ↑n) * avg ^ p + (q / p) * ↑n * prev ^ p := by
          rw [add_right_comm, ← add_mul]
    _ = -(((n : ℝ) + 1) / (p - 1)) * avg ^ p + (1 / (p - 1)) * ↑n * prev ^ p := by
          rw [hcoeff, hqp]
    _ = ↑n / (p - 1) * prev ^ p - (↑n + 1) / (p - 1) * avg ^ p := by
          rw [hmuln, neg_mul, add_comm, ← sub_eq_add_neg]

/-- Partial sums of Cesaro means obey Hardy's inequality with the sharp constant. -/
private theorem sum_hardyAverage_pow_le {p : ℝ} (hp : 1 < p) {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (N : ℕ) : ∑ n ∈ range N, hardyAverage a n ^ p ≤
      (p / (p - 1)) ^ p * ∑ n ∈ range N, a n ^ p := by
  set q : ℝ := p / (p - 1) with hq
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpm1 : 0 < p - 1 := sub_pos.mpr hp
  have hq0 : 0 < q := by
    rw [hq]
    exact div_pos hp0 hpm1
  have hpq : p.HolderConjugate q := by
    rw [hq]
    exact HolderConjugate.conjExponent hp
  let S : ℕ → ℝ := fun k => ∑ j ∈ range k, a j
  let prev : ℕ → ℝ := fun n => if n = 0 then 0 else S n / n
  let avg : ℕ → ℝ := fun n => hardyAverage a n
  have hSnonneg : ∀ n, 0 ≤ S n := fun n => by
    simpa [S] using Finset.sum_nonneg fun j _ => ha j
  have havg : ∀ n, 0 ≤ avg n := fun n => by
    unfold avg hardyAverage
    exact div_nonneg (sum_nonneg fun j _ => ha j) (by positivity)
  have hprev : ∀ n, 0 ≤ prev n := fun n => by
    by_cases hn : n = 0
    · simp [prev, hn]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      simpa [prev, hn] using div_nonneg (hSnonneg n) hn0.le
  have hident : ∀ n, a n = (n + 1 : ℝ) * avg n - (n : ℝ) * prev n := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [avg, prev, hardyAverage, S]
    · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
      simp only [avg, hardyAverage, prev, hn, ite_false, S]
      rw [mul_div_cancel₀ _ hn1, mul_div_cancel₀ _ hn0, sum_range_succ]
      ring
  let u : ℕ → ℝ := fun n => (n : ℝ) / (p - 1) * prev n ^ p
  have hstep : ∀ n ∈ range N, avg n ^ p ≤
      q * a n * avg n ^ (p - 1) + (u n - u (n + 1)) := by
    intro n _
    have hys := hardy_young_step hp n (havg n) (hprev n)
    have hprev_succ : prev (n + 1) = avg n := by
      simp only [prev, Nat.succ_ne_zero n, ite_false, avg, hardyAverage, S]
      rw [Nat.cast_add, Nat.cast_one]
    have hu_n : u n = (n : ℝ) / (p - 1) * prev n ^ p := rfl
    have hu_succ : u (n + 1) = (n + 1 : ℝ) / (p - 1) * avg n ^ p := by
      simp only [u, hprev_succ]
      rw [Nat.cast_add, Nat.cast_one]
    rw [← hident n, ← hu_n, ← hu_succ] at hys
    have : avg n ^ p ≤ u n - u (n + 1) + q * a n * avg n ^ (p - 1) :=
      (sub_le_iff_le_add).mp hys
    linarith
  have hsum : ∑ n ∈ range N, avg n ^ p ≤ q * ∑ n ∈ range N, a n * avg n ^ (p - 1) := by
    calc
      ∑ n ∈ range N, avg n ^ p
          ≤ ∑ n ∈ range N, (q * a n * avg n ^ (p - 1) + (u n - u (n + 1))) :=
            sum_le_sum hstep
      _ = q * ∑ n ∈ range N, a n * avg n ^ (p - 1) +
            ∑ n ∈ range N, (u n - u (n + 1)) := by
            rw [sum_add_distrib]
            congr 1
            simp_rw [mul_assoc]
            rw [← mul_sum]
      _ = q * ∑ n ∈ range N, a n * avg n ^ (p - 1) + (u 0 - u N) := by
            rw [sum_sub_succ_eq_sub]
      _ ≤ q * ∑ n ∈ range N, a n * avg n ^ (p - 1) := by
            have hu0 : u 0 = 0 := by simp [u, prev]
            have huN : 0 ≤ u N :=
              mul_nonneg (div_nonneg (Nat.cast_nonneg _) hpm1.le) (rpow_nonneg (hprev N) _)
            linarith
  have hconj_exp : (p - 1) * q = p := by
    rw [hq, div_eq_mul_inv, mul_left_comm, mul_inv_cancel₀ hpm1.ne', mul_one]
  have hgg : ∀ n, (avg n ^ (p - 1)) ^ q = avg n ^ p := by
    intro n
    rw [← rpow_mul (havg n), hconj_exp]
  have hholder : ∑ n ∈ range N, a n * avg n ^ (p - 1) ≤
      (∑ n ∈ range N, a n ^ p) ^ (1 / p) * (∑ n ∈ range N, avg n ^ p) ^ (1 / q) := by
    have hraw := inner_le_Lp_mul_Lq_of_nonneg (s := range N) (f := a)
      (g := fun n => avg n ^ (p - 1)) hpq (fun n _ => ha n)
      (fun n _ => rpow_nonneg (havg n) _)
    simpa [hgg] using hraw
  have h1q : (1 : ℝ) / q = (p - 1) / p := by
    rw [hq, one_div_div]
  have hA : ∑ n ∈ range N, avg n ^ p ≤
      q * (∑ n ∈ range N, a n ^ p) ^ (1 / p) *
        (∑ n ∈ range N, avg n ^ p) ^ ((p - 1) / p) := by
    calc
      ∑ n ∈ range N, avg n ^ p ≤ q * ∑ n ∈ range N, a n * avg n ^ (p - 1) := hsum
      _ ≤ q * ((∑ n ∈ range N, a n ^ p) ^ (1 / p) *
          (∑ n ∈ range N, avg n ^ p) ^ (1 / q)) :=
            mul_le_mul_of_nonneg_left hholder hq0.le
      _ = q * (∑ n ∈ range N, a n ^ p) ^ (1 / p) *
          (∑ n ∈ range N, avg n ^ p) ^ ((p - 1) / p) := by
            rw [h1q, mul_assoc]
  have habsorb := hardy_absorb_rpow hp
    (Finset.sum_nonneg fun n _ => rpow_nonneg (havg n) _)
    (Finset.sum_nonneg fun n _ => rpow_nonneg (ha n) _) hq0.le hA
  simpa [avg, hq] using habsorb

/-- **11.32**: Hardy's discrete inequality, stated as an extended nonnegative sum. -/
theorem discrete_hardy {p : ℝ} (hp : 1 < p) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) :
    (∑' n, ENNReal.ofReal (hardyAverage a n ^ p)) ≤
      ENNReal.ofReal ((p / (p - 1)) ^ p) * ∑' n, ENNReal.ofReal (a n ^ p) := by
  set c : ℝ := (p / (p - 1)) ^ p
  have hc : 0 ≤ c := by
    exact rpow_nonneg (div_nonneg (le_of_lt (lt_trans zero_lt_one hp))
      (sub_nonneg.mpr (le_of_lt hp))) _
  have havg : ∀ n, 0 ≤ hardyAverage a n ^ p := fun n => by
    unfold hardyAverage
    exact rpow_nonneg (div_nonneg (sum_nonneg fun j _ => ha j) (by positivity)) _
  have hap : ∀ n, 0 ≤ a n ^ p := fun n => rpow_nonneg (ha n) _
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun n _ => havg n]
  have hpartial := sum_hardyAverage_pow_le hp ha N
  have hmul : ENNReal.ofReal (c * ∑ n ∈ range N, a n ^ p) =
      ENNReal.ofReal c * ENNReal.ofReal (∑ n ∈ range N, a n ^ p) :=
    ENNReal.ofReal_mul hc
  calc
    ENNReal.ofReal (∑ n ∈ range N, hardyAverage a n ^ p)
        ≤ ENNReal.ofReal (c * ∑ n ∈ range N, a n ^ p) :=
          ENNReal.ofReal_le_ofReal hpartial
    _ = ENNReal.ofReal c * ENNReal.ofReal (∑ n ∈ range N, a n ^ p) := hmul
    _ = ENNReal.ofReal c * ∑ n ∈ range N, ENNReal.ofReal (a n ^ p) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun n _ => hap n]
    _ ≤ ENNReal.ofReal c * ∑' n, ENNReal.ofReal (a n ^ p) :=
          mul_le_mul' le_rfl (ENNReal.sum_le_tsum _)

/-- Power weight `(n+1)^{-1/p}` truncated to `n < N`, used to test the Hardy constant. -/
private def hardyTrunc (p : ℝ) (N n : ℕ) : ℝ :=
  if n < N then (n + 1 : ℝ) ^ (-(1 / p)) else 0

/-- The truncated power weight is nonnegative. -/
private theorem hardyTrunc_nonneg (p : ℝ) (N n : ℕ) : 0 ≤ hardyTrunc p N n := by
  unfold hardyTrunc
  split_ifs
  · exact rpow_nonneg (by positivity) _
  · exact le_rfl

/-- The truncated power weight is supported on `n < N`. -/
private theorem hardyTrunc_support_finite (p : ℝ) (N : ℕ) :
    (Function.support (hardyTrunc p N)).Finite := by
  refine (range N).finite_toSet.subset ?_
  intro n hn
  by_contra hmem
  have hlt : ¬ n < N := by simpa [mem_range] using hmem
  apply hn
  simp [hardyTrunc, hlt]

/-- Integral lower bound for one normalized partial sum of `k^{-1/p}`. -/
private theorem hardy_weight_term_lower {p : ℝ} (hp : 1 < p) {m : ℕ} (hm : 1 ≤ m) :
    (p / (p - 1)) ^ p * (m : ℝ)⁻¹ *
        ((1 + (m : ℝ)⁻¹) ^ ((p - 1) / p) - (m : ℝ) ^ (-((p - 1) / p))) ^ p ≤
      ((∑ k ∈ Icc 1 m, (k : ℝ) ^ (-(1 / p))) / (m : ℝ)) ^ p := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpm1 : 0 < p - 1 := sub_pos.mpr hp
  set β : ℝ := (p - 1) / p with hβ
  have hβ0 : 0 < β := by
    rw [hβ]
    exact div_pos hpm1 hp0
  have hr : -1 < -(1 / p) := neg_lt_neg ((div_lt_one hp0).mpr hp)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(1 / p)))
      (Set.Icc (↑(1 : ℕ)) (↑(m + 1))) := by
    refine (antitoneOn_rpow_Ioi_of_exponent_nonpos
      (neg_nonpos.mpr (le_of_lt (by positivity : 0 < 1 / p)))).mono ?_
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := by simpa using hx.1
    exact lt_of_lt_of_le zero_lt_one hx1
  have hint_le :=
    AntitoneOn.integral_le_sum_Ico (a := 1) (b := m + 1) (by omega) hanti
  have hIco : ∑ k ∈ Ico 1 (m + 1), (k : ℝ) ^ (-(1 / p)) =
      ∑ k ∈ Icc 1 m, (k : ℝ) ^ (-(1 / p)) := by
    rw [Ico_add_one_right_eq_Icc]
  have hpow : -(1 / p) + 1 = β := by
    rw [hβ]
    field_simp
    ring
  have hinvβ : β⁻¹ = p / (p - 1) := by
    rw [hβ]
    field_simp
  have hint : ∫ x in (1 : ℕ)..(m + 1), x ^ (-(1 / p)) =
      (((m : ℝ) + 1) ^ β - 1) * (p / (p - 1)) := by
    rw [integral_rpow (Or.inl hr), hpow, Nat.cast_one, one_rpow, div_eq_mul_inv, hinvβ]
  set S : ℝ := ∑ k ∈ Icc 1 m, (k : ℝ) ^ (-(1 / p))
  set A : ℝ := ((m : ℝ) + 1) ^ β - 1
  have hA0 : 0 ≤ A := by
    have : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ β :=
      one_le_rpow (by linarith : (1 : ℝ) ≤ (m : ℝ) + 1) hβ0.le
    linarith
  have hS : A * (p / (p - 1)) ≤ S := by
    have hcast : ((m : ℝ) + 1) = ↑(m + 1) := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [← hint, hcast, ← hIco]
    exact hint_le
  have hbase : 0 ≤ A * (p / (p - 1)) / m :=
    div_nonneg (mul_nonneg hA0 (div_nonneg hp0.le hpm1.le)) hm0.le
  have hpowle : (A * (p / (p - 1)) / m) ^ p ≤ (S / m) ^ p :=
    rpow_le_rpow hbase (div_le_div_of_nonneg_right hS hm0.le) hp0.le
  have hc0 : 0 ≤ p / (p - 1) := div_nonneg hp0.le hpm1.le
  have hfactor : (A * (p / (p - 1)) / m) ^ p =
      (p / (p - 1)) ^ p * (A ^ p / (m : ℝ) ^ p) := by
    calc
      (A * (p / (p - 1)) / m) ^ p
          = (A * (p / (p - 1)) * (m : ℝ)⁻¹) ^ p := by rw [div_eq_mul_inv]
      _ = (A * (p / (p - 1))) ^ p * ((m : ℝ)⁻¹) ^ p := by
            rw [mul_rpow (mul_nonneg hA0 hc0) (inv_nonneg.mpr hm0.le)]
      _ = A ^ p * (p / (p - 1)) ^ p * ((m : ℝ) ^ p)⁻¹ := by
            rw [mul_rpow hA0 hc0, inv_rpow hm0.le]
      _ = (p / (p - 1)) ^ p * (A ^ p * ((m : ℝ) ^ p)⁻¹) := by
            rw [mul_assoc, mul_left_comm]
      _ = (p / (p - 1)) ^ p * (A ^ p / (m : ℝ) ^ p) := by
            rw [← div_eq_mul_inv]
  have hβp : β * p = p - 1 := by
    rw [hβ]
    field_simp
  have hratio : (m : ℝ)⁻¹ * (A / (m : ℝ) ^ β) ^ p = A ^ p / (m : ℝ) ^ p := by
    have hmβnonneg : 0 ≤ (m : ℝ) ^ β := rpow_nonneg hm0.le _
    calc
      (m : ℝ)⁻¹ * (A / (m : ℝ) ^ β) ^ p
          = (m : ℝ)⁻¹ * (A ^ p / ((m : ℝ) ^ β) ^ p) := by
            rw [div_rpow hA0 hmβnonneg]
      _ = (m : ℝ)⁻¹ * (A ^ p / (m : ℝ) ^ (β * p)) := by
            rw [← rpow_mul hm0.le]
      _ = (m : ℝ)⁻¹ * (A ^ p / (m : ℝ) ^ (p - 1)) := by
            rw [hβp]
      _ = (m : ℝ)⁻¹ * (A ^ p * ((m : ℝ) ^ (p - 1))⁻¹) := by
            rw [div_eq_mul_inv]
      _ = A ^ p * ((m : ℝ)⁻¹ * ((m : ℝ) ^ (p - 1))⁻¹) := by
            rw [← mul_assoc, mul_comm ((m : ℝ)⁻¹), mul_assoc]
      _ = A ^ p * ((m : ℝ) * (m : ℝ) ^ (p - 1))⁻¹ := by
            rw [← mul_inv]
      _ = A ^ p * ((m : ℝ) ^ p)⁻¹ := by
            congr 1
            nth_rw 1 [← rpow_one (m : ℝ)]
            rw [← rpow_add hm0]
            congr 1
            ring
      _ = A ^ p / (m : ℝ) ^ p := by
            rw [← div_eq_mul_inv]
  have hquot : ((m : ℝ) + 1) / m = 1 + (m : ℝ)⁻¹ := by
    field_simp
  have hshift : A / (m : ℝ) ^ β = (1 + (m : ℝ)⁻¹) ^ β - (m : ℝ) ^ (-β) := by
    calc
      A / (m : ℝ) ^ β = (((m : ℝ) + 1) ^ β - 1) / (m : ℝ) ^ β := rfl
      _ = ((m : ℝ) + 1) ^ β / (m : ℝ) ^ β - 1 / (m : ℝ) ^ β := by rw [sub_div]
      _ = (((m : ℝ) + 1) / m) ^ β - (m : ℝ) ^ (-β) := by
            rw [← div_rpow (by linarith : (0 : ℝ) ≤ (m : ℝ) + 1) hm0.le, one_div,
              ← rpow_neg hm0.le]
      _ = (1 + (m : ℝ)⁻¹) ^ β - (m : ℝ) ^ (-β) := by
            rw [hquot]
  have hgoal : (A * (p / (p - 1)) / m) ^ p =
      (p / (p - 1)) ^ p * (m : ℝ)⁻¹ *
        ((1 + (m : ℝ)⁻¹) ^ β - (m : ℝ) ^ (-β)) ^ p := by
    rw [hfactor, ← hratio, mul_assoc, hshift]
  calc
    (p / (p - 1)) ^ p * (m : ℝ)⁻¹ *
        ((1 + (m : ℝ)⁻¹) ^ β - (m : ℝ) ^ (-β)) ^ p
        = (A * (p / (p - 1)) / m) ^ p := by rw [← hgoal]
    _ ≤ (S / m) ^ p := hpowle

/-- The constant in Hardy's inequality is optimal already on finitely supported inputs. -/
theorem discrete_hardy_constant_le {p C : ℝ} (hp : 1 < p)
    (hbound : ∀ a : ℕ → ℝ, (∀ n, 0 ≤ a n) → (Function.support a).Finite →
      (∑' n, ENNReal.ofReal (hardyAverage a n ^ p)) ≤
        ENNReal.ofReal C * ∑' n, ENNReal.ofReal (a n ^ p)) :
    (p / (p - 1)) ^ p ≤ C := by
  set c : ℝ := (p / (p - 1)) ^ p
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpm1 : 0 < p - 1 := sub_pos.mpr hp
  have hc0 : 0 < c := rpow_pos_of_pos (div_pos hp0 hpm1) _
  have hC : 0 ≤ C := by
    by_contra hneg
    have hlt : C < 0 := lt_of_not_ge hneg
    let a : ℕ → ℝ := hardyTrunc p 1
    have ha : ∀ n, 0 ≤ a n := fun n => hardyTrunc_nonneg p 1 n
    have hfin := hardyTrunc_support_finite p 1
    have hbd := hbound a ha hfin
    have ha0 : a 0 = 1 := by
      simp [a, hardyTrunc, one_rpow]
    have hone : hardyAverage a 0 ^ p = 1 := by
      simp [hardyAverage, ha0, one_rpow]
    have hge : (1 : ℝ≥0∞) ≤ ∑' n, ENNReal.ofReal (hardyAverage a n ^ p) := by
      calc
        (1 : ℝ≥0∞) = ENNReal.ofReal (hardyAverage a 0 ^ p) := by simp [hone]
        _ = ∑ n ∈ range 1, ENNReal.ofReal (hardyAverage a n ^ p) := by simp
        _ ≤ ∑' n, ENNReal.ofReal (hardyAverage a n ^ p) := ENNReal.sum_le_tsum _
    have hzero : ENNReal.ofReal C = 0 := ENNReal.ofReal_of_nonpos hlt.le
    rw [hzero, zero_mul] at hbd
    exact not_lt_of_ge (hge.trans hbd) zero_lt_one
  let H : ℕ → ℝ := fun N => ∑ k ∈ Icc 1 N, (k : ℝ)⁻¹
  have hHlog : ∀ N : ℕ, Real.log ((N : ℝ) + 1) ≤ H N := by
    intro N
    have hanti : AntitoneOn (fun x : ℝ => x⁻¹) (Set.Icc (↑(1 : ℕ)) (↑(N + 1))) :=
      inv_antitoneOn_Ioi.mono fun x hx =>
        lt_of_lt_of_le zero_lt_one (by simpa using hx.1)
    have hint := AntitoneOn.integral_le_sum_Ico (a := 1) (b := N + 1) (by omega) hanti
    have heq : ∑ k ∈ Ico 1 (N + 1), (k : ℝ)⁻¹ = H N := by
      rw [Ico_add_one_right_eq_Icc]
    have hintv : ∫ x in (1 : ℕ)..(N + 1), x⁻¹ = Real.log ((N : ℝ) + 1) := by
      rw [integral_inv_of_pos (by positivity : (0 : ℝ) < (1 : ℕ)) (by positivity)]
      simp [div_one, Nat.cast_one]
    simpa [heq, hintv] using hint
  have hHtop : Tendsto H atTop atTop :=
    tendsto_atTop_mono hHlog <| tendsto_log_atTop.comp <|
      tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  set β : ℝ := (p - 1) / p
  have hβ0 : 0 < β := div_pos hpm1 hp0
  let φ : ℕ → ℝ := fun m =>
    ((1 + (m : ℝ)⁻¹) ^ β - (m : ℝ) ^ (-β)) ^ p
  have hφ_nonneg : ∀ m, 1 ≤ m → 0 ≤ φ m := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hinside : 0 ≤ (1 + (m : ℝ)⁻¹) ^ β - (m : ℝ) ^ (-β) := by
      have hone : (1 : ℝ) ≤ (1 + (m : ℝ)⁻¹) ^ β :=
        one_le_rpow (le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg m))) hβ0.le
      have hsmall : (m : ℝ) ^ (-β) ≤ 1 := by
        rw [rpow_neg hm0.le]
        exact inv_le_one_of_one_le₀ (one_le_rpow hm1r hβ0.le)
      linarith
    exact rpow_nonneg hinside _
  have hφ : Tendsto φ atTop (nhds 1) := by
    have hinv : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hbase : Tendsto (fun m : ℕ => 1 + (m : ℝ)⁻¹) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.add hinv
    have hleft : Tendsto (fun m : ℕ => (1 + (m : ℝ)⁻¹) ^ β) atTop (nhds 1) := by
      have hcont := (continuousAt_rpow_const (1 : ℝ) β (Or.inl one_ne_zero)).tendsto
      have hcomp := hcont.comp hbase
      simp only [one_rpow] at hcomp
      exact Tendsto.congr (fun _ => rfl) hcomp
    have hright : Tendsto (fun m : ℕ => (m : ℝ) ^ (-β)) atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hβ0).comp tendsto_natCast_atTop_atTop
    have hsub : Tendsto (fun m : ℕ => (1 + (m : ℝ)⁻¹) ^ β - (m : ℝ) ^ (-β)) atTop (nhds 1) := by
      simpa using hleft.sub hright
    have hcontp := (continuous_rpow_const (q := p) hp0.le).continuousAt (x := 1)
    have hcomp := hcontp.tendsto.comp hsub
    simp only [one_rpow] at hcomp
    exact Tendsto.congr (fun _ => rfl) hcomp
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ : ℝ := min (1 / 2) (ε / c)
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < 1 := by
    have hδle : δ ≤ 1 / 2 := min_le_left _ _
    have : (1 : ℝ) / 2 < 1 := by norm_num
    linarith
  have hδε : c * δ ≤ ε := by
    have hδle : δ ≤ ε / c := min_le_right _ _
    calc
      c * δ ≤ c * (ε / c) := mul_le_mul_of_nonneg_left hδle hc0.le
      _ = ε := by field_simp
  set η : ℝ := δ / 2
  have hη0 : 0 < η := by positivity
  have hη1 : η < 1 := by
    rw [show η = δ / 2 from rfl, div_lt_one (by norm_num : (0 : ℝ) < 2)]
    linarith [hδ1]
  have hsq : 1 - δ ≤ (1 - η) ^ 2 := by
    have hηdef : η = δ / 2 := rfl
    nlinarith
  have hcloseφ : ∀ᶠ m : ℕ in atTop, φ m ∈ Set.Ioo (1 - η) (1 + η) :=
    hφ.eventually (Ioo_mem_nhds (sub_lt_self 1 hη0) (lt_add_of_pos_right 1 hη0))
  obtain ⟨M0, hM0⟩ := eventually_atTop.mp hcloseφ
  let M : ℕ := max M0 1
  have hM1 : 1 ≤ M := le_max_right _ _
  have hMφ : ∀ m ≥ M, 1 - η < φ m := by
    intro m hm
    have hmem := hM0 m (le_trans (le_max_left _ _) hm)
    rw [Set.mem_Ioo] at hmem
    exact hmem.1
  have hlarge : ∀ᶠ N : ℕ in atTop, H (M - 1) / η ≤ H N ∧ M ≤ N :=
    (hHtop.eventually_ge_atTop (H (M - 1) / η)).and (eventually_ge_atTop M)
  obtain ⟨N, hNge, hNM⟩ := hlarge.exists
  have hN1 : 1 ≤ N := le_trans hM1 hNM
  have hHpos : 0 < H N := by
    have hmem : (1 : ℕ) ∈ Icc 1 N := by simp [hN1]
    have hone : (1 : ℝ)⁻¹ ≤ H N := by
      have hle := Finset.single_le_sum (f := fun k : ℕ => (k : ℝ)⁻¹)
        (fun k _ => inv_nonneg.mpr (Nat.cast_nonneg k)) hmem
      simpa [H] using hle
    have : (1 : ℝ) ≤ H N := by simpa using hone
    linarith
  let a : ℕ → ℝ := hardyTrunc p N
  have ha : ∀ n, 0 ≤ a n := fun n => hardyTrunc_nonneg p N n
  have hfin := hardyTrunc_support_finite p N
  have hbd := hbound a ha hfin
  have hpow : ∀ n, n < N → a n ^ p = (n + 1 : ℝ)⁻¹ := by
    intro n hn
    simp only [a, hardyTrunc, ite_eq_left hn]
    have hexp : -(1 / p) * p = -1 := by
      field_simp
    rw [← rpow_mul (by positivity : (0 : ℝ) ≤ (n + 1 : ℝ)), hexp, rpow_neg_one]
  have hR : ∑ n ∈ range N, a n ^ p = H N := by
    have hcast : ∑ n ∈ range N, a n ^ p = ∑ n ∈ range N, (↑(n + 1))⁻¹ := by
      refine sum_congr rfl fun n hn => ?_
      rw [hpow n (mem_range.mp hn), Nat.cast_add, Nat.cast_one]
    rw [hcast, range_eq_Ico, sum_Ico_add' (fun k : ℕ => (k : ℝ)⁻¹) 0 N (c := 1),
      Ico_add_one_right_eq_Icc]
  let S : ℕ → ℝ := fun m => ∑ k ∈ Icc 1 m, (k : ℝ) ^ (-(1 / p))
  have havg : ∀ n, n < N → hardyAverage a n = S (n + 1) / (n + 1 : ℝ) := by
    intro n hn
    have hterms : ∀ j ∈ range (n + 1), a j = (↑(j + 1)) ^ (-(1 / p)) := by
      intro j hj
      have hjN : j < N := lt_of_le_of_lt (Nat.le_of_lt_succ (mem_range.mp hj)) hn
      simp only [a, hardyTrunc, ite_eq_left hjN, Nat.cast_add, Nat.cast_one]
    simp only [hardyAverage, S]
    rw [sum_congr rfl hterms, range_eq_Ico,
      sum_Ico_add' (fun k : ℕ => (k : ℝ) ^ (-(1 / p))) 0 (n + 1) (c := 1),
      Ico_add_one_right_eq_Icc]
  have hpartial_ge : c * ∑ m ∈ Icc 1 N, φ m * (m : ℝ)⁻¹ ≤
      ∑ n ∈ range N, hardyAverage a n ^ p := by
    have hre : ∑ n ∈ range N, hardyAverage a n ^ p =
        ∑ m ∈ Icc 1 N, (S m / (m : ℝ)) ^ p := by
      rw [range_eq_Ico, ← Ico_add_one_right_eq_Icc,
        ← sum_Ico_add' (fun m : ℕ => (S m / (m : ℝ)) ^ p) 0 N (c := 1)]
      refine sum_congr rfl fun n hn => ?_
      rw [havg n (mem_Ico.mp hn).2, Nat.cast_add, Nat.cast_one]
    rw [hre, mul_sum]
    refine sum_le_sum fun m hm => ?_
    have hm1 : 1 ≤ m := (mem_Icc.mp hm).1
    have hlow := hardy_weight_term_lower hp hm1
    calc
      c * (φ m * (m : ℝ)⁻¹) = c * (m : ℝ)⁻¹ * φ m := by
        rw [mul_comm (φ m), mul_assoc]
      _ ≤ (S m / (m : ℝ)) ^ p := by
        simpa [S, φ, β] using hlow
  have hpartial_le : ∑ n ∈ range N, hardyAverage a n ^ p ≤ C * H N := by
    have hap : ∀ n, 0 ≤ a n ^ p := fun n => rpow_nonneg (ha n) _
    have havg_nonneg : ∀ n, 0 ≤ hardyAverage a n ^ p := fun n =>
      rpow_nonneg (div_nonneg (sum_nonneg fun j _ => ha j) (by positivity)) _
    have htail : ∀ n, N ≤ n → a n = 0 := fun n hn => by
      simp [a, hardyTrunc, not_lt.mpr hn]
    have hcompl : ∑' i : ↥((range N : Set ℕ)ᶜ), ENNReal.ofReal (a i ^ p) = 0 := by
      rw [ENNReal.tsum_eq_zero]
      rintro ⟨n, hn⟩
      have hnN : N ≤ n := by
        simpa [Set.mem_compl_iff, mem_coe, mem_range, not_lt] using hn
      rw [htail n hnN, zero_rpow hp0.ne', ENNReal.ofReal_zero]
    have htsumR : ∑' n, ENNReal.ofReal (a n ^ p) =
        ENNReal.ofReal (∑ n ∈ range N, a n ^ p) := by
      have hadd :=
        ENNReal.sum_add_tsum_compl (range N) (fun n => ENNReal.ofReal (a n ^ p))
      rw [hcompl, add_zero] at hadd
      rw [← hadd, ENNReal.ofReal_sum_of_nonneg fun n _ => hap n]
    have hge : ENNReal.ofReal (∑ n ∈ range N, hardyAverage a n ^ p) ≤
        ∑' n, ENNReal.ofReal (hardyAverage a n ^ p) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun n _ => havg_nonneg n]
      exact ENNReal.sum_le_tsum (range N)
    have hmul := hbd
    rw [htsumR, hR] at hmul
    have : ENNReal.ofReal (∑ n ∈ range N, hardyAverage a n ^ p) ≤
        ENNReal.ofReal C * ENNReal.ofReal (H N) := le_trans hge hmul
    rw [← ENNReal.ofReal_mul hC] at this
    have hHN : 0 ≤ C * H N := mul_nonneg hC (le_of_lt hHpos)
    exact (ENNReal.ofReal_le_ofReal_iff hHN).mp this
  have hsplit : (1 - η) * (H N - H (M - 1)) ≤ ∑ m ∈ Icc 1 N, φ m * (m : ℝ)⁻¹ := by
    have hunion : Icc 1 (M - 1) ∪ Icc M N = Icc 1 N := by
      ext k
      simp only [mem_union, mem_Icc]
      omega
    have hdisj : Disjoint (Icc 1 (M - 1)) (Icc M N) := by
      rw [disjoint_left]
      intro k hk1 hk2
      simp only [mem_Icc] at hk1 hk2
      omega
    have hsum : ∑ m ∈ Icc 1 N, φ m * (m : ℝ)⁻¹ =
        ∑ m ∈ Icc 1 (M - 1), φ m * (m : ℝ)⁻¹ + ∑ m ∈ Icc M N, φ m * (m : ℝ)⁻¹ := by
      rw [← sum_union hdisj, hunion]
    have htail : (1 - η) * ∑ m ∈ Icc M N, (m : ℝ)⁻¹ ≤
        ∑ m ∈ Icc M N, φ m * (m : ℝ)⁻¹ := by
      rw [mul_sum]
      refine sum_le_sum fun m hm => ?_
      have hmM : M ≤ m := (mem_Icc.mp hm).1
      have hinv : 0 ≤ (m : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg m)
      exact mul_le_mul_of_nonneg_right (le_of_lt (hMφ m hmM)) hinv
    have hHsplit : H N = H (M - 1) + ∑ m ∈ Icc M N, (m : ℝ)⁻¹ := by
      have hsumH : ∑ m ∈ Icc 1 N, (m : ℝ)⁻¹ =
          ∑ m ∈ Icc 1 (M - 1), (m : ℝ)⁻¹ + ∑ m ∈ Icc M N, (m : ℝ)⁻¹ := by
        rw [← sum_union hdisj, hunion]
      simpa [H] using hsumH
    have hdrop : 0 ≤ ∑ m ∈ Icc 1 (M - 1), φ m * (m : ℝ)⁻¹ := by
      refine sum_nonneg fun m hm => ?_
      exact mul_nonneg (hφ_nonneg m (mem_Icc.mp hm).1) (inv_nonneg.mpr (Nat.cast_nonneg m))
    have htail_le : (1 - η) * (H N - H (M - 1)) ≤ ∑ m ∈ Icc M N, φ m * (m : ℝ)⁻¹ := by
      rw [hHsplit, add_sub_cancel_left]
      exact htail
    exact (le_trans htail_le (le_add_of_nonneg_left hdrop)).trans_eq hsum.symm
  have hratio : (1 - η) ^ 2 ≤ (∑ m ∈ Icc 1 N, φ m * (m : ℝ)⁻¹) / H N := by
    have hprev : H (M - 1) ≤ η * H N := by
      simpa [mul_comm] using (div_le_iff₀ hη0).mp hNge
    have hdiff : (1 - η) * H N ≤ H N - H (M - 1) := by linarith
    have hcomp : (1 - η) ^ 2 * H N ≤ (1 - η) * (H N - H (M - 1)) := by
      calc
        (1 - η) ^ 2 * H N = (1 - η) * ((1 - η) * H N) := by ring
        _ ≤ (1 - η) * (H N - H (M - 1)) :=
          mul_le_mul_of_nonneg_left hdiff (by linarith)
    exact (le_div_iff₀ hHpos).mpr (hcomp.trans hsplit)
  have hclose : c * (1 - δ) ≤ C := by
    have hquot : c * (1 - δ) ≤
        c * ((∑ m ∈ Icc 1 N, φ m * (m : ℝ)⁻¹) / H N) :=
      mul_le_mul_of_nonneg_left (le_trans hsq hratio) hc0.le
    rw [mul_div_assoc'] at hquot
    have hleC : (c * ∑ m ∈ Icc 1 N, φ m * (m : ℝ)⁻¹) / H N ≤ C := by
      rw [div_le_iff₀ hHpos]
      exact le_trans hpartial_ge hpartial_le
    exact hquot.trans hleC
  have hcδ : c * (1 - δ) = c - c * δ := by ring
  linarith

end CKMA
