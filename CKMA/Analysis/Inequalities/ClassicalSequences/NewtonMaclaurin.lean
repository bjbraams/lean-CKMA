/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

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
# Newton–Maclaurin inequalities for multisets and finite tuples

Normalized elementary symmetric means of finite tuples and multisets, together with Newton
log-concavity and Maclaurin's monotone chain for nonnegative entries. Newton's inequality is
derived from Mathlib's Rolle bound `Polynomial.card_roots_le_derivative`.
Sources: GAPS 11.9.

## Main definitions

* `CKMA.normalizedElementaryMean`: normalized elementary symmetric mean `e_k / choose(n, k)` of a
  finite tuple.
* `CKMA.elemMean`: normalized elementary symmetric mean of a multiset.

## Main results

* `CKMA.newton_elemMean`: Newton log-concavity for the normalized elementary means of a
  nonnegative multiset.
* `CKMA.maclaurin_elemMean`: Maclaurin's comparison of normalized elementary means of a
  nonnegative multiset.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Finset Real

open scoped BigOperators

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

/-- Normalized elementary symmetric mean of a multiset, `e_k / choose(card, k)`. -/
def elemMean (s : Multiset ℝ) (k : ℕ) : ℝ :=
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
theorem newton_elemMean {n : ℕ} :
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
theorem maclaurin_elemMean {n j k : ℕ} {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x)
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
    have hP0 : 0 ≤ P :=
      Finset.prod_nonneg fun i hi => hρ0 i (by simp [Finset.mem_Ico] at hi; omega)
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

end CKMA
