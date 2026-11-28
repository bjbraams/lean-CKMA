/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary

/-!
# Newton–Maclaurin inequalities for multisets and finite tuples

Normalized elementary symmetric means `E_k = e_k / choose(n, k)` of a multiset or a finite tuple
of `n` reals, Newton's log-concavity `E_{k-1} E_{k+1} ≤ E_k ^ 2` and Maclaurin's monotone chain
`E_k ^ (1 / k) ≤ E_j ^ (1 / j)` for `1 ≤ j ≤ k`.

Newton's inequality holds for every real multiset and every `k ≥ 1`: for `k ≥ n` the left side
is `0`, because `choose n (k + 1) = 0` and division by zero is `0`. Maclaurin's chain needs
nonnegative entries (the pair `(-1, -1)` has `E_1 = -1` and `E_2 = 1`); for `k > n` the left side
is `0 ^ (1 / k) = 0`.

Newton's inequality is proved by induction on the cardinality. The derivative of the real-rooted
polynomial `∏ (X + r)` is real-rooted by Mathlib's Rolle bound
`Polynomial.card_roots_le_derivative` and has the same normalized means below the top degree;
the top case `k = n - 1` reduces to `k = 1` by inverting the entries. Maclaurin's chain follows
from Newton's inequality by a telescoping product of the ratios `E_{i+1} / E_i`. The Pascal
recurrence `Multiset.esymm_cons` is TauCeti's. Source: GAPS 11.9.

## Main definitions

* `CKMA.esymmMean`: normalized elementary symmetric mean `e_k / choose(card, k)` of a multiset.
* `CKMA.normalizedElementaryMean`: normalized elementary symmetric mean `e_k / choose(n, k)` of a
  finite tuple.

## Main results

* `CKMA.newton_esymmMean`: Newton log-concavity for the normalized means of a real multiset.
* `CKMA.maclaurin_esymmMean`: Maclaurin's chain for a nonnegative multiset.
* `CKMA.newton_normalizedElementaryMean` (**11.9**): Newton log-concavity for a real tuple.
* `CKMA.maclaurin_normalizedElementaryMean` (**11.9**): Maclaurin's chain for a nonnegative
  tuple.
-/

public section

noncomputable section

namespace CKMA

open Finset Real

open scoped BigOperators

/-- Normalized elementary symmetric mean of a multiset, `e_k / choose(card, k)`. -/
@[expose]
def esymmMean (s : Multiset ℝ) (k : ℕ) : ℝ :=
  s.esymm k / (s.card.choose k : ℝ)

/-- Defining equation of `esymmMean`. -/
theorem esymmMean_def (s : Multiset ℝ) (k : ℕ) :
    esymmMean s k = s.esymm k / (s.card.choose k : ℝ) := rfl

/-- The zeroth normalized mean of a multiset is one. -/
@[simp]
theorem esymmMean_zero (s : Multiset ℝ) : esymmMean s 0 = 1 := by
  simp [esymmMean, Multiset.esymm_zero]

/-- Normalized means beyond the cardinality vanish, since `choose n k = 0` for `n < k`. -/
theorem esymmMean_of_card_lt {s : Multiset ℝ} {k : ℕ} (hk : s.card < k) : esymmMean s k = 0 := by
  rw [esymmMean, Nat.choose_eq_zero_of_lt hk, Nat.cast_zero, div_zero]

/-- The elementary symmetric mean `e_k / choose(n,k)` of a finite real tuple. -/
@[expose]
def normalizedElementaryMean {n : ℕ} (x : Fin n → ℝ) (k : ℕ) : ℝ :=
  (Finset.univ.val.map x).esymm k / (n.choose k : ℝ)

/-- Defining equation of `normalizedElementaryMean`. -/
theorem normalizedElementaryMean_def {n : ℕ} (x : Fin n → ℝ) (k : ℕ) :
    normalizedElementaryMean x k = (Finset.univ.val.map x).esymm k / (n.choose k : ℝ) := rfl

/-- The normalized mean of a tuple is the normalized mean of the multiset of its entries. -/
theorem normalizedElementaryMean_eq_esymmMean {n : ℕ} (x : Fin n → ℝ) (k : ℕ) :
    normalizedElementaryMean x k = esymmMean (Finset.univ.val.map x) k := by
  simp [normalizedElementaryMean, esymmMean]

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
        rw [← Multiset.esymm_cons, hk]
      have hnn1 : 0 ≤ s.esymm (k + 1) := esymm_nonneg hs' _
      have hnn2 : 0 ≤ a * s.esymm k := mul_nonneg ha (esymm_nonneg hs' _)
      obtain ⟨htail, hmul⟩ := (add_eq_zero_iff_of_nonneg hnn1 hnn2).mp hrec
      cases m with
      | zero => omega
      | succ m =>
        have hm' : k ≤ m := by omega
        rw [Multiset.esymm_cons, ih hs' htail (by omega)]
        rcases mul_eq_zero.mp hmul with ha0 | hk0
        · simp [ha0]
        · simp [ih hs' hk0 hm']

/-- Normalized elementary means of a nonnegative multiset are nonnegative. -/
theorem esymmMean_nonneg {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x) (k : ℕ) :
    0 ≤ esymmMean s k :=
  div_nonneg (esymm_nonneg hs k) (Nat.cast_nonneg _)

/-- Vanishing of one normalized mean propagates to every higher mean up to the cardinality. -/
private theorem esymmMean_eq_zero_of_le {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x) {k m : ℕ}
    (hk : esymmMean s k = 0) (hm : k ≤ m) (hmn : m ≤ s.card) : esymmMean s m = 0 := by
  have hC : (s.card.choose k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (hm.trans hmn)).ne'
  have he : s.esymm k = 0 := (div_eq_zero_iff.mp hk).resolve_right hC
  rw [esymmMean, esymm_eq_zero_of_le hs he hm, zero_div]

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

/-- Reversal of one linear factor with nonzero root is a constant times the inverted factor. -/
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
    · simp [hn, revAt_le (Nat.zero_le _)]
    · simp [hn, revAt_eq_self_of_lt (by omega : 0 < n), coeff_one]
  | cons a s ih =>
    have ha : a ≠ 0 := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ x ∈ s, x ≠ 0 := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [reverse_mul_of_domain, reverse_X_add_C ha, ih hs', map_mul]
    ring

/-- For a real multiset of cardinality at least two, negating the roots of the derivative of
`∏ (X + C r)` produces a multiset of cardinality one less with the same normalized means in
every degree below the original cardinality. -/
private theorem exists_derivative_esymmMean (s : Multiset ℝ) (hn : 2 ≤ s.card) :
    ∃ s' : Multiset ℝ, s'.card = s.card - 1 ∧
      ∀ j, j < s.card → esymmMean s' j = esymmMean s j := by
  set p : ℝ[X] := (s.map fun r => X + C r).prod
  have hp_deg : p.natDegree = s.card := prod_X_add_C_natDegree s
  have hp_roots : p.roots = s.map Neg.neg := by
    have hp_eq : p = ((s.map Neg.neg).map fun a => X - C a).prod := by
      rw [Multiset.map_map]
      exact congrArg Multiset.prod
        (Multiset.map_congr rfl fun r _ => X_add_C_eq_X_sub_C_neg r)
    rw [hp_eq, roots_multiset_prod_X_sub_C]
  set p' : ℝ[X] := derivative p
  have hp'_deg : p'.natDegree = s.card - 1 := by rw [natDegree_derivative, hp_deg]
  have hp'_lead : p'.leadingCoeff = (s.card : ℝ) := by
    rw [leadingCoeff_derivative, (prod_X_add_C_monic s).leadingCoeff, hp_deg, one_mul]
  have hcard' : p'.roots.card = p'.natDegree := by
    have hle1 : p.roots.card ≤ p'.roots.card + 1 := card_roots_le_derivative p
    have hle2 : p'.roots.card ≤ p'.natDegree := card_roots' p'
    rw [hp_roots, Multiset.card_map] at hle1
    rw [hp'_deg] at hle2 ⊢
    omega
  set s' : Multiset ℝ := p'.roots.map Neg.neg
  have hs'card : s'.card = s.card - 1 := by
    rw [Multiset.card_map, hcard', hp'_deg]
  refine ⟨s', hs'card, fun j hj => ?_⟩
  have hj' : j ≤ s.card - 1 := Nat.le_sub_one_of_lt hj
  have hidx : p'.natDegree - (p'.natDegree - j) = j := Nat.sub_sub_self (by rw [hp'_deg]; omega)
  have hcoeff := coeff_eq_esymm_roots_of_card hcard' (k := p'.natDegree - j) (Nat.sub_le _ _)
  rw [hidx, hp'_lead] at hcoeff
  have hroots' : p'.roots = s'.map Neg.neg := by
    simp [s', Multiset.map_map, neg_neg, Multiset.map_id']
  rw [hroots', Multiset.esymm_neg] at hcoeff
  have hleft : p'.coeff (p'.natDegree - j) = (s.card : ℝ) * s'.esymm j := by
    rw [hcoeff, mul_assoc, ← mul_assoc ((-1 : ℝ) ^ j), ← mul_pow, neg_one_mul, neg_neg,
      one_pow, one_mul]
  have hadd : (p'.natDegree - j) + 1 = s.card - j := by rw [hp'_deg]; omega
  have hright : p'.coeff (p'.natDegree - j) = s.esymm j * ((s.card - j : ℕ) : ℝ) := by
    rw [coeff_derivative, Multiset.prod_X_add_C_coeff s (by rw [hadd]; exact Nat.sub_le _ _),
      show s.card - ((p'.natDegree - j) + 1) = j by rw [hadd]; omega, ← Nat.cast_add_one, hadd]
  have hnat := Nat.choose_mul_succ_eq (s.card - 1) j
  rw [Nat.sub_add_cancel (by omega : 1 ≤ s.card)] at hnat
  have hch : ((s.card - 1).choose j : ℝ) * (s.card : ℝ) =
      (s.card.choose j : ℝ) * ((s.card - j : ℕ) : ℝ) := by exact_mod_cast hnat
  have hC' : ((s.card - 1).choose j : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj').ne'
  have hC : (s.card.choose j : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj.le).ne'
  have hn0 : (s.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : s.card ≠ 0)
  rw [esymmMean, esymmMean, hs'card, div_eq_div_iff hC' hC]
  apply mul_right_cancel₀ hn0
  linear_combination (s.card.choose j : ℝ) * (hleft.symm.trans hright) - s.esymm j * hch

/-- Elementary symmetric sums of a zero-free multiset and of its inverses are related by the
product of the entries. -/
private theorem esymm_inv {s : Multiset ℝ} (hs : ∀ x ∈ s, x ≠ 0) (j : ℕ) (hj : j ≤ s.card) :
    s.esymm j = s.prod * (s.map Inv.inv).esymm (s.card - j) := by
  have hdeg : (s.map fun r => X + C r).prod.natDegree = s.card := prod_X_add_C_natDegree s
  have hrev := reverse_prod_X_add_C hs
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
private theorem esymmMean_inv {s : Multiset ℝ} (hs : ∀ x ∈ s, x ≠ 0) {m : ℕ} (hm : m ≤ s.card) :
    esymmMean (s.map Inv.inv) m = esymmMean s (s.card - m) / s.prod := by
  have hprod : s.prod ≠ 0 := Multiset.prod_ne_zero fun h0 => hs 0 h0 rfl
  have hc : (s.map Inv.inv).card = s.card := Multiset.card_map _ _
  have hsym := esymm_inv hs (s.card - m) (Nat.sub_le _ _)
  have hsub : s.card - (s.card - m) = m := Nat.sub_sub_self hm
  rw [hsub] at hsym
  rw [esymmMean, esymmMean, hc, Nat.choose_symm hm, hsym]
  field_simp [hprod]

end SymmetricPolynomial

/-- Top case `k = n - 1` of Newton's inequality, reduced to `k = 1` by inverting the entries. -/
private theorem newton_esymmMean_top {s : Multiset ℝ} {n : ℕ} (hcard : s.card = n) (hn : 3 ≤ n)
    (hlow : esymmMean (s.map Inv.inv) 0 * esymmMean (s.map Inv.inv) 2 ≤
      esymmMean (s.map Inv.inv) 1 ^ 2) :
    esymmMean s (n - 1 - 1) * esymmMean s (n - 1 + 1) ≤ esymmMean s (n - 1) ^ 2 := by
  have hEn : esymmMean s n = s.prod := by
    rw [esymmMean, ← hcard, esymm_card, hcard, Nat.choose_self, Nat.cast_one, div_one]
  rw [show n - 1 + 1 = n by omega, hEn, show n - 1 - 1 = n - 2 by omega]
  by_cases hprod : s.prod = 0
  · rw [hprod, mul_zero]
    exact sq_nonneg _
  have hne : ∀ x ∈ s, x ≠ 0 := fun x hx h0 => hprod (Multiset.prod_eq_zero (h0 ▸ hx))
  rw [esymmMean_inv hne (Nat.zero_le _), esymmMean_inv hne (by omega),
    esymmMean_inv hne (by omega), hcard, Nat.sub_zero, hEn, div_self hprod, one_mul] at hlow
  have hmul := mul_le_mul_of_nonneg_right hlow (sq_nonneg s.prod)
  have hleft : esymmMean s (n - 2) / s.prod * s.prod ^ 2 = esymmMean s (n - 2) * s.prod := by
    field_simp [hprod]
  have hright : (esymmMean s (n - 1) / s.prod) ^ 2 * s.prod ^ 2 = esymmMean s (n - 1) ^ 2 := by
    field_simp [hprod]
  rwa [hleft, hright] at hmul

/-- Newton's inequality below the cardinality, by induction on the cardinality. -/
private theorem newton_esymmMean_of_lt {n : ℕ} :
    ∀ {s : Multiset ℝ}, s.card = n → ∀ {k : ℕ}, 1 ≤ k → k < n →
      esymmMean s (k - 1) * esymmMean s (k + 1) ≤ esymmMean s k ^ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hcard k hk hkn
    have hlow : ∀ t : Multiset ℝ, t.card = n → ∀ j, 1 ≤ j → j + 1 < n →
        esymmMean t (j - 1) * esymmMean t (j + 1) ≤ esymmMean t j ^ 2 := by
      intro t hct j hj hjlt
      obtain ⟨t', hcard', hmean⟩ := exists_derivative_esymmMean t (by omega)
      have hrec := ih (n - 1) (by omega) (hcard'.trans (by rw [hct])) hj (by omega)
      rwa [hmean (j - 1) (by omega), hmean j (by omega), hmean (j + 1) (by omega)] at hrec
    by_cases hbd : k + 1 < n
    · exact hlow s hcard k hk hbd
    obtain rfl : k = n - 1 := by omega
    by_cases hn2 : n = 2
    · subst hn2
      obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp hcard
      simp only [esymmMean]
      norm_num
      nlinarith [sq_nonneg (a - b)]
    exact newton_esymmMean_top hcard (by omega)
      (hlow _ (by rw [Multiset.card_map, hcard]) 1 le_rfl (by omega))

/-- Newton log-concavity `E_{k-1} E_{k+1} ≤ E_k ^ 2` for the normalized elementary means of a
real multiset, for every `k ≥ 1`. For `k ≥ card` the left side is `0`. -/
theorem newton_esymmMean (s : Multiset ℝ) {k : ℕ} (hk : 1 ≤ k) :
    esymmMean s (k - 1) * esymmMean s (k + 1) ≤ esymmMean s k ^ 2 := by
  rcases lt_or_ge k s.card with hkn | hkn
  · exact newton_esymmMean_of_lt rfl hk hkn
  · rw [esymmMean_of_card_lt (by omega : s.card < k + 1), mul_zero]
    exact sq_nonneg _

/-- A sequence with `E 0 = 1` that is positive and log-concave up to `k` satisfies
`E k ^ j ≤ E j ^ k` for `j ≤ k`: the ratios `E (i + 1) / E i` decrease. -/
private theorem pow_le_pow_of_logConcave {E : ℕ → ℝ} {j k : ℕ} (h0 : E 0 = 1)
    (hpos : ∀ r, r ≤ k → 0 < E r)
    (hlc : ∀ i, i + 1 < k → E (i + 2) * E i ≤ E (i + 1) * E (i + 1)) (hj : 1 ≤ j)
    (hjk : j ≤ k) : E k ^ j ≤ E j ^ k := by
  let ρ : ℕ → ℝ := fun i => E (i + 1) / E i
  have hρ0 : ∀ i, i < k → 0 ≤ ρ i := fun i hi => div_nonneg (hpos _ hi).le (hpos i hi.le).le
  have hρ_anti : ∀ i, i + 1 < k → ρ (i + 1) ≤ ρ i := fun i hi =>
    (div_le_div_iff₀ (hpos (i + 1) (by omega)) (hpos i (by omega))).mpr (hlc i hi)
  have hstep : ∀ d i, i + d < k → ρ (i + d) ≤ ρ i := by
    intro d
    induction d with
    | zero => intro i _; simp
    | succ d ih => exact fun i hi => (hρ_anti (i + d) (by omega)).trans (ih i (by omega))
  have hupper : ∀ i, j ≤ i → i < k → ρ i ≤ ρ (j - 1) := fun i hi hik => by
    simpa [show j - 1 + (i - (j - 1)) = i by omega] using hstep (i - (j - 1)) (j - 1) (by omega)
  have hlower : ∀ i, i < j → ρ (j - 1) ≤ ρ i := fun i hi => by
    simpa [show i + (j - 1 - i) = j - 1 by omega] using hstep (j - 1 - i) i (by omega)
  have hfac : ∀ m, m ≤ k → E m = ∏ i ∈ Finset.range m, ρ i := by
    intro m hm
    induction m with
    | zero => simp [h0]
    | succ m ih =>
      rw [Finset.prod_range_succ, ← ih (by omega), mul_div_cancel₀ _ (hpos m (by omega)).ne']
  have hprod : E k = E j * ∏ i ∈ Finset.Ico j k, ρ i := by
    rw [hfac k le_rfl, hfac j hjk, Finset.prod_range_mul_prod_Ico _ hjk]
  set c : ℝ := ρ (j - 1)
  have hc0 : 0 ≤ c := hρ0 (j - 1) (by omega)
  have hPle : ∏ i ∈ Finset.Ico j k, ρ i ≤ c ^ (k - j) := by
    rw [← Nat.card_Ico, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun i hi => hρ0 i (Finset.mem_Ico.mp hi).2)
      (fun i hi => hupper i (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2)
  have hQge : c ^ j ≤ E j := by
    rw [hfac j hjk]
    calc c ^ j = ∏ _i ∈ Finset.range j, c := by rw [Finset.prod_const, Finset.card_range]
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hc0) fun i hi =>
          hlower i (Finset.mem_range.mp hi)
  have hEj : 0 ≤ E j := (hpos j hjk).le
  calc E k ^ j = E j ^ j * (∏ i ∈ Finset.Ico j k, ρ i) ^ j := by rw [hprod, mul_pow]
    _ ≤ E j ^ j * (c ^ j) ^ (k - j) := by
        rw [← pow_mul, mul_comm j, pow_mul]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
          (Finset.prod_nonneg fun i hi => hρ0 i (Finset.mem_Ico.mp hi).2) hPle j)
          (pow_nonneg hEj j)
    _ ≤ E j ^ j * E j ^ (k - j) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (pow_nonneg hc0 j) hQge _) (pow_nonneg hEj j)
    _ = E j ^ k := by rw [← pow_add, Nat.add_sub_of_le hjk]

/-- Maclaurin's chain `E_k ^ (1 / k) ≤ E_j ^ (1 / j)` for `1 ≤ j ≤ k` and a nonnegative multiset.
For `k` beyond the cardinality the left side is `0`. -/
theorem maclaurin_esymmMean {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x) {j k : ℕ} (hj : 1 ≤ j)
    (hjk : j ≤ k) : esymmMean s k ^ (1 / (k : ℝ)) ≤ esymmMean s j ^ (1 / (j : ℝ)) := by
  have hE0 : ∀ r, 0 ≤ esymmMean s r := esymmMean_nonneg hs
  by_cases hEk : esymmMean s k = 0
  · rw [hEk, Real.zero_rpow (one_div_ne_zero (Nat.cast_ne_zero.mpr (by omega : k ≠ 0)))]
    exact Real.rpow_nonneg (hE0 j) _
  have hkns : k ≤ s.card := by
    by_contra h
    exact hEk (esymmMean_of_card_lt (by omega))
  have hpos : ∀ r, r ≤ k → 0 < esymmMean s r := fun r hr =>
    (hE0 r).lt_of_ne fun hr0 => hEk (esymmMean_eq_zero_of_le hs hr0.symm hr hkns)
  have hnat : esymmMean s k ^ j ≤ esymmMean s j ^ k :=
    pow_le_pow_of_logConcave (esymmMean_zero s) hpos (fun i _ => by
      simpa [pow_two, mul_comm] using newton_esymmMean s (k := i + 1) (by omega)) hj hjk
  have hkj : 0 < (j : ℝ) * (k : ℝ) :=
    mul_pos (by exact_mod_cast (by omega : 0 < j)) (by exact_mod_cast (by omega : 0 < k))
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg (hE0 k) _) (Real.rpow_nonneg (hE0 j) _)
    hkj).mp
  rw [← Real.rpow_mul (hE0 k), ← Real.rpow_mul (hE0 j)]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  rw [show (1 / (k : ℝ)) * ((j : ℝ) * k) = j by field_simp [hk0],
    show (1 / (j : ℝ)) * ((j : ℝ) * k) = k by field_simp [hj0], Real.rpow_natCast,
    Real.rpow_natCast]
  exact hnat

/-- **11.9**: Newton log-concavity `E_{k-1} E_{k+1} ≤ E_k ^ 2` of the normalized elementary
symmetric means of a real tuple, for every `k ≥ 1`. -/
theorem newton_normalizedElementaryMean {n k : ℕ} (x : Fin n → ℝ) (hk : 1 ≤ k) :
    normalizedElementaryMean x (k - 1) * normalizedElementaryMean x (k + 1) ≤
      normalizedElementaryMean x k ^ 2 := by
  simpa only [normalizedElementaryMean_eq_esymmMean] using newton_esymmMean _ hk

/-- **11.9**: Maclaurin's chain `E_k ^ (1 / k) ≤ E_j ^ (1 / j)` for `1 ≤ j ≤ k` and a
nonnegative tuple, allowing zero entries. -/
theorem maclaurin_normalizedElementaryMean {n j k : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hj : 1 ≤ j) (hjk : j ≤ k) :
    normalizedElementaryMean x k ^ (1 / (k : ℝ)) ≤
      normalizedElementaryMean x j ^ (1 / (j : ℝ)) := by
  simp only [normalizedElementaryMean_eq_esymmMean]
  exact maclaurin_esymmMean (by simpa using hx) hj hjk

end CKMA
