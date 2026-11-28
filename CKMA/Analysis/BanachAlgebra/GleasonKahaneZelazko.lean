/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Complex.Basic

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The Gleason–Kahane–Żelazko theorem

A complex-linear functional `F` on a complex Banach algebra with `F 1 = 1` that vanishes at no
invertible element is multiplicative. Continuity of `F` and commutativity of the algebra are not
assumed. The argument follows Kaniuth's comparison of polynomial coefficients: the roots of the
polynomial `λ ↦ F ((λ • 1 - x) ^ n)` lie in the spectrum of `x`, and comparing its two leading
coefficients with the elementary symmetric functions of the roots bounds
`‖F x ^ 2 - F (x ^ 2)‖` by a constant over `n`. Hence `F` preserves squares, and a
square-preserving normalized linear functional is multiplicative.
Source: GAPS 20.19.

## Main results

* `CKMA.gleason_kahane_zelazko`: the Gleason–Kahane–Żelazko theorem.
-/

public section

noncomputable section

namespace CKMA

open Filter Topology Polynomial

/-- A vector bounded in norm by `C / n` for every integer `n ≥ 2` is zero. -/
private theorem eq_zero_of_norm_le_div_nat {E : Type*} [NormedAddCommGroup E] {z : E} {C : ℝ}
    (h : ∀ n : ℕ, 2 ≤ n → ‖z‖ ≤ C / (n : ℝ)) : z = 0 :=
  norm_eq_zero.mp <| le_antisymm (ge_of_tendsto (tendsto_const_div_atTop_nhds_zero_nat C)
    (eventually_atTop.2 ⟨2, h⟩)) (norm_nonneg _)

/-- A complex-linear map sending `1` to `1` and preserving squares is multiplicative. -/
private theorem linearMap_mul_of_sq {A : Type*} [Ring A] [Algebra ℂ A] (F : A →ₗ[ℂ] ℂ)
    (hF : F 1 = 1) (hsq : ∀ x : A, F (x ^ 2) = (F x) ^ 2) (a b : A) :
    F (a * b) = F a * F b := by
  have htwo (z : A) : F ((2 : A) * z) = 2 * F z := by
    rw [← one_add_one_eq_two, add_mul, one_mul, map_add]
    ring
  have hsym (x y : A) : F (x * y + y * x) = 2 * F x * F y := by
    have hexp : (x + y) ^ 2 = x ^ 2 + (x * y + y * x) + y ^ 2 := by noncomm_ring
    have hsplit : F (x ^ 2 + (x * y + y * x) + y ^ 2) =
        F (x ^ 2) + F (x * y + y * x) + F (y ^ 2) := by
      rw [map_add, map_add]
    calc
      F (x * y + y * x)
          = F ((x + y) ^ 2) - F (x ^ 2) - F (y ^ 2) := by
            rw [hexp, hsplit]
            ring
      _ = (F (x + y)) ^ 2 - (F x) ^ 2 - (F y) ^ 2 := by
            rw [hsq (x + y), hsq x, hsq y]
      _ = (F x + F y) ^ 2 - (F x) ^ 2 - (F y) ^ 2 := by rw [map_add]
      _ = 2 * F x * F y := by ring
  let a0 : A := a - (F a) • (1 : A)
  have hFa0 : F a0 = 0 := by simp [a0, hF]
  have hid : (a0 * b - b * a0) ^ 2 + (a0 * b + b * a0) ^ 2 =
      (2 : A) * (a0 * (b * a0 * b) + (b * a0 * b) * a0) := by noncomm_ring
  have hFsum : F (a0 * b + b * a0) = 0 := by rw [hsym, hFa0]; ring
  have hFdiff : F (a0 * b - b * a0) = 0 := by
    have hsumsq :
        (F (a0 * b - b * a0)) ^ 2 + (F (a0 * b + b * a0)) ^ 2 = 0 := by
      calc
        (F (a0 * b - b * a0)) ^ 2 + (F (a0 * b + b * a0)) ^ 2
            = F ((a0 * b - b * a0) ^ 2) + F ((a0 * b + b * a0) ^ 2) := by
              rw [← hsq (a0 * b - b * a0), ← hsq (a0 * b + b * a0)]
        _ = 2 * F (a0 * (b * a0 * b) + (b * a0 * b) * a0) := by
              rw [← map_add, hid, htwo]
        _ = 2 * (2 * F a0 * F (b * a0 * b)) := by rw [hsym]
        _ = 0 := by rw [hFa0]; ring
    rw [hFsum] at hsumsq
    exact sq_eq_zero_iff.mp (by simpa using hsumsq)
  have hFa0b : F (a0 * b) = 0 := by
    have h1 : F (a0 * b) + F (b * a0) = 0 := by rw [← map_add]; exact hFsum
    have h2 : F (a0 * b) - F (b * a0) = 0 := by rw [← map_sub]; exact hFdiff
    have hdouble : F (a0 * b) + F (a0 * b) =
        (F (a0 * b) + F (b * a0)) + (F (a0 * b) - F (b * a0)) := by ring
    have hzero : 2 * F (a0 * b) = 0 := by rw [two_mul, hdouble, h1, h2, add_zero]
    exact (mul_eq_zero.mp hzero).resolve_left two_ne_zero
  have ha : a = a0 + (F a) • (1 : A) := by simp [a0]
  calc
    F (a * b) = F ((a0 + (F a) • 1) * b) := by conv_lhs => rw [ha]
    _ = F (a0 * b + ((F a) • 1) * b) := by rw [add_mul]
    _ = F (a0 * b) + F (((F a) • (1 : A)) * b) := by rw [map_add]
    _ = F (((F a) • (1 : A)) * b) := by rw [hFa0b, zero_add]
    _ = F ((F a) • b) := by rw [Algebra.smul_mul_assoc, one_mul]
    _ = F a * F b := by rw [map_smul, smul_eq_mul]

/-- Binomial polynomial comparing `F ((lam • 1 - x) ^ n)` with the values `F (x ^ k)`. -/
private def gkzNewton {A : Type*} [Ring A] [Algebra ℂ A] (F : A →ₗ[ℂ] ℂ) (x : A) (n : ℕ) :
    ℂ[X] :=
  ∑ m ∈ Finset.range (n + 1),
    Polynomial.monomial m ((n.choose m : ℂ) * (-1) ^ (n - m) * F (x ^ (n - m)))

/-- The coefficient of `X ^ k` in `gkzNewton` is the corresponding binomial term. -/
private theorem gkzNewton_coeff {A : Type*} [Ring A] [Algebra ℂ A] (F : A →ₗ[ℂ] ℂ) (x : A)
    {n k : ℕ} (hk : k ≤ n) :
    (gkzNewton F x n).coeff k =
      (n.choose k : ℂ) * (-1) ^ (n - k) * F (x ^ (n - k)) := by
  rw [gkzNewton, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single k]
  · simp
  · intro m _ hmk
    simp [Polynomial.coeff_monomial, hmk]
  · intro hkmem
    exact (hkmem (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))).elim

/-- `gkzNewton` is monic of degree `n` when `F` is normalized. -/
private theorem gkzNewton_monic {A : Type*} [Ring A] [Algebra ℂ A] (F : A →ₗ[ℂ] ℂ)
    (hF : F 1 = 1) (x : A) (n : ℕ) : (gkzNewton F x n).Monic := by
  refine monic_of_natDegree_le_of_coeff_eq_one n ?_ ?_
  · refine natDegree_sum_le_of_forall_le _ _ ?_
    intro m hm
    exact (Polynomial.natDegree_monomial_le _).trans
      (Nat.le_of_lt_succ (Finset.mem_range.mp hm))
  · rw [gkzNewton_coeff F x le_rfl, Nat.sub_self, pow_zero, pow_zero, Nat.choose_self,
      Nat.cast_one, one_mul, one_mul, hF]

/-- The degree of a normalized `gkzNewton` polynomial is exactly `n`. -/
private theorem gkzNewton_natDegree {A : Type*} [Ring A] [Algebra ℂ A] (F : A →ₗ[ℂ] ℂ)
    (hF : F 1 = 1) (x : A) (n : ℕ) : (gkzNewton F x n).natDegree = n := by
  have hle : (gkzNewton F x n).natDegree ≤ n := by
    refine natDegree_sum_le_of_forall_le _ _ ?_
    intro m hm
    exact (Polynomial.natDegree_monomial_le _).trans
      (Nat.le_of_lt_succ (Finset.mem_range.mp hm))
  have hge : n ≤ (gkzNewton F x n).natDegree :=
    le_natDegree_of_ne_zero <| by
      rw [gkzNewton_coeff F x le_rfl, Nat.sub_self, pow_zero, pow_zero, Nat.choose_self,
        Nat.cast_one, one_mul, one_mul, hF]
      exact one_ne_zero
  exact le_antisymm hle hge

/-- One binomial summand maps under `F` to the matching monomial evaluation. -/
private theorem gkz_binom_term {A : Type*} [Ring A] [Algebra ℂ A] (F : A →ₗ[ℂ] ℂ) (x : A)
    (lam : ℂ) (n m : ℕ) :
    F ((lam • (1 : A)) ^ m * (-x) ^ (n - m) * (n.choose m : A)) =
      ((n.choose m : ℂ) * (-1) ^ (n - m) * F (x ^ (n - m))) * lam ^ m := by
  have hpow : (lam • (1 : A)) ^ m = lam ^ m • (1 : A) := by
    rw [← Algebra.algebraMap_eq_smul_one, ← map_pow (algebraMap ℂ A) lam m,
      Algebra.algebraMap_eq_smul_one]
  have hneg1 : (-1 : A) = algebraMap ℂ A (-1 : ℂ) := by rw [map_neg, map_one]
  have hneg : (-x) ^ (n - m) = (-1 : ℂ) ^ (n - m) • x ^ (n - m) := by
    rw [neg_pow, hneg1, ← map_pow (algebraMap ℂ A) (-1) (n - m),
      Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc, one_mul]
  have hcast : (n.choose m : A) = (n.choose m : ℂ) • (1 : A) := by
    rw [← Algebra.algebraMap_eq_smul_one, ← map_natCast (algebraMap ℂ A)]
  set k : ℕ := n - m
  rw [hpow, hneg, hcast]
  have hmul : (lam ^ m • (1 : A)) * (((-1 : ℂ) ^ k) • x ^ k) =
      (lam ^ m * (-1) ^ k) • x ^ k := by
    rw [Algebra.smul_mul_assoc, one_mul, smul_smul]
  rw [hmul, Algebra.mul_smul_comm, mul_one, smul_smul, map_smul]
  ring

/-- Evaluating `gkzNewton` recovers `F` on the binomial expansion of `(lam • 1 - x) ^ n`. -/
private theorem gkzNewton_eval {A : Type*} [Ring A] [Algebra ℂ A] (F : A →ₗ[ℂ] ℂ) (x : A)
    (lam : ℂ) (n : ℕ) :
    (gkzNewton F x n).eval lam = F ((lam • (1 : A) - x) ^ n) := by
  have hcomm : Commute (lam • (1 : A)) x := by
    simpa [Algebra.algebraMap_eq_smul_one] using Algebra.commute_algebraMap_left lam x
  rw [sub_eq_add_neg, (hcomm.neg_right).add_pow n, map_sum, gkzNewton,
    Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl ?_
  intro m _
  rw [Polynomial.eval_monomial, gkz_binom_term]

/-- The first elementary symmetric function is the sum of the multiset. -/
private theorem esymm_one_eq_sum (s : Multiset ℂ) : s.esymm 1 = s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_add, Multiset.sum_add,
      Multiset.powersetCard_zero_left, Nat.zero_add, ← Multiset.esymm, ih]
    simp [Multiset.map_singleton, Multiset.sum_singleton, add_comm]

/-- Scalar multiplication passes through a multiset sum. -/
private theorem multiset_sum_map_mul_left (c : ℂ) (s : Multiset ℂ) :
    (s.map (fun x => c * x)).sum = c * s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih, mul_add]

/-- The second elementary symmetric function splits off one element. -/
private theorem esymm_two_cons (a : ℂ) (s : Multiset ℂ) :
    (a ::ₘ s).esymm 2 = a * s.sum + s.esymm 2 := by
  have hcross :
      ((Multiset.powersetCard 1 s).map (fun t => (a ::ₘ t).prod)).sum = a * s.sum := by
    rw [Multiset.powersetCard_one, Multiset.map_map]
    simp only [Function.comp_def, Multiset.prod_cons, Multiset.prod_singleton]
    exact multiset_sum_map_mul_left a s
  rw [Multiset.esymm, Multiset.powersetCard_cons (n := 1), Multiset.map_add, Multiset.sum_add]
  have htwo : (1 : ℕ) + 1 = 2 := by decide
  rw [htwo, ← Multiset.esymm, Multiset.map_map]
  simp only [Function.comp_def]
  rw [hcross, add_comm]

/-- The square of a sum is the sum of squares plus twice the second elementary symmetric sum. -/
private theorem multiset_sq_sum (s : Multiset ℂ) :
    s.sum ^ 2 = (s.map (fun z => z ^ 2)).sum + 2 * s.esymm 2 := by
  induction s using Multiset.induction_on with
  | empty =>
    simp [Multiset.esymm_of_card_lt (show (0 : Multiset ℂ).card < 2 by simp)]
  | cons a s ih =>
    rw [Multiset.sum_cons]
    calc
      (a + s.sum) ^ 2 = a ^ 2 + 2 * a * s.sum + s.sum ^ 2 := by ring
      _ = a ^ 2 + 2 * a * s.sum + ((s.map (fun z => z ^ 2)).sum + 2 * s.esymm 2) := by
            rw [ih]
      _ = ((a ::ₘ s).map (fun z => z ^ 2)).sum + 2 * (a ::ₘ s).esymm 2 := by
            rw [esymm_two_cons, Multiset.map_cons, Multiset.sum_cons]
            ring

/-- A real multiset bounded above by `c` has sum at most `card • c`. -/
private theorem multiset_sum_le_card_nsmul {s : Multiset ℝ} {c : ℝ} (hc : ∀ x ∈ s, x ≤ c) :
    s.sum ≤ s.card • c := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : a ≤ c := hc a (Multiset.mem_cons_self a s)
    have hs : s.sum ≤ s.card • c :=
      ih fun x hx => hc x (Multiset.mem_cons_of_mem hx)
    rw [Multiset.sum_cons, Multiset.card_cons, add_nsmul, one_nsmul,
      add_comm (s.card • c)]
    exact add_le_add ha hs

/-- The roots of `gkzNewton F x n` for `n ≥ 2`: their sum is `n * F x`, their second elementary
symmetric function is `n.choose 2 * F (x ^ 2)`, there are `n` of them, and they lie in the
spectrum of `x` when `F` vanishes at no unit. -/
private theorem gkzNewton_roots {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (F : A →ₗ[ℂ] ℂ) (hF : F 1 = 1) (hu : ∀ a : A, IsUnit a → F a ≠ 0) (x : A) {n : ℕ}
    (hn : 2 ≤ n) :
    (gkzNewton F x n).roots.sum = (n : ℂ) * F x ∧
      (gkzNewton F x n).roots.esymm 2 = (n.choose 2 : ℂ) * F (x ^ 2) ∧
      (gkzNewton F x n).roots.card = n ∧
      ∀ lam ∈ (gkzNewton F x n).roots, lam ∈ spectrum ℂ x := by
  set p : ℂ[X] := gkzNewton F x n
  have hmonic : p.Monic := gkzNewton_monic F hF x n
  have hnat : p.natDegree = n := gkzNewton_natDegree F hF x n
  have hsub1 : n - (n - 1) = 1 := Nat.sub_sub_self (le_trans (by decide : 1 ≤ 2) hn)
  have hsub2 : n - (n - 2) = 2 := Nat.sub_sub_self hn
  have hcoeff1 : p.coeff (n - 1) = -((n : ℂ) * F x) := by
    rw [gkzNewton_coeff F x (Nat.sub_le n 1), hsub1, pow_one, pow_one]
    have hchoose : (n.choose (n - 1) : ℂ) = n := by
      rw [Nat.choose_symm (le_trans (by decide : 1 ≤ 2) hn), Nat.choose_one_right]
    rw [hchoose]
    ring
  have hcoeff2 : p.coeff (n - 2) = (n.choose 2 : ℂ) * F (x ^ 2) := by
    rw [gkzNewton_coeff F x (Nat.sub_le n 2), hsub2]
    rw [Nat.choose_symm hn]
    simp
  have hv1 := Polynomial.coeff_eq_esymm_roots_of_splits (IsAlgClosed.splits p)
    (show n - 1 ≤ p.natDegree by rw [hnat]; exact Nat.sub_le n 1)
  have hv2 := Polynomial.coeff_eq_esymm_roots_of_splits (IsAlgClosed.splits p)
    (show n - 2 ≤ p.natDegree by rw [hnat]; exact Nat.sub_le n 2)
  rw [hmonic, hnat, hsub1, pow_one, one_mul, esymm_one_eq_sum] at hv1
  rw [hmonic, hnat, hsub2, one_mul] at hv2
  refine ⟨?_, ?_, by rw [IsAlgClosed.card_roots_eq_natDegree, hnat], ?_⟩
  · have hv1' : p.coeff (n - 1) = -p.roots.sum := by rw [hv1]; ring
    have : -p.roots.sum = -((n : ℂ) * F x) := by rw [← hv1', hcoeff1]
    exact neg_inj.mp this
  · have hpow : (-1 : ℂ) ^ 2 = 1 := by norm_num
    rw [hpow, one_mul] at hv2
    rw [← hv2, hcoeff2]
  · intro lam hlam
    rw [Polynomial.mem_roots hmonic.ne_zero] at hlam
    rw [Polynomial.IsRoot.def] at hlam
    have heval : F ((lam • (1 : A) - x) ^ n) = 0 := by
      rw [← gkzNewton_eval, hlam]
    have hnu : ¬ IsUnit ((lam • (1 : A) - x) ^ n) := fun hunit => hu _ hunit heval
    rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
    intro hu1
    exact hnu ((isUnit_pow_iff (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hn))).mpr hu1)

/-- A multiset of `n` complex numbers in the closed disk of radius `R`, with sum `n * c` and
second elementary symmetric function `n.choose 2 * d`, satisfies
`n * ‖c ^ 2 - d‖ ≤ R ^ 2 + ‖d‖`. -/
private theorem nat_mul_norm_sq_sub_le_of_roots {s : Multiset ℂ} {n : ℕ} {c d : ℂ} {R : ℝ}
    (hn : 2 ≤ n) (hsum : s.sum = (n : ℂ) * c) (hes2 : s.esymm 2 = (n.choose 2 : ℂ) * d)
    (hcard : s.card = n) (hR : ∀ z ∈ s, ‖z‖ ≤ R) :
    (n : ℝ) * ‖c ^ 2 - d‖ ≤ R ^ 2 + ‖d‖ := by
  set δ : ℂ := c ^ 2 - d
  have hsqnorm : ‖(s.map (fun z : ℂ => z ^ 2)).sum‖ ≤ (n : ℝ) * R ^ 2 := by
    refine (norm_multiset_sum_le _).trans ?_
    rw [Multiset.map_map]
    simp only [Function.comp_def]
    have hmap : (s.map (fun z => ‖z ^ 2‖)).sum = (s.map (fun z => ‖z‖ ^ 2)).sum :=
      congrArg Multiset.sum (Multiset.map_congr rfl fun z _ => norm_pow z 2)
    rw [hmap]
    have hle : (s.map (fun z => ‖z‖ ^ 2)).sum ≤ (s.map (fun z => ‖z‖ ^ 2)).card • R ^ 2 :=
      multiset_sum_le_card_nsmul fun t ht => by
        obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp ht
        exact pow_le_pow_left₀ (norm_nonneg _) (hR z hz) 2
    rw [Multiset.card_map, hcard, nsmul_eq_mul] at hle
    exact hle
  have hchoose : 2 * (n.choose 2 : ℂ) = (n : ℂ) * ((n : ℂ) - 1) := by
    rw [Nat.cast_choose_two]
    field_simp
  have hdiff : (n : ℂ) ^ 2 * δ = (s.map (fun z : ℂ => z ^ 2)).sum - (n : ℂ) * d := by
    have hid := multiset_sq_sum s
    rw [hsum, hes2] at hid
    have hsub : (s.map (fun z : ℂ => z ^ 2)).sum =
        ((n : ℂ) * c) ^ 2 - 2 * ((n.choose 2 : ℂ) * d) := by
      rw [eq_sub_iff_add_eq]
      exact hid.symm
    rw [hsub, ← mul_assoc, hchoose]
    ring
  have htri : ‖(n : ℂ) ^ 2 * δ‖ ≤ (n : ℝ) * (R ^ 2 + ‖d‖) := by
    calc
      ‖(n : ℂ) ^ 2 * δ‖ = ‖(s.map (fun z : ℂ => z ^ 2)).sum - (n : ℂ) * d‖ := by rw [hdiff]
      _ ≤ ‖(s.map (fun z : ℂ => z ^ 2)).sum‖ + ‖(n : ℂ) * d‖ := norm_sub_le _ _
      _ ≤ (n : ℝ) * R ^ 2 + (n : ℝ) * ‖d‖ := by
            rw [norm_mul, Complex.norm_natCast]
            exact add_le_add hsqnorm le_rfl
      _ = (n : ℝ) * (R ^ 2 + ‖d‖) := by ring
  have hnpos : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn
  have hmul : (n : ℝ) ^ 2 * ‖δ‖ ≤ (n : ℝ) * (R ^ 2 + ‖d‖) := by
    simpa [norm_mul, norm_pow, Complex.norm_natCast, mul_assoc] using htri
  rw [pow_two, mul_assoc] at hmul
  exact le_of_mul_le_mul_left hmul hnpos

/-- Normalized invertible-preserving linear functionals preserve squares. -/
private theorem gkz_preserves_sq {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (F : A →ₗ[ℂ] ℂ) (hF : F 1 = 1)
    (hu : ∀ a : A, IsUnit a → F a ≠ 0) (x : A) : F (x ^ 2) = (F x) ^ 2 := by
  have hδ : ∀ n : ℕ, 2 ≤ n →
      ‖(F x) ^ 2 - F (x ^ 2)‖ ≤ ((‖x‖ * ‖(1 : A)‖) ^ 2 + ‖F (x ^ 2)‖) / (n : ℝ) := by
    intro n hn
    obtain ⟨hsum, hes2, hcard, hroot⟩ := gkzNewton_roots F hF hu x hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn
    rw [le_div_iff₀ hnpos, mul_comm]
    exact nat_mul_norm_sq_sub_le_of_roots hn hsum hes2 hcard fun z hz =>
      spectrum.norm_le_norm_mul_of_mem (hroot z hz)
  exact eq_comm.mp (sub_eq_zero.mp (eq_zero_of_norm_le_div_nat hδ))

/-- **20.19**, Gleason–Kahane–Żelazko: a normalized complex linear functional nonzero on
units is multiplicative. Continuity and commutativity are not assumed. -/
theorem gleason_kahane_zelazko {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (F : A →ₗ[ℂ] ℂ) (hF : F 1 = 1)
    (hu : ∀ a : A, IsUnit a → F a ≠ 0) : ∀ a b : A, F (a * b) = F a * F b :=
  fun a b => linearMap_mul_of_sq F hF (fun x => gkz_preserves_sq F hF hu x) a b

end CKMA
