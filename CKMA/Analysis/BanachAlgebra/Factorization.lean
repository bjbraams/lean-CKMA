/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Order.Directed
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Fourier.FourierTransform

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.OrderClosed

/-!
# Characters, norming boundaries, Tauberian density, and factorization

The character theorem concerns normalized linear functionals on complex Banach algebras;
continuity and commutativity are not assumed. Closed norming boundaries are subsets of a
compact Hausdorff carrier, including the empty carrier. The Tauberian statement uses actual
L1 equivalence classes and measure-preserving translations on the real line.

Cohen–Hewitt factorization is formulated for a continuous bilinear action of a nonunital
real or complex Banach algebra. Its bounded approximate identity is indexed by a directed set.
The Gleason–Kahane–Żelazko argument follows Kaniuth’s comparison of polynomial coefficients.
The Shilov boundary is the intersection of maximizing sets, as in Bonsall–Duncan.
Sources: GAPS 20.19, 20.23, 20.41, and 20.47.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology MeasureTheory FourierTransform Polynomial
open scoped FourierTransform

/-- A complex number bounded by `C / n` for every integer `n ≥ 2` is zero. -/
private theorem complex_norm_le_div_nat_zero {z : ℂ} {C : ℝ}
    (h : ∀ n : ℕ, 2 ≤ n → ‖z‖ ≤ C / (n : ℝ)) : z = 0 := by
  by_cases hC : 0 < C
  · by_contra hz
    have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    obtain ⟨k, hk⟩ := exists_nat_gt (C / ‖z‖)
    have hk0 : 0 < k := by
      have hnonneg : 0 ≤ C / ‖z‖ := div_nonneg hC.le hpos.le
      by_contra hk0
      rw [Nat.eq_zero_of_not_pos hk0, Nat.cast_zero] at hk
      exact not_lt_of_ge hnonneg hk
    let n : ℕ := max k 2
    have hn : 2 ≤ n := le_max_right k 2
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast le_max_left k 2
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk0
    have hnpos : (0 : ℝ) < n := lt_of_lt_of_le hkpos hkn
    have hdiv : C / (k : ℝ) < ‖z‖ := by
      rw [div_lt_iff₀ hkpos, mul_comm]
      rwa [← div_lt_iff₀ hpos]
    have hle : C / (n : ℝ) ≤ C / (k : ℝ) :=
      div_le_div_of_nonneg_left hC.le hkpos hkn
    exact (hle.trans_lt hdiv).not_ge (h n hn)
  · have hnonpos : C / 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hC) (by norm_num)
    exact norm_eq_zero.mp <| le_antisymm ((h 2 le_rfl).trans hnonpos) (norm_nonneg _)

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

/-- Normalized invertible-preserving linear functionals preserve squares. -/
private theorem gkz_preserves_sq {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (F : A →ₗ[ℂ] ℂ) (hF : F 1 = 1)
    (hu : ∀ a : A, IsUnit a → F a ≠ 0) (x : A) : F (x ^ 2) = (F x) ^ 2 := by
  let δ : ℂ := (F x) ^ 2 - F (x ^ 2)
  let R : ℝ := ‖x‖ * ‖(1 : A)‖
  have hδ : ∀ n : ℕ, 2 ≤ n → ‖δ‖ ≤ (R ^ 2 + ‖F (x ^ 2)‖) / (n : ℝ) := by
    intro n hn
    let p : ℂ[X] := gkzNewton F x n
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
    have hsum : p.roots.sum = (n : ℂ) * F x := by
      have hv1' : p.coeff (n - 1) = -p.roots.sum := by rw [hv1]; ring
      have : -p.roots.sum = -((n : ℂ) * F x) := by rw [← hv1', hcoeff1]
      exact neg_inj.mp this
    have hes2 : p.roots.esymm 2 = (n.choose 2 : ℂ) * F (x ^ 2) := by
      have hpow : (-1 : ℂ) ^ 2 = 1 := by norm_num
      rw [hpow, one_mul] at hv2
      rw [← hv2, hcoeff2]
    have hroot : ∀ lam ∈ p.roots, lam ∈ spectrum ℂ x := by
      intro lam hlam
      rw [Polynomial.mem_roots hmonic.ne_zero] at hlam
      rw [Polynomial.IsRoot.def] at hlam
      have heval : F ((lam • (1 : A) - x) ^ n) = 0 := by
        rw [← gkzNewton_eval, hlam]
      have hnu : ¬ IsUnit ((lam • (1 : A) - x) ^ n) := fun hunit => hu _ hunit heval
      rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
      intro hu1
      exact hnu ((isUnit_pow_iff (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hn))).mpr hu1)
    have hcard : p.roots.card = n := by rw [IsAlgClosed.card_roots_eq_natDegree, hnat]
    have hsqnorm : ‖(p.roots.map (fun z : ℂ => z ^ 2)).sum‖ ≤ (n : ℝ) * R ^ 2 := by
      refine (norm_multiset_sum_le _).trans ?_
      rw [Multiset.map_map]
      simp only [Function.comp_def]
      have hmap : (p.roots.map (fun z => ‖z ^ 2‖)).sum =
          (p.roots.map (fun z => ‖z‖ ^ 2)).sum := by
        refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
        intro z _
        exact norm_pow z 2
      rw [hmap]
      have hle : (p.roots.map (fun z => ‖z‖ ^ 2)).sum ≤
          (p.roots.map (fun z => ‖z‖ ^ 2)).card • R ^ 2 :=
        multiset_sum_le_card_nsmul fun t ht => by
          obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp ht
          exact pow_le_pow_left₀ (norm_nonneg _) (spectrum.norm_le_norm_mul_of_mem (hroot z hz)) 2
      rw [Multiset.card_map, hcard, nsmul_eq_mul] at hle
      exact hle
    have hchoose : 2 * (n.choose 2 : ℂ) = (n : ℂ) * ((n : ℂ) - 1) := by
      rw [Nat.cast_choose_two]
      field_simp
    have hsumsq : (p.roots.map (fun z : ℂ => z ^ 2)).sum =
        (n : ℂ) ^ 2 * δ + (n : ℂ) * F (x ^ 2) := by
      have hid := multiset_sq_sum p.roots
      rw [hsum, hes2] at hid
      have hsub : (p.roots.map (fun z : ℂ => z ^ 2)).sum =
          ((n : ℂ) * F x) ^ 2 - 2 * ((n.choose 2 : ℂ) * F (x ^ 2)) := by
        rw [eq_sub_iff_add_eq]
        exact hid.symm
      rw [hsub, ← mul_assoc, hchoose]
      ring
    have htri : ‖(n : ℂ) ^ 2 * δ‖ ≤ (n : ℝ) * (R ^ 2 + ‖F (x ^ 2)‖) := by
      have hdiff : (n : ℂ) ^ 2 * δ =
          (p.roots.map (fun z : ℂ => z ^ 2)).sum - (n : ℂ) * F (x ^ 2) := by
        rw [hsumsq]
        ring
      calc
        ‖(n : ℂ) ^ 2 * δ‖
            = ‖(p.roots.map (fun z : ℂ => z ^ 2)).sum - (n : ℂ) * F (x ^ 2)‖ := by rw [hdiff]
        _ ≤ ‖(p.roots.map (fun z : ℂ => z ^ 2)).sum‖ + ‖(n : ℂ) * F (x ^ 2)‖ := norm_sub_le _ _
        _ ≤ (n : ℝ) * R ^ 2 + (n : ℝ) * ‖F (x ^ 2)‖ := by
              rw [norm_mul, Complex.norm_natCast]
              exact add_le_add hsqnorm le_rfl
        _ = (n : ℝ) * (R ^ 2 + ‖F (x ^ 2)‖) := by ring
    have hnpos : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn
    have hmul : (n : ℝ) ^ 2 * ‖δ‖ ≤ (n : ℝ) * (R ^ 2 + ‖F (x ^ 2)‖) := by
      simpa [norm_mul, norm_pow, Complex.norm_natCast, mul_assoc] using htri
    rw [pow_two, mul_assoc] at hmul
    have hcancel : (n : ℝ) * ‖δ‖ ≤ R ^ 2 + ‖F (x ^ 2)‖ :=
      le_of_mul_le_mul_left hmul hnpos
    rw [le_div_iff₀ hnpos, mul_comm]
    exact hcancel
  exact eq_comm.mp (sub_eq_zero.mp (complex_norm_le_div_nat_zero hδ))

/-- **20.19**, Gleason–Kahane–Żelazko: a normalized complex linear functional nonzero on
units is multiplicative. Continuity and commutativity are not assumed. -/
theorem gleason_kahane_zelazko {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (F : A →ₗ[ℂ] ℂ) (hF : F 1 = 1)
    (hu : ∀ a : A, IsUnit a → F a ≠ 0) : ∀ a b : A, F (a * b) = F a * F b :=
  fun a b => linearMap_mul_of_sq F hF (fun x => gkz_preserves_sq F hF hu x) a b

/-- A closed boundary for a uniform algebra, using the supremum convention that also
allows the zero algebra on the empty compact space. -/
def IsUniformAlgebraBoundary {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (A : Subalgebra ℂ C(K, ℂ)) (F : Set K) : Prop :=
  IsClosed F ∧ ∀ f : A, ‖f.1‖ = sSup ((fun x ↦ ‖f.1 x‖) '' F)

/-- The supremum of a norm on any set is at most the supremum norm. -/
private theorem sSup_norm_image_le {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {A : Subalgebra ℂ C(K, ℂ)} (f : A) (F : Set K) :
    sSup ((fun x => ‖f.1 x‖) '' F) ≤ ‖f.1‖ := by
  by_cases hF : ((fun x => ‖f.1 x‖) '' F).Nonempty
  · exact csSup_le hF fun r hr => by
      obtain ⟨x, -, rfl⟩ := hr
      exact f.1.norm_coe_le_norm x
  · rw [Set.not_nonempty_iff_eq_empty] at hF
    rw [hF, Real.sSup_empty]
    exact norm_nonneg _

/-- Norms are nonnegative, so their supremum on any set is nonnegative. -/
private theorem sSup_norm_image_nonneg {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {A : Subalgebra ℂ C(K, ℂ)} (f : A) (F : Set K) :
    0 ≤ sSup ((fun x => ‖f.1 x‖) '' F) := by
  by_cases hF : ((fun x => ‖f.1 x‖) '' F).Nonempty
  · obtain ⟨r, hr⟩ := hF
    obtain ⟨x, hx, rfl⟩ := hr
    exact (norm_nonneg (f.1 x)).trans <| le_csSup
      ⟨‖f.1‖, fun t ht => by
        obtain ⟨y, -, rfl⟩ := ht
        exact f.1.norm_coe_le_norm y⟩ ⟨x, hx, rfl⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hF
    rw [hF, Real.sSup_empty]

/-- On a compact carrier the supremum norm is the supremum of the pointwise norms. -/
private theorem norm_eq_sSup_univ {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (f : C(K, ℂ)) : ‖f‖ = sSup ((fun x => ‖f x‖) '' Set.univ) := by
  rw [ContinuousMap.norm_eq_iSup_norm, iSup, ← Set.image_univ]

/-- The whole carrier is a closed norming boundary. -/
private theorem isUniformAlgebraBoundary_univ {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (A : Subalgebra ℂ C(K, ℂ)) : IsUniformAlgebraBoundary A Set.univ :=
  ⟨isClosed_univ, fun f => norm_eq_sSup_univ f.1⟩

/-- Pointwise norm of a power times another algebra element. -/
private theorem norm_pow_mul_apply {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {A : Subalgebra ℂ C(K, ℂ)} (g f : A) (n : ℕ) (z : K) :
    ‖((g ^ n * f).1 z)‖ = ‖g.1 z‖ ^ n * ‖f.1 z‖ := by
  rw [Subalgebra.coe_mul, Subalgebra.coe_pow, ContinuousMap.mul_apply,
    ContinuousMap.pow_apply, norm_mul, norm_pow]

/-- A strict pointwise bound on a compact set is a strict bound on the supremum. -/
private theorem sSup_norm_image_lt {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {E : Set K} (hE : IsCompact E) {g : C(K, ℂ)} {c : ℝ} (hc : 0 < c)
    (hlt : ∀ x ∈ E, ‖g x‖ < c) : sSup ((fun x => ‖g x‖) '' E) < c := by
  by_cases hne : E.Nonempty
  · obtain ⟨x, hx, heq⟩ := hE.exists_sSup_image_eq hne
      ((continuous_norm.comp g.continuous).continuousOn (s := E))
    have hfun : (fun a : ℂ => ‖a‖) ∘ ⇑g = fun x => ‖g x‖ := funext fun _ => rfl
    rw [hfun] at heq
    rw [heq]
    exact hlt x hx
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.image_empty, Real.sSup_empty]
    exact hc

/-- A nonempty boundary attains the supremum norm of every algebra element. -/
private theorem exists_norm_eq_on_boundary {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {A : Subalgebra ℂ C(K, ℂ)} {E : Set K} (hE : IsUniformAlgebraBoundary A E)
    (hEne : E.Nonempty) (g : A) : ∃ z ∈ E, ‖g.1 z‖ = ‖g.1‖ := by
  obtain ⟨z, hz, heq⟩ := hE.1.isCompact.exists_sSup_image_eq hEne
    ((continuous_norm.comp g.1.continuous).continuousOn (s := E))
  have hfun : (fun a : ℂ => ‖a‖) ∘ ⇑(g.1) = fun x => ‖g.1 x‖ :=
    funext fun _ => rfl
  rw [hfun] at heq
  exact ⟨z, hz, heq.symm.trans (hE.2 g).symm⟩

/-- The carrierwise point-separation hypothesis is separation of points for the algebra. -/
private theorem separatesPoints_of_point_separation {K : Type*} [TopologicalSpace K]
    {A : Subalgebra ℂ C(K, ℂ)}
    (hsep : ∀ x y : K, x ≠ y → ∃ f : A, f.1 x ≠ f.1 y) : A.SeparatesPoints := by
  intro x y hxy
  obtain ⟨f, hf⟩ := hsep x y hxy
  exact ⟨⇑(f.1), ⟨f.1, f.property, rfl⟩, hf⟩

/-- Folding set differences cannot restore a point that starts outside or meets a deleted set. -/
private theorem not_mem_foldl_sdiff {α β : Type*} (l : List α) (U : α → Set β) (E : Set β)
    {z : β} (h : z ∉ E ∨ ∃ i ∈ l, z ∈ U i) :
    z ∉ l.foldl (fun G i => G \ U i) E := by
  induction l generalizing E with
  | nil =>
    cases h with
    | inl hz => exact hz
    | inr hex =>
      obtain ⟨_, hi, _⟩ := hex
      cases hi
  | cons a as ih =>
    dsimp only [List.foldl]
    refine ih (E \ U a) ?_
    cases h with
    | inl hz => exact Or.inl fun hz' => hz hz'.1
    | inr hex =>
      obtain ⟨i, hi, hz⟩ := hex
      rcases List.mem_cons.mp hi with hia | hias
      · subst hia
        exact Or.inl fun hz' => hz'.2 hz
      · exact Or.inr ⟨i, hias, hz⟩

/-- Deleting sets that preserve boundaries, one at a time, leaves a boundary. -/
private theorem boundary_foldl_sdiff {K α : Type*} [TopologicalSpace K] [CompactSpace K]
    (A : Subalgebra ℂ C(K, ℂ)) (l : List α) (U : α → Set K)
    (hdel : ∀ i ∈ l, ∀ E, IsUniformAlgebraBoundary A E →
      IsUniformAlgebraBoundary A (E \ U i))
    {E : Set K} (hE : IsUniformAlgebraBoundary A E) :
    IsUniformAlgebraBoundary A (l.foldl (fun G i => G \ U i) E) := by
  induction l generalizing E with
  | nil => exact hE
  | cons i is ih =>
    dsimp only [List.foldl]
    exact ih (fun j hj F hF => hdel j (List.mem_cons.mpr (Or.inr hj)) F hF)
      (hdel i (List.mem_cons.mpr (Or.inl rfl)) E hE)

/-- Around a point omitted by one boundary, an open set may be deleted from every boundary. -/
private theorem exists_open_boundary_sdiff {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (A : Subalgebra ℂ C(K, ℂ))
    (hsep : ∀ x y : K, x ≠ y → ∃ f : A, f.1 x ≠ f.1 y)
    {E0 : Set K} (hE0 : IsUniformAlgebraBoundary A E0) {x0 : K} (hx0 : x0 ∉ E0) :
    ∃ U : Set K, IsOpen U ∧ x0 ∈ U ∧ ∀ E : Set K, IsUniformAlgebraBoundary A E →
      IsUniformAlgebraBoundary A (E \ U) := by
  have hE0ne : E0.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hsup := hE0.2 (1 : A)
    rw [hempty, Set.image_empty, Real.sSup_empty, Subalgebra.coe_one] at hsup
    have hnorm : ‖(1 : C(K, ℂ))‖ = 1 := by
      rw [ContinuousMap.norm_eq_iSup_norm]
      have hpt : ∀ x : K, ‖(1 : C(K, ℂ)) x‖ = 1 := fun x => by
        rw [ContinuousMap.one_apply, norm_one]
      simp only [hpt]
      exact @ciSup_const ℝ K _ ⟨x0⟩ 1
    exact one_ne_zero (hnorm.symm.trans hsup)
  have hpts := separatesPoints_of_point_separation hsep
  have hex (y : E0) : ∃ f : A, f.1 x0 = 0 ∧ f.1 (y : K) = 2 := by
    classical
    have hyx : (y : K) ≠ x0 := fun h => hx0 (h ▸ y.property)
    obtain ⟨g, hgA, hg0, hg2⟩ := hpts.strongly
      (fun z => if z = (y : K) then (2 : ℂ) else 0) x0 y
    refine ⟨⟨g, hgA⟩, ?_, ?_⟩
    · rw [hg0]
      simp [Ne.symm hyx]
    · rw [hg2]
      simp
  choose f hf0 hf2 using hex
  let V : E0 → Set K := fun y => {z | 1 < ‖(f y).1 z‖}
  have hVopen : ∀ y, IsOpen (V y) := fun y =>
    isOpen_lt continuous_const (continuous_norm.comp (f y).1.continuous)
  have hcover : E0 ⊆ ⋃ y, V y := by
    intro z hz
    refine Set.mem_iUnion.mpr ⟨⟨z, hz⟩, ?_⟩
    apply Set.mem_ofPred.mpr
    rw [hf2 ⟨z, hz⟩, Complex.norm_two]
    exact one_lt_two
  obtain ⟨t, ht⟩ := hE0.1.isCompact.elim_finite_subcover V hVopen hcover
  have htne : t.Nonempty := by
    obtain ⟨z, hz⟩ := hE0ne
    obtain ⟨y, hy, -⟩ := Set.mem_iUnion₂.mp (ht hz)
    exact ⟨y, hy⟩
  let U : Set K := ⋂ y ∈ t, {z | ‖(f y).1 z‖ < 1}
  have hUopen : IsOpen U := isOpen_biInter_finset fun y _ =>
    isOpen_lt (continuous_norm.comp (f y).1.continuous) continuous_const
  have hx0U : x0 ∈ U := by
    rw [Set.mem_iInter₂]
    intro y _
    apply Set.mem_ofPred.mpr
    rw [hf0 y, norm_zero]
    exact one_pos
  have hcap : E0 ∩ U = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hzE hzU
    obtain ⟨y, hy, hyz⟩ := Set.mem_iUnion₂.mp (ht hzE)
    rw [Set.mem_iInter₂] at hzU
    exact lt_asymm hyz.out (hzU y hy).out
  have hMbd : BddAbove ((fun y : E0 => ‖(f y).1‖) '' (t : Set E0)) :=
    ((Finset.finite_toSet t).image (fun y => ‖(f y).1‖)).bddAbove
  set M : ℝ := sSup ((fun y : E0 => ‖(f y).1‖) '' (t : Set E0))
  have hMy (y : E0) (hy : y ∈ t) : ‖(f y).1‖ ≤ M :=
    le_csSup hMbd (Set.mem_image_of_mem _ hy)
  have hMgt : 1 < M := by
    obtain ⟨y, hy⟩ := htne
    have h2le : (2 : ℝ) ≤ M := by
      calc
        (2 : ℝ) = ‖(f y).1 (y : K)‖ := by rw [hf2 y, Complex.norm_two]
        _ ≤ ‖(f y).1‖ := (f y).1.norm_coe_le_norm _
        _ ≤ M := hMy y hy
    linarith
  refine ⟨U, hUopen, hx0U, ?_⟩
  intro E hE
  refine ⟨hE.1.sdiff hUopen, fun g => ?_⟩
  set N : ℝ := ‖g.1‖
  set ρ : ℝ := sSup ((fun x => ‖g.1 x‖) '' (E \ U))
  have hρle : ρ ≤ N := sSup_norm_image_le g (E \ U)
  have hρnn : 0 ≤ ρ := sSup_norm_image_nonneg g (E \ U)
  have hNle : N ≤ ρ := by
    by_contra hlt
    have hρlt : ρ < N := lt_of_not_ge hlt
    have hNpos : 0 < N := hρnn.trans_lt hρlt
    have hMpos : 0 < M := one_pos.trans hMgt
    have hratio : ρ / N < 1 := (div_lt_one hNpos).mpr hρlt
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (one_div_pos.mpr hMpos) hratio
    have hlt1 : (ρ / N) ^ n * M < 1 := by
      calc
        (ρ / N) ^ n * M < (1 / M) * M := mul_lt_mul_of_pos_right hn hMpos
        _ = 1 := by rw [one_div, inv_mul_cancel₀ hMpos.ne']
    have hpow : ρ ^ n * M < N ^ n := by
      have hNnp : 0 < N ^ n := pow_pos hNpos n
      have hrewrite : ρ ^ n * M = (ρ / N) ^ n * M * N ^ n := by
        rw [div_pow, div_mul_eq_mul_div, div_mul_cancel₀ _ (pow_ne_zero n hNpos.ne')]
      rw [hrewrite]
      calc
        (ρ / N) ^ n * M * N ^ n < 1 * N ^ n := mul_lt_mul_of_pos_right hlt1 hNnp
        _ = N ^ n := one_mul _
    have hpt (y : E0) (hy : y ∈ t) (z : K) (hz : z ∈ E) :
        ‖((g ^ n * f y).1 z)‖ < N ^ n := by
      rw [norm_pow_mul_apply]
      by_cases hzu : z ∈ U
      · have hfy : ‖(f y).1 z‖ < 1 := by
          have hzU := hzu
          rw [Set.mem_iInter₂] at hzU
          exact (hzU y hy).out
        calc
          ‖g.1 z‖ ^ n * ‖(f y).1 z‖
              ≤ N ^ n * ‖(f y).1 z‖ :=
                mul_le_mul_of_nonneg_right
                  (pow_le_pow_left₀ (norm_nonneg _) (g.1.norm_coe_le_norm z) _)
                  (norm_nonneg _)
          _ < N ^ n * 1 := mul_lt_mul_of_pos_left hfy (pow_pos hNpos n)
          _ = N ^ n := mul_one _
      · have hzE : z ∈ E \ U := ⟨hz, hzu⟩
        have hgle : ‖g.1 z‖ ≤ ρ := le_csSup
          ⟨N, fun r hr => by
            obtain ⟨w, -, rfl⟩ := hr
            exact g.1.norm_coe_le_norm w⟩ ⟨z, hzE, rfl⟩
        calc
          ‖g.1 z‖ ^ n * ‖(f y).1 z‖
              ≤ ρ ^ n * ‖(f y).1 z‖ :=
                mul_le_mul_of_nonneg_right
                  (pow_le_pow_left₀ (norm_nonneg _) hgle n) (norm_nonneg _)
          _ ≤ ρ ^ n * M := mul_le_mul_of_nonneg_left
                ((f y).1.norm_coe_le_norm z |>.trans (hMy y hy))
                (pow_nonneg hρnn n)
          _ < N ^ n := hpow
    obtain ⟨y0, hy0E, hy0⟩ := exists_norm_eq_on_boundary hE0 hE0ne g
    have hy0lt : ∀ y ∈ t, ‖(f y).1 y0‖ < 1 := by
      intro y hy
      have hnorm : ‖(g ^ n * f y).1‖ < N ^ n := by
        have hs := sSup_norm_image_lt hE.1.isCompact (pow_pos hNpos n)
          (hpt y hy)
        rw [← hE.2 (g ^ n * f y)] at hs
        exact hs
      have hval : N ^ n * ‖(f y).1 y0‖ < N ^ n := by
        calc
          N ^ n * ‖(f y).1 y0‖ = ‖((g ^ n * f y).1 y0)‖ := by
            rw [norm_pow_mul_apply, hy0]
          _ ≤ ‖(g ^ n * f y).1‖ := (g ^ n * f y).1.norm_coe_le_norm y0
          _ < N ^ n := hnorm
      exact (mul_lt_iff_lt_one_left (pow_pos hNpos n)).mp (by
        rw [mul_comm]
        exact hval)
    have hy0U : y0 ∈ U := by
      rw [Set.mem_iInter₂]
      intro y hy
      exact Set.mem_ofPred.mpr (hy0lt y hy)
    have hy0cap : y0 ∈ E0 ∩ U := ⟨hy0E, hy0U⟩
    rw [hcap] at hy0cap
    exact Set.notMem_empty y0 hy0cap
  exact le_antisymm hNle hρle

/-- **20.23**: a uniformly closed point-separating algebra has a smallest closed norming boundary.
The restriction isometry is expressed by the exact boundary-norm identity in the predicate. -/
theorem exists_shilov_boundary {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (A : Subalgebra ℂ C(K, ℂ)) (hA : IsClosed (A : Set C(K, ℂ)))
    (hsep : ∀ x y : K, x ≠ y → ∃ f : A, f.1 x ≠ f.1 y) :
    ∃ F : Set K, IsUniformAlgebraBoundary A F ∧
      ∀ G : Set K, IsUniformAlgebraBoundary A G → F ⊆ G := by
  have _hA := hA
  let boundaries : Set (Set K) := {F | IsUniformAlgebraBoundary A F}
  let S : Set K := ⋂₀ boundaries
  have hSclosed : IsClosed S := isClosed_sInter fun _ hB => hB.1
  have hleast : ∀ G, IsUniformAlgebraBoundary A G → S ⊆ G :=
    fun _ hG => Set.sInter_subset_of_mem hG
  refine ⟨S, ⟨hSclosed, ?_⟩, hleast⟩
  intro f
  have hle : sSup ((fun x => ‖f.1 x‖) '' S) ≤ ‖f.1‖ := sSup_norm_image_le f S
  by_cases hf0 : ‖f.1‖ = 0
  · have hnn := sSup_norm_image_nonneg f S
    have hle0 : sSup ((fun x => ‖f.1 x‖) '' S) ≤ 0 := by simpa [hf0] using hle
    rw [hf0, le_antisymm hle0 hnn]
  · have hfpos : 0 < ‖f.1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hf0)
    let Mset : Set K := {x | ‖f.1 x‖ = ‖f.1‖}
    have hMclosed : IsClosed Mset := by
      have hcont : Continuous fun x => ‖f.1 x‖ := continuous_norm.comp f.1.continuous
      have hset : Mset = (fun x => ‖f.1 x‖) ⁻¹' {‖f.1‖} := by
        ext x
        simp [Mset]
      rw [hset]
      exact isClosed_singleton.preimage hcont
    by_cases hinter : (S ∩ Mset).Nonempty
    · obtain ⟨x, hx⟩ := hinter
      have hbdd : BddAbove ((fun z => ‖f.1 z‖) '' S) :=
        ⟨‖f.1‖, fun r hr => by
          obtain ⟨z, -, rfl⟩ := hr
          exact f.1.norm_coe_le_norm z⟩
      exact le_antisymm (le_csSup hbdd ⟨x, hx.1, hx.2⟩) hle
    · rw [Set.not_nonempty_iff_eq_empty] at hinter
      exfalso
      have hex (x : Mset) :
          ∃ E, IsUniformAlgebraBoundary A E ∧ (x : K) ∉ E := by
        have hxS : (x : K) ∉ S := by
          intro hx
          have : (x : K) ∈ S ∩ Mset := ⟨hx, x.property⟩
          rw [hinter] at this
          exact Set.notMem_empty _ this
        have hnot : ¬ ∀ E : boundaries, (x : K) ∈ (E : Set K) := by
          intro hall
          apply hxS
          dsimp only [S]
          rw [Set.sInter_eq_iInter]
          exact Set.mem_iInter.mpr fun E => hall E
        obtain ⟨E, hE⟩ := not_forall.mp hnot
        exact ⟨E.1, E.2, hE⟩
      choose E hEb hxE using hex
      have hU (x : Mset) := exists_open_boundary_sdiff A hsep (hEb x) (hxE x)
      choose U hUopen hxU hUbd using hU
      have hcover : Mset ⊆ ⋃ x : Mset, U x := fun z hz =>
        Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hxU ⟨z, hz⟩⟩
      obtain ⟨t, ht⟩ := hMclosed.isCompact.elim_finite_subcover U
        (fun x => hUopen x) hcover
      have hfold := boundary_foldl_sdiff A t.toList U
        (fun V _ F hF => hUbd V F hF) (isUniformAlgebraBoundary_univ A)
      have hmiss : ∀ z ∈ Mset, z ∉ t.toList.foldl (fun G i => G \ U i) Set.univ := by
        intro z hz
        obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (ht hz)
        exact not_mem_foldl_sdiff t.toList U Set.univ
          (Or.inr ⟨i, Finset.mem_toList.mpr hi, hzi⟩)
      have hpt : ∀ z ∈ t.toList.foldl (fun G i => G \ U i) Set.univ,
          ‖f.1 z‖ < ‖f.1‖ := by
        intro z hz
        exact lt_of_le_of_ne (f.1.norm_coe_le_norm z) fun heq => hmiss z heq hz
      have hstrict := sSup_norm_image_lt hfold.1.isCompact hfpos hpt
      exact hstrict.ne (hfold.2 f).symm

/-- Translation of an L1 equivalence class on the real line, constructed by the actual
measure-preserving composition map. -/
def lpTranslate (f : Lp ℂ 1 (volume : Measure ℝ)) (t : ℝ) : Lp ℂ 1 (volume : Measure ℝ) :=
  Lp.compMeasurePreserving (E := ℂ) (p := 1) (fun x : ℝ ↦ x + t)
    (measurePreserving_add_right (volume : Measure ℝ) t) f

/-- **20.41**, Wiener Tauberian density on the real line. The Fourier transform is the L1
integral of an a.e. representative; the translation span is a closed submodule of L1. -/
theorem wiener_tauberian_real (f : Lp ℂ 1 (volume : Measure ℝ)) :
    (∀ ξ : ℝ, 𝓕 (fun x : ℝ ↦ f x) ξ ≠ 0) ↔
      (Submodule.span ℂ (Set.range (lpTranslate f))).topologicalClosure = ⊤ := by
  sorry

/-- A bounded left approximate identity along `atTop` on a preorder. -/
def IsBoundedLeftApproximateIdentity {ι A : Type*} [Preorder ι] [NonUnitalNormedRing A]
    (e : ι → A) : Prop :=
  (∃ M : ℝ, ∀ i, ‖e i‖ ≤ M) ∧ ∀ a : A, Tendsto (fun i ↦ e i * a) atTop (𝓝 a)

/-- **20.47**, Cohen–Hewitt factorization for a bounded directed approximate identity
acting strongly as the identity on a real or complex Banach module. The action is a continuous
bilinear map, which supports genuinely nonunital algebras without requiring a unital Module
instance. -/
theorem cohen_hewitt_factorization {𝕜 ι A X : Type*} [RCLike 𝕜] [Preorder ι]
    [IsDirected ι (· ≤ ·)] [NonUnitalNormedRing A]
    [NormedSpace 𝕜 A] [CompleteSpace A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    (act : A →L[𝕜] X →L[𝕜] X)
    (hassoc : ∀ a b x, act (a * b) x = act a (act b x))
    (e : ι → A) (he : IsBoundedLeftApproximateIdentity e)
    (hstrong : ∀ x, Tendsto (fun i ↦ act (e i) x) atTop (𝓝 x)) :
    ∀ x : X, ∃ a : A, ∃ y : X, x = act a y := by
  sorry

end CKMA
