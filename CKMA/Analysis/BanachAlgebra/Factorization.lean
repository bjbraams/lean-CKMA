/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.UnitizationL1
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Characters, norming boundaries, Tauberian density, and factorization

The character theorem concerns normalized linear functionals on complex Banach algebras;
continuity and commutativity are not assumed. Closed norming boundaries are subsets of a
compact Hausdorff carrier, including the empty carrier. The Tauberian statement uses actual
L1 equivalence classes and measure-preserving translations on the real line.

Cohen–Hewitt factorization is formulated for a continuous bilinear action of a nonunital
real or complex Banach algebra. Its bounded approximate identity is indexed by a directed set.
The proof uses Mathlib's sum-norm unitization `WithLp 1 (Unitization 𝕜 A)`, the Neumann
series `Units.oneSub` and `tsum_geometric_le_of_norm_lt_one`, and
`cauchySeq_of_le_geometric`; it does not require a regular norm. The Gleason–Kahane–Żelazko
argument follows Kaniuth’s comparison of polynomial coefficients. The Shilov boundary is the
intersection of maximizing sets, as in Bonsall–Duncan.
Sources: GAPS 20.19, 20.23, 20.41, and 20.47.

## Main definitions

* `CKMA.IsUniformAlgebraBoundary`: closed norming boundary for a subalgebra of `C(K, ℂ)`.
* `CKMA.lpTranslate`: translation of an `L¹(ℝ)` equivalence class.
* `CKMA.IsBoundedLeftApproximateIdentity`: bounded left approximate identity along `atTop`.

## Main results

* `eq_zero_of_norm_le_div_nat`: a vector bounded in norm by `C / n` for all `n ≥ 2` is zero.
* `CKMA.gleason_kahane_zelazko`: Gleason–Kahane–Żelazko theorem.
* `CKMA.exists_shilov_boundary`: existence of the Shilov boundary.
* `CKMA.wiener_tauberian_real`: Wiener's Tauberian theorem on `L¹(ℝ)`.
* `CKMA.cohen_hewitt_factorization`: Cohen–Hewitt factorization theorem.
-/

public section

noncomputable section

namespace CKMA

open Filter Topology MeasureTheory FourierTransform Polynomial
open scoped FourierTransform

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
  exact eq_comm.mp (sub_eq_zero.mp (eq_zero_of_norm_le_div_nat hδ))

/-- **20.19**, Gleason–Kahane–Żelazko: a normalized complex linear functional nonzero on
units is multiplicative. Continuity and commutativity are not assumed. -/
theorem gleason_kahane_zelazko {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (F : A →ₗ[ℂ] ℂ) (hF : F 1 = 1)
    (hu : ∀ a : A, IsUnit a → F a ≠ 0) : ∀ a b : A, F (a * b) = F a * F b :=
  fun a b => linearMap_mul_of_sq F hF (fun x => gkz_preserves_sq F hF hu x) a b

/-- A closed boundary for a uniform algebra, using the supremum convention that also
allows the zero algebra on the empty compact space. -/
@[expose]
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

/-- On a nonempty carrier every closed boundary is nonempty, since it norms the unit. -/
private theorem IsUniformAlgebraBoundary.nonempty {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [Nonempty K] {A : Subalgebra ℂ C(K, ℂ)} {E : Set K}
    (hE : IsUniformAlgebraBoundary A E) : E.Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hsup := hE.2 (1 : A)
  rw [hempty, Set.image_empty, Real.sSup_empty, Subalgebra.coe_one] at hsup
  have hnorm : ‖(1 : C(K, ℂ))‖ = 1 := by
    rw [ContinuousMap.norm_eq_iSup_norm]
    have hpt : ∀ x : K, ‖(1 : C(K, ℂ)) x‖ = 1 := fun x => by
      rw [ContinuousMap.one_apply, norm_one]
    simp only [hpt]
    exact ciSup_const
  exact one_ne_zero (hnorm.symm.trans hsup)

/-- If `0 ≤ ρ < N` and `0 < M`, then `ρ ^ n * M < N ^ n` for some exponent `n`. -/
private theorem exists_pow_mul_lt_pow {ρ N M : ℝ} (hρ : 0 ≤ ρ) (hρN : ρ < N) (hM : 0 < M) :
    ∃ n : ℕ, ρ ^ n * M < N ^ n := by
  have hNpos : 0 < N := hρ.trans_lt hρN
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (one_div_pos.mpr hM) ((div_lt_one hNpos).mpr hρN)
  have hlt1 : (ρ / N) ^ n * M < 1 := by
    calc
      (ρ / N) ^ n * M < (1 / M) * M := mul_lt_mul_of_pos_right hn hM
      _ = 1 := by rw [one_div, inv_mul_cancel₀ hM.ne']
  refine ⟨n, ?_⟩
  have hrewrite : ρ ^ n * M = (ρ / N) ^ n * M * N ^ n := by
    rw [div_pow, div_mul_eq_mul_div, div_mul_cancel₀ _ (pow_ne_zero n hNpos.ne')]
  rw [hrewrite]
  calc
    (ρ / N) ^ n * M * N ^ n < 1 * N ^ n := mul_lt_mul_of_pos_right hlt1 (pow_pos hNpos n)
    _ = N ^ n := one_mul _

/-- Deleting an open set `U` from a boundary `E` keeps the norm of `g`, provided that `U` misses
a nonempty boundary `E0` and is the common sublevel set `{‖f y‖ < 1}` of finitely many algebra
elements `f y` of norm at most `M`. Otherwise `g ^ n * f y` would have norm below `‖g‖ ^ n`
on `E` for large `n`, forcing the point of `E0` where `g` peaks into `U`. -/
private theorem norm_le_sSup_norm_image_sdiff {K ι : Type*} [TopologicalSpace K]
    [CompactSpace K] {A : Subalgebra ℂ C(K, ℂ)} {E0 E U : Set K}
    (hE0 : IsUniformAlgebraBoundary A E0) (hE0ne : E0.Nonempty)
    (hE : IsUniformAlgebraBoundary A E) (hcap : E0 ∩ U = ∅) {t : Finset ι} (f : ι → A) {M : ℝ}
    (hM : 0 < M) (hMy : ∀ y ∈ t, ‖(f y).1‖ ≤ M)
    (hU : ∀ z, z ∈ U ↔ ∀ y ∈ t, ‖(f y).1 z‖ < 1) (g : A) :
    ‖g.1‖ ≤ sSup ((fun x => ‖g.1 x‖) '' (E \ U)) := by
  set N : ℝ := ‖g.1‖
  set ρ : ℝ := sSup ((fun x => ‖g.1 x‖) '' (E \ U))
  have hρnn : 0 ≤ ρ := sSup_norm_image_nonneg g (E \ U)
  by_contra hlt
  have hρlt : ρ < N := lt_of_not_ge hlt
  have hNpos : 0 < N := hρnn.trans_lt hρlt
  obtain ⟨n, hpow⟩ := exists_pow_mul_lt_pow hρnn hρlt hM
  have hpt (y : ι) (hy : y ∈ t) (z : K) (hz : z ∈ E) :
      ‖((g ^ n * f y).1 z)‖ < N ^ n := by
    rw [norm_pow_mul_apply]
    by_cases hzu : z ∈ U
    · have hfy : ‖(f y).1 z‖ < 1 := (hU z).1 hzu y hy
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
      have hs := sSup_norm_image_lt hE.1.isCompact (pow_pos hNpos n) (hpt y hy)
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
  have hy0cap : y0 ∈ E0 ∩ U := ⟨hy0E, (hU y0).2 hy0lt⟩
  rw [hcap] at hy0cap
  exact Set.notMem_empty y0 hy0cap

/-- Around a point omitted by one boundary, an open set may be deleted from every boundary. -/
private theorem exists_open_boundary_sdiff {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (A : Subalgebra ℂ C(K, ℂ))
    (hsep : ∀ x y : K, x ≠ y → ∃ f : A, f.1 x ≠ f.1 y)
    {E0 : Set K} (hE0 : IsUniformAlgebraBoundary A E0) {x0 : K} (hx0 : x0 ∉ E0) :
    ∃ U : Set K, IsOpen U ∧ x0 ∈ U ∧ ∀ E : Set K, IsUniformAlgebraBoundary A E →
      IsUniformAlgebraBoundary A (E \ U) := by
  have : Nonempty K := ⟨x0⟩
  have hE0ne : E0.Nonempty := hE0.nonempty
  -- Functions vanishing at `x0` and of modulus `2` at the points of `E0`.
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
  -- Finitely many of the open sets `{1 < ‖f y‖}` cover the compact boundary `E0`.
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
  -- The open set `U` where all of these functions are small contains `x0` and misses `E0`.
  let U : Set K := ⋂ y ∈ t, {z | ‖(f y).1 z‖ < 1}
  have hU : ∀ z, z ∈ U ↔ ∀ y ∈ t, ‖(f y).1 z‖ < 1 := fun z => Set.mem_iInter₂
  have hUopen : IsOpen U := isOpen_biInter_finset fun y _ =>
    isOpen_lt (continuous_norm.comp (f y).1.continuous) continuous_const
  have hx0U : x0 ∈ U := (hU x0).2 fun y _ => by
    rw [hf0 y, norm_zero]
    exact one_pos
  have hcap : E0 ∩ U = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hzE hzU
    obtain ⟨y, hy, hyz⟩ := Set.mem_iUnion₂.mp (ht hzE)
    exact lt_asymm hyz.out ((hU z).1 hzU y hy)
  have hMbd : BddAbove ((fun y : E0 => ‖(f y).1‖) '' (t : Set E0)) :=
    ((Finset.finite_toSet t).image (fun y => ‖(f y).1‖)).bddAbove
  set M : ℝ := sSup ((fun y : E0 => ‖(f y).1‖) '' (t : Set E0))
  have hMy (y : E0) (hy : y ∈ t) : ‖(f y).1‖ ≤ M :=
    le_csSup hMbd (Set.mem_image_of_mem _ hy)
  have hMpos : 0 < M := by
    obtain ⟨y, hy⟩ := htne
    calc
      (0 : ℝ) < 2 := two_pos
      _ = ‖(f y).1 (y : K)‖ := by rw [hf2 y, Complex.norm_two]
      _ ≤ ‖(f y).1‖ := (f y).1.norm_coe_le_norm _
      _ ≤ M := hMy y hy
  refine ⟨U, hUopen, hx0U, fun E hE => ⟨hE.1.sdiff hUopen, fun g => ?_⟩⟩
  exact le_antisymm
    (norm_le_sSup_norm_image_sdiff hE0 hE0ne hE hcap f hMpos hMy hU g)
    (sSup_norm_image_le g (E \ U))

/-- **20.23**: a point-separating algebra has a smallest closed norming boundary.
The restriction isometry is expressed by the exact boundary-norm identity in the predicate. -/
theorem exists_shilov_boundary {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (A : Subalgebra ℂ C(K, ℂ))
    (hsep : ∀ x y : K, x ≠ y → ∃ f : A, f.1 x ≠ f.1 y) :
    ∃ F : Set K, IsUniformAlgebraBoundary A F ∧
      ∀ G : Set K, IsUniformAlgebraBoundary A G → F ⊆ G := by
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
@[expose]
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
@[expose]
def IsBoundedLeftApproximateIdentity {ι A : Type*} [Preorder ι] [NonUnitalNormedRing A]
    (e : ι → A) : Prop :=
  (∃ M : ℝ, ∀ i, ‖e i‖ ≤ M) ∧ ∀ a : A, Tendsto (fun i ↦ e i * a) atTop (𝓝 a)

private abbrev U (R B : Type*) := WithLp 1 (Unitization R B)

section CohenHewitt

open Unitization WithLp

variable {𝕜 A X : Type*} [RCLike 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
    [CompleteSpace A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (act : A →L[𝕜] X →L[𝕜] X)

private def incl (a : A) : U 𝕜 A := toLp 1 (a : Unitization 𝕜 A)

private def ofS (r : 𝕜) : U 𝕜 A := algebraMap 𝕜 (U 𝕜 A) r

private lemma norm_incl (a : A) : ‖(incl a : U 𝕜 A)‖ = ‖a‖ := by
  simpa [incl] using unitization_norm_inr (𝕜 := 𝕜) (A := A) a

private lemma norm_ofS (r : 𝕜) : ‖(ofS r : U 𝕜 A)‖ = ‖r‖ := by
  rw [show (ofS r : U 𝕜 A) = algebraMap 𝕜 (U 𝕜 A) r by rfl, unitization_norm_def,
    unitization_algebraMap, algebraMap_eq_inl, fst_inl, snd_inl, norm_zero, add_zero]

private lemma ofS_one : ofS (1 : 𝕜) = (1 : U 𝕜 A) := by simp [ofS]

private lemma ofS_zero : ofS (0 : 𝕜) = (0 : U 𝕜 A) := by simp [ofS]

private lemma incl_zero : incl (0 : A) = (0 : U 𝕜 A) := by simp [incl]

private lemma ofS_mul (r s : 𝕜) : (ofS r * ofS s : U 𝕜 A) = ofS (r * s) := by
  simp [ofS, map_mul]

private lemma incl_smul (r : 𝕜) (a : A) : incl (r • a) = (r • incl a : U 𝕜 A) := by
  simp [incl, inr_smul]

private lemma ofS_mul_incl (r : 𝕜) (a : A) : ofS r * incl a = incl (r • a) := by
  apply ofLp_injective
  simp [ofS, incl, unitization_mul, unitization_algebraMap, ofLp_toLp, algebraMap_eq_inl,
    inl_mul_inr]

private lemma incl_mul_incl (a b : A) : (incl a * incl b : U 𝕜 A) = incl (a * b) := by
  apply ofLp_injective
  simp [incl, unitization_mul, ofLp_toLp, inr_mul]

private def actU (u : U 𝕜 A) (x : X) : X :=
  (ofLp u).fst • x + act (ofLp u).snd x

private lemma actU_incl (a : A) (x : X) : actU act (incl a) x = act a x := by
  simp [actU, incl, ofLp_toLp, fst_inr, snd_inr, zero_smul]

private lemma actU_ofS (r : 𝕜) (x : X) : actU act (ofS r) x = r • x := by
  rw [actU, ofS, unitization_algebraMap, algebraMap_eq_inl, fst_inl, snd_inl]
  simp

private lemma actU_one (x : X) : actU act 1 x = x := by
  rw [← ofS_one, actU_ofS, one_smul]

private lemma actU_add (u v : U 𝕜 A) (x : X) :
    actU act (u + v) x = actU act u x + actU act v x := by
  simp only [actU, ofLp_add, fst_add, snd_add, add_smul, map_add, add_apply]
  abel

private lemma actU_smul (r : 𝕜) (u : U 𝕜 A) (x : X) :
    actU act (r • u) x = r • actU act u x := by
  simp only [actU, ofLp_smul, fst_smul, snd_smul, map_smul, smul_apply, smul_add, smul_assoc]

private lemma actU_zero_right (u : U 𝕜 A) : actU act u 0 = 0 := by simp [actU]

private lemma actU_add_right (u : U 𝕜 A) (x y : X) :
    actU act u (x + y) = actU act u x + actU act u y := by
  simp only [actU, smul_add, map_add, add_apply]
  abel

private lemma actU_sub_right (u : U 𝕜 A) (x y : X) :
    actU act u (x - y) = actU act u x - actU act u y := by
  simp only [actU, smul_sub, map_sub, sub_apply]
  abel

private lemma actU_sub (u v : U 𝕜 A) (x : X) :
    actU act (u - v) x = actU act u x - actU act v x := by
  have h := actU_add act v (u - v) x
  rw [add_sub_cancel] at h
  rw [eq_sub_iff_add_eq, add_comm]
  exact h.symm

private lemma norm_actU_le (u : U 𝕜 A) (x : X) :
    ‖actU act u x‖ ≤ max ‖act‖ 1 * ‖u‖ * ‖x‖ := by
  set p := ofLp u
  have hsnd : ‖act p.snd x‖ ≤ ‖act‖ * ‖p.snd‖ * ‖x‖ := by
    calc
      ‖act p.snd x‖ ≤ ‖act p.snd‖ * ‖x‖ := (act p.snd).le_opNorm x
      _ ≤ (‖act‖ * ‖p.snd‖) * ‖x‖ := by gcongr; exact act.le_opNorm p.snd
      _ = ‖act‖ * ‖p.snd‖ * ‖x‖ := by ring
  have hfst : ‖p.fst‖ * ‖x‖ ≤ max ‖act‖ 1 * ‖p.fst‖ * ‖x‖ := by
    have hm : (1 : ℝ) ≤ max ‖act‖ 1 := le_max_right _ _
    calc
      ‖p.fst‖ * ‖x‖ = 1 * (‖p.fst‖ * ‖x‖) := by ring
      _ ≤ max ‖act‖ 1 * (‖p.fst‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_right hm (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = max ‖act‖ 1 * ‖p.fst‖ * ‖x‖ := by ring
  have hsnd' : ‖act‖ * ‖p.snd‖ * ‖x‖ ≤ max ‖act‖ 1 * ‖p.snd‖ * ‖x‖ := by
    have hm : ‖act‖ ≤ max ‖act‖ 1 := le_max_left _ _
    calc
      ‖act‖ * ‖p.snd‖ * ‖x‖ = ‖act‖ * (‖p.snd‖ * ‖x‖) := by ring
      _ ≤ max ‖act‖ 1 * (‖p.snd‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_right hm (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = max ‖act‖ 1 * ‖p.snd‖ * ‖x‖ := by ring
  calc
    ‖actU act u x‖ ≤ ‖p.fst • x‖ + ‖act p.snd x‖ := by simpa [actU, p] using norm_add_le _ _
    _ ≤ ‖p.fst‖ * ‖x‖ + ‖act‖ * ‖p.snd‖ * ‖x‖ := by gcongr; exact norm_smul_le _ _
    _ ≤ max ‖act‖ 1 * ‖p.fst‖ * ‖x‖ + max ‖act‖ 1 * ‖p.snd‖ * ‖x‖ := by gcongr
    _ = max ‖act‖ 1 * (‖p.fst‖ + ‖p.snd‖) * ‖x‖ := by ring
    _ = max ‖act‖ 1 * ‖u‖ * ‖x‖ := by
      have hnorm : ‖p.fst‖ + ‖p.snd‖ = ‖u‖ := by
        simpa [p] using (unitization_norm_def u).symm
      rw [hnorm]

private lemma actU_mul (hassoc : ∀ a b (x : X), act (a * b) x = act a (act b x))
    (u v : U 𝕜 A) (x : X) : actU act (u * v) x = actU act u (actU act v x) := by
  simp only [actU, unitization_mul, fst_mul, snd_mul, map_add, map_smul, mul_smul, smul_add,
    add_apply, smul_apply]
  simp only [smul_mul_assoc, hassoc, (act _).map_smul]
  abel_nf

/-- Sum-norm element `(1 - C) + C • a`. -/
private def uOf (C : ℝ) (a : A) : U 𝕜 A := ofS (1 - (C : 𝕜)) + (C : 𝕜) • incl a

private lemma ofS_mul_smul_incl (r s : 𝕜) (a : A) :
    ofS r * (s • incl a) = incl ((r * s) • a) := by
  rw [← incl_smul, ofS_mul_incl, smul_smul]

private lemma uOf_factor (C : ℝ) (a : A) (hC : 0 < C) (hC1 : C < 1) :
    uOf C a = ofS (1 - (C : 𝕜)) * (1 + ((C : 𝕜) / (1 - (C : 𝕜))) • incl a) := by
  have hne : (1 - (C : 𝕜)) ≠ 0 := by
    rw [sub_ne_zero, ne_comm]
    exact_mod_cast hC1.ne
  rw [uOf, mul_add, mul_one, ofS_mul_smul_incl, incl_smul]
  refine congrArg (fun t : U 𝕜 A => ofS (1 - (C : 𝕜)) + t) ?_
  refine congrArg (fun s : 𝕜 => s • incl a) ?_
  exact (mul_div_cancel₀ (C : 𝕜) hne).symm

private lemma incl_add (a b : A) : incl (a + b) = (incl a + incl b : U 𝕜 A) := by
  apply ofLp_injective
  simp [incl, ofLp_add, inr_add]

private lemma incl_mul_ofS (a : A) (r : 𝕜) : (incl a * ofS r : U 𝕜 A) = incl (r • a) := by
  apply ofLp_injective
  simp [incl, ofS, unitization_mul, unitization_algebraMap, ofLp_toLp, algebraMap_eq_inl,
    inr_mul_inl]

private lemma smul_incl_mul_ofS (c r : 𝕜) (a : A) :
    ((c • incl a : U 𝕜 A) * ofS r) = incl ((r * c) • a) := by
  rw [smul_mul_assoc, incl_mul_ofS, ← incl_smul, smul_smul, mul_comm]

private lemma smul_incl_mul_incl (c : 𝕜) (a b : A) :
    ((c • incl a : U 𝕜 A) * incl b) = incl (c • (a * b)) := by
  rw [smul_mul_assoc, incl_mul_incl, incl_smul]

private lemma uOf_mul_shift (C : ℝ) (b s : A) (r : 𝕜) :
    uOf C b * (ofS r + incl s) =
      ofS ((1 - (C : 𝕜)) * r) +
        incl ((1 - (C : 𝕜)) • s + (r * (C : 𝕜)) • b + (C : 𝕜) • (b * s)) := by
  rw [uOf, add_mul, mul_add, mul_add, ofS_mul, ofS_mul_incl, smul_incl_mul_ofS,
    smul_incl_mul_incl, add_assoc]
  congr 1
  rw [← add_assoc, ← incl_add, ← incl_add]

/-- Neumann inverse of `(1 - C) + C • b` when `‖b‖ ≤ K` and `C = 1 / (K + 2)`. -/
private lemma uOf_isUnit {K C : ℝ} (hK : 1 ≤ K) (hC : C = 1 / (K + 2)) (b : A)
    (hb : ‖b‖ ≤ K) : ∃ φ : U 𝕜 A, uOf C b * φ = 1 ∧ φ * uOf C b = 1 ∧ ‖φ‖ ≤ K + 2 := by
  have h2 : 0 < K + 2 := by linarith
  have h1 : 0 < K + 1 := by linarith
  have hCpos : 0 < C := by rw [hC]; exact div_pos one_pos h2
  have hClt : C < 1 := by rw [hC, div_lt_one h2]; linarith
  have hσpos : 0 < 1 - C := by rwa [sub_pos]
  have h1C : 1 - C = (K + 1) / (K + 2) := by
    rw [hC]
    calc
      (1 : ℝ) - 1 / (K + 2) = (K + 2) / (K + 2) - 1 / (K + 2) := by rw [div_self h2.ne']
      _ = (K + 2 - 1) / (K + 2) := (sub_div _ _ _).symm
      _ = (K + 1) / (K + 2) := by congr 1; ring
  have hγ : C / (1 - C) = 1 / (K + 1) := by
    rw [h1C, hC, div_div_div_cancel_right₀ h2.ne']
  have hγK : C / (1 - C) * K < 1 := by
    rw [hγ, div_mul_eq_mul_div, one_mul, div_lt_one h1]; linarith
  have hinv : (1 - C)⁻¹ = (K + 2) / (K + 1) := by rw [h1C, inv_div]
  let γ : ℝ := C / (1 - C)
  have hγ0 : 0 ≤ γ := div_nonneg hCpos.le hσpos.le
  let t : U 𝕜 A := (γ : 𝕜) • incl b
  have ht_le : ‖t‖ ≤ γ * K := by
    calc
      ‖t‖ = ‖(γ : 𝕜)‖ * ‖b‖ := by rw [norm_smul, norm_incl]
      _ = |γ| * ‖b‖ := by rw [RCLike.norm_ofReal]
      _ = γ * ‖b‖ := by rw [abs_of_nonneg hγ0]
      _ ≤ γ * K := by gcongr
  have ht : ‖t‖ < 1 := lt_of_le_of_lt ht_le hγK
  let qU : (U 𝕜 A)ˣ := Units.oneSub (-t) (by simpa [norm_neg] using ht)
  let pk : 𝕜 := 1 - (C : 𝕜)
  have hpk : pk ≠ 0 := by
    rw [sub_ne_zero, ne_comm]
    exact_mod_cast hClt.ne
  let pU : (U 𝕜 A)ˣ := {
    val := ofS pk
    inv := ofS pk⁻¹
    val_inv := by rw [ofS_mul, mul_inv_cancel₀ hpk, ofS_one]
    inv_val := by rw [ofS_mul, inv_mul_cancel₀ hpk, ofS_one] }
  have hpkcoe : pk = (1 - C : 𝕜) := rfl
  have hpnorm : ‖(↑(pU⁻¹) : U 𝕜 A)‖ = (1 - C)⁻¹ := by
    calc
      ‖(↑(pU⁻¹) : U 𝕜 A)‖ = ‖(ofS (pk⁻¹) : U 𝕜 A)‖ := rfl
      _ = ‖pk⁻¹‖ := norm_ofS _
      _ = ‖pk‖⁻¹ := norm_inv _
      _ = ‖(1 - C : 𝕜)‖⁻¹ := by rw [hpkcoe]
      _ = |1 - C|⁻¹ := by
          rw [← RCLike.ofReal_one, ← RCLike.ofReal_sub, RCLike.norm_ofReal]
      _ = (1 - C)⁻¹ := by rw [abs_of_pos hσpos]
  have hqnorm : ‖(↑(qU⁻¹) : U 𝕜 A)‖ ≤ (1 - ‖t‖)⁻¹ := by
    have hsum := tsum_geometric_le_of_norm_lt_one (-t) (by simpa [norm_neg] using ht)
    have hq : (↑(qU⁻¹) : U 𝕜 A) = ∑' n : ℕ, (-t) ^ n := rfl
    rw [hq]
    simpa [norm_one, sub_self, zero_add, norm_neg] using hsum
  have hbase : 1 - γ * K = 1 / (K + 1) := by
    have hγdef : γ = C / (1 - C) := rfl
    rw [hγdef, hγ]
    calc
      1 - 1 / (K + 1) * K = 1 - K / (K + 1) := by ring
      _ = (K + 1) / (K + 1) - K / (K + 1) := by rw [div_self h1.ne']
      _ = (K + 1 - K) / (K + 1) := (sub_div _ _ _).symm
      _ = 1 / (K + 1) := by congr 1; ring
  have hanti : (1 - ‖t‖)⁻¹ ≤ K + 1 := by
    have hpos : 0 < 1 - γ * K := by linarith [hγK]
    have hineq : 1 - γ * K ≤ 1 - ‖t‖ := by linarith [ht_le]
    have := inv_anti₀ hpos hineq
    rw [hbase, inv_div, div_one] at this
    exact this
  have hγcoe : (γ : 𝕜) = (C : 𝕜) / (1 - (C : 𝕜)) := by
    have hγdef : γ = C / (1 - C) := rfl
    rw [hγdef, RCLike.ofReal_div, RCLike.ofReal_sub, RCLike.ofReal_one]
  have hu : uOf C b = (pU : U 𝕜 A) * (qU : U 𝕜 A) := by
    rw [uOf_factor C b hCpos hClt]
    have hq : (qU : U 𝕜 A) = 1 + t := sub_neg_eq_add _ _
    have hp : (pU : U 𝕜 A) = ofS (1 - (C : 𝕜)) := rfl
    have ht' : t = ((C : 𝕜) / (1 - (C : 𝕜))) • incl b := by
      unfold t
      rw [hγcoe]
    rw [hq, hp, ht']
  let φ : U 𝕜 A := ↑(qU⁻¹ * pU⁻¹)
  refine ⟨φ, ?_, ?_, ?_⟩
  · rw [hu]
    calc
      (pU : U 𝕜 A) * (qU : U 𝕜 A) * φ = ↑pU * ↑qU * (↑(qU⁻¹) * ↑(pU⁻¹)) := by
        simp [φ, Units.val_mul]
      _ = ↑pU * (↑qU * ↑(qU⁻¹)) * ↑(pU⁻¹) := by simp [mul_assoc]
      _ = 1 := by rw [Units.mul_inv, mul_one, Units.mul_inv]
  · rw [hu]
    calc
      φ * ((pU : U 𝕜 A) * (qU : U 𝕜 A)) = ↑(qU⁻¹) * ↑(pU⁻¹) * (↑pU * ↑qU) := by
        simp [φ, Units.val_mul]
      _ = ↑(qU⁻¹) * (↑(pU⁻¹) * ↑pU) * ↑qU := by simp [mul_assoc]
      _ = 1 := by rw [Units.inv_mul, mul_one, Units.inv_mul]
  · calc
      ‖φ‖ ≤ ‖(↑(qU⁻¹) : U 𝕜 A)‖ * ‖(↑(pU⁻¹) : U 𝕜 A)‖ := by
        simpa [φ, Units.val_mul] using norm_mul_le (↑(qU⁻¹) : U 𝕜 A) ↑(pU⁻¹)
      _ ≤ (K + 1) * (1 - C)⁻¹ :=
        mul_le_mul (hqnorm.trans hanti) (le_of_eq hpnorm) (norm_nonneg _) (by linarith)
      _ = K + 2 := by rw [hinv, mul_div_cancel₀ _ h1.ne']

private lemma uOf_mul_pow {C σ : ℝ} (hσ : σ = 1 - C) (b s : A) (n : ℕ) :
    uOf C b * (ofS ((σ : 𝕜) ^ n) + incl s) =
      ofS ((σ : 𝕜) ^ (n + 1)) +
        incl ((σ : 𝕜) • s + ((C * σ ^ n : ℝ) : 𝕜) • b + (C : 𝕜) • (b * s)) := by
  rw [uOf_mul_shift]
  have hcoe : (1 - (C : 𝕜)) = (σ : 𝕜) := by rw [hσ, RCLike.ofReal_sub, RCLike.ofReal_one]
  have hpow : (1 - (C : 𝕜)) * (σ : 𝕜) ^ n = (σ : 𝕜) ^ (n + 1) := by
    rw [hcoe, mul_comm, pow_succ]
  have hsmul : (1 - (C : 𝕜)) • s = (σ : 𝕜) • s := by rw [hcoe]
  have hcoeff : (σ : 𝕜) ^ n * (C : 𝕜) = ((C * σ ^ n : ℝ) : 𝕜) := by
    rw [mul_comm, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul]
  rw [hpow, hsmul, hcoeff]

private lemma actU_uOf (C : ℝ) (b : A) (x : X) :
    actU act (uOf C b) x = (1 - (C : 𝕜)) • x + (C : 𝕜) • act b x := by
  rw [uOf, actU_add, actU_ofS, actU_smul, actU_incl]

private lemma actU_smul_right (r : 𝕜) (u : U 𝕜 A) (x : X) :
    actU act u (r • x) = r • actU act u x := by
  simp only [actU, map_smul, smul_apply, smul_add]
  rw [← smul_comm r (ofLp u).fst x]

private lemma actU_inv_sub {C : ℝ} {b : A} {φ : U 𝕜 A} {x : X}
    (hassoc : ∀ a b (x : X), act (a * b) x = act a (act b x)) (hφ : φ * uOf C b = 1) :
    actU act φ x - x = (C : 𝕜) • actU act φ (x - act b x) := by
  have hx : x = actU act φ (actU act (uOf C b) x) := by
    rw [← actU_mul act hassoc, hφ, actU_one]
  nth_rw 2 [hx]
  rw [← actU_sub_right]
  have hdiff : x - actU act (uOf C b) x = (C : 𝕜) • (x - act b x) := by
    rw [actU_uOf, sub_add_eq_sub_sub]
    nth_rw 1 [← one_smul 𝕜 x]
    rw [← sub_smul]
    have hsc : (1 : 𝕜) - (1 - (C : 𝕜)) = C := by ring
    rw [hsc, smul_sub]
  rw [hdiff, actU_smul_right]

private lemma norm_step_s {K C σ : ℝ} (hK : 1 ≤ K) (hC : C = 1 / (K + 2))
    (hσ : σ = 1 - C) (hσ0 : 0 ≤ σ) (n : ℕ) {b s : A} (hb : ‖b‖ ≤ K)
    (hbs : ‖b * s - s‖ ≤ σ ^ n) :
    ‖(σ : 𝕜) • s + ((C * σ ^ n : ℝ) : 𝕜) • b + (C : 𝕜) • (b * s) - s‖ ≤
      σ ^ (n + 1) := by
  have h2 : K + 2 ≠ 0 := by linarith
  have hC0 : 0 ≤ C := by rw [hC]; exact div_nonneg zero_le_one (by linarith)
  have h1C : 1 - C = (K + 1) / (K + 2) := by
    rw [hC]
    calc
      (1 : ℝ) - 1 / (K + 2) = (K + 2) / (K + 2) - 1 / (K + 2) := by rw [div_self h2]
      _ = (K + 2 - 1) / (K + 2) := (sub_div _ _ _).symm
      _ = (K + 1) / (K + 2) := by congr 1; ring
  have hprod : C * (K + 1) = σ := by rw [hσ, h1C, hC, div_mul_eq_mul_div, one_mul]
  have hcoe : (σ : 𝕜) = 1 - (C : 𝕜) := by rw [hσ, RCLike.ofReal_sub, RCLike.ofReal_one]
  set coeff : 𝕜 := ((C * σ ^ n : ℝ) : 𝕜)
  have hEq :
      (σ : 𝕜) • s + coeff • b + (C : 𝕜) • (b * s) - s =
        (C : 𝕜) • (b * s - s) + coeff • b := by
    calc
      (σ : 𝕜) • s + coeff • b + (C : 𝕜) • (b * s) - s
        = (σ : 𝕜) • s + coeff • b + (C : 𝕜) • (b * s) - (1 : 𝕜) • s := by rw [one_smul]
      _ = ((σ : 𝕜) • s - (1 : 𝕜) • s) + coeff • b + (C : 𝕜) • (b * s) := by abel
      _ = ((σ : 𝕜) - 1) • s + coeff • b + (C : 𝕜) • (b * s) := by rw [sub_smul]
      _ = (-(C : 𝕜)) • s + (C : 𝕜) • (b * s) + coeff • b := by
          rw [show (σ : 𝕜) - 1 = -(C : 𝕜) by rw [hcoe]; ring]; abel
      _ = (C : 𝕜) • (b * s) - (C : 𝕜) • s + coeff • b := by rw [neg_smul]; abel
      _ = (C : 𝕜) • (b * s - s) + coeff • b := by rw [smul_sub]
  rw [hEq]
  have h1 : ‖(C : 𝕜) • (b * s - s)‖ ≤ C * σ ^ n := by
    calc
      ‖(C : 𝕜) • (b * s - s)‖ = C * ‖b * s - s‖ := by
        rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg hC0]
      _ ≤ C * σ ^ n := by gcongr
  have hpow : 0 ≤ C * σ ^ n := mul_nonneg hC0 (pow_nonneg hσ0 _)
  have h2n : ‖coeff • b‖ ≤ C * σ ^ n * K := by
    calc
      ‖coeff • b‖ = C * σ ^ n * ‖b‖ := by
        rw [norm_smul, show coeff = ((C * σ ^ n : ℝ) : 𝕜) from rfl, RCLike.norm_ofReal,
          abs_of_nonneg hpow]
      _ ≤ C * σ ^ n * K := by gcongr
  calc
    ‖(C : 𝕜) • (b * s - s) + coeff • b‖ ≤ ‖(C : 𝕜) • (b * s - s)‖ + ‖coeff • b‖ :=
      norm_add_le _ _
    _ ≤ C * σ ^ n + C * σ ^ n * K := by gcongr
    _ = C * (K + 1) * σ ^ n := by ring
    _ = σ * σ ^ n := by rw [hprod]
    _ = σ ^ (n + 1) := by rw [← pow_succ']

private lemma norm_step_y {K C : ℝ} (hK : 1 ≤ K) (hC : C = 1 / (K + 2))
    (hassoc : ∀ a b (x : X), act (a * b) x = act a (act b x)) {b : A} {φ : U 𝕜 A}
    (hφ : φ * uOf C b = 1) (hφn : ‖φ‖ ≤ K + 2) (aInv : U 𝕜 A) (z : X) {eps : ℝ}
    (heps : ‖act b z - z‖ ≤ eps) :
    ‖actU act (aInv * φ) z - actU act aInv z‖ ≤ (max ‖act‖ 1) ^ 2 * ‖aInv‖ * eps := by
  have hpos : 0 < K + 2 := by linarith
  have hCpos : 0 < C := by rw [hC]; exact div_pos one_pos hpos
  have hCK : C * (K + 2) = 1 := by rw [hC, div_mul_cancel₀ 1 hpos.ne']
  set Mm := max ‖act‖ 1
  have hinner : ‖actU act φ (z - act b z)‖ ≤ Mm * (K + 2) * eps := by
    calc
      ‖actU act φ (z - act b z)‖ ≤ Mm * ‖φ‖ * ‖z - act b z‖ := norm_actU_le act φ _
      _ ≤ Mm * (K + 2) * ‖z - act b z‖ := by gcongr
      _ ≤ Mm * (K + 2) * eps := by gcongr; simpa [norm_sub_rev] using heps
  have hmain :
      actU act (aInv * φ) z - actU act aInv z =
        (C : 𝕜) • actU act aInv (actU act φ (z - act b z)) := by
    rw [actU_mul act hassoc, ← actU_sub_right, actU_inv_sub act hassoc hφ, actU_smul_right]
  calc
    ‖actU act (aInv * φ) z - actU act aInv z‖
      = C * ‖actU act aInv (actU act φ (z - act b z))‖ := by
        rw [hmain, norm_smul, RCLike.norm_ofReal, abs_of_pos hCpos]
    _ ≤ C * (Mm * ‖aInv‖ * ‖actU act φ (z - act b z)‖) := by
        gcongr; exact norm_actU_le act aInv _
    _ ≤ C * (Mm * ‖aInv‖ * (Mm * (K + 2) * eps)) := by gcongr
    _ = Mm ^ 2 * ‖aInv‖ * eps := by
        calc
          C * (Mm * ‖aInv‖ * (Mm * (K + 2) * eps))
            = (C * (K + 2)) * Mm ^ 2 * ‖aInv‖ * eps := by ring
          _ = Mm ^ 2 * ‖aInv‖ * eps := by rw [hCK, one_mul]

private def stepEps (Mm na : ℝ) (n : ℕ) : ℝ :=
  (1 / 2) ^ (n + 1) / (Mm ^ 2 * (na + 1))

private lemma stepEps_scaled (Mm na : ℝ) (n : ℕ) (hMm : 1 ≤ Mm) (hna : 0 ≤ na) :
    Mm ^ 2 * na * stepEps Mm na n ≤ ((1 : ℝ) / 2) ^ (n + 1) := by
  have hden : 0 < Mm ^ 2 * (na + 1) :=
    mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one hMm) _) (by linarith)
  rw [stepEps, ← mul_div_assoc, div_le_iff₀ hden]
  have hnum : 0 ≤ ((1 : ℝ) / 2) ^ (n + 1) := pow_nonneg (by norm_num) _
  have hmul : Mm ^ 2 * na ≤ Mm ^ 2 * (na + 1) :=
    mul_le_mul_of_nonneg_left (by linarith : na ≤ na + 1)
      (pow_nonneg (le_trans zero_le_one hMm) _)
  calc
    Mm ^ 2 * na * ((1 : ℝ) / 2) ^ (n + 1)
      = ((1 : ℝ) / 2) ^ (n + 1) * (Mm ^ 2 * na) := by ring
    _ ≤ ((1 : ℝ) / 2) ^ (n + 1) * (Mm ^ 2 * (na + 1)) :=
        mul_le_mul_of_nonneg_left hmul hnum

private lemma exists_factor_index {ι : Type*} [Preorder ι] [Nonempty ι]
    [IsDirected ι (· ≤ ·)] (e : ι → A) (he : IsBoundedLeftApproximateIdentity e)
    (hstrong : ∀ x, Tendsto (fun i ↦ act (e i) x) atTop (𝓝 x)) {K σ : ℝ}
    (hbound : ∀ i, ‖e i‖ ≤ K) (hσpos : 0 < σ) (s : A) (aInv : U 𝕜 A) (n : ℕ)
    (z : X) : ∃ b : A, ‖b‖ ≤ K ∧ ‖b * s - s‖ ≤ σ ^ n ∧
      ‖act b z - z‖ ≤ stepEps (max ‖act‖ 1) ‖aInv‖ n := by
  have _hne : Nonempty ι := inferInstance
  have hs := (Metric.tendsto_nhds.mp (he.2 s)) (σ ^ n) (pow_pos hσpos n)
  have heps : 0 < stepEps (max ‖act‖ 1) ‖aInv‖ n := by
    refine div_pos (pow_pos (by norm_num) _) ?_
    exact mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) _)
      (by linarith [norm_nonneg aInv])
  have hz := (Metric.tendsto_nhds.mp (hstrong z)) _ heps
  rw [Filter.eventually_atTop] at hs hz
  obtain ⟨N1, hN1⟩ := hs
  obtain ⟨N2, hN2⟩ := hz
  obtain ⟨j, hj1, hj2⟩ := IsDirected.directed (r := (· ≤ ·)) N1 N2
  refine ⟨e j, hbound j, ?_, ?_⟩
  · exact (dist_eq_norm (e j * s) s ▸ hN1 j hj1).le
  · exact (dist_eq_norm ((act (e j)) z) z ▸ hN2 j hj2).le

private structure Coh (σ : ℝ) (z : X) where
  n : ℕ
  s : A
  sPrev : A
  a : U 𝕜 A
  aInv : U 𝕜 A
  y : X
  yPrev : X
  ha : a = ofS ((σ : 𝕜) ^ n) + incl s
  hmul : a * aInv = 1
  hinv : aInv * a = 1
  hy : y = actU act aInv z
  hds : ‖s - sPrev‖ ≤ σ ^ n
  hdy : ‖y - yPrev‖ ≤ (1 / 2) ^ n

private def cohZero {σ : ℝ} (z : X) : Coh act σ z where
  n := 0
  s := 0
  sPrev := 0
  a := 1
  aInv := 1
  y := z
  yPrev := z
  ha := by simp [pow_zero, ofS_one, incl_zero, add_zero]
  hmul := one_mul _
  hinv := mul_one _
  hy := (actU_one act z).symm
  hds := by simp [sub_self, norm_zero, pow_zero]
  hdy := by simp [sub_self, norm_zero, pow_zero]

private noncomputable def pickedB {ι : Type*} [Preorder ι] [Nonempty ι]
    [IsDirected ι (· ≤ ·)] (e : ι → A) (he : IsBoundedLeftApproximateIdentity e)
    (hstrong : ∀ x, Tendsto (fun i ↦ act (e i) x) atTop (𝓝 x)) {K σ : ℝ}
    (hbound : ∀ i, ‖e i‖ ≤ K) (hσpos : 0 < σ) {z : X} (st : Coh act σ z) : A :=
  Classical.choose
    (exists_factor_index act e he hstrong hbound hσpos st.s st.aInv st.n z)

private lemma pickedB_spec {ι : Type*} [Preorder ι] [Nonempty ι]
    [IsDirected ι (· ≤ ·)] (e : ι → A) (he : IsBoundedLeftApproximateIdentity e)
    (hstrong : ∀ x, Tendsto (fun i ↦ act (e i) x) atTop (𝓝 x)) {K σ : ℝ}
    (hbound : ∀ i, ‖e i‖ ≤ K) (hσpos : 0 < σ) {z : X} (st : Coh act σ z) :
    ‖pickedB act e he hstrong hbound hσpos st‖ ≤ K ∧
      ‖pickedB act e he hstrong hbound hσpos st * st.s - st.s‖ ≤ σ ^ st.n ∧
        ‖act (pickedB act e he hstrong hbound hσpos st) z - z‖ ≤
          stepEps (max ‖act‖ 1) ‖st.aInv‖ st.n :=
  Classical.choose_spec
    (exists_factor_index act e he hstrong hbound hσpos st.s st.aInv st.n z)

private noncomputable def pickedφ {ι : Type*} [Preorder ι] [Nonempty ι]
    [IsDirected ι (· ≤ ·)] (e : ι → A) (he : IsBoundedLeftApproximateIdentity e)
    (hstrong : ∀ x, Tendsto (fun i ↦ act (e i) x) atTop (𝓝 x)) {K C σ : ℝ}
    (hK : 1 ≤ K) (hC : C = 1 / (K + 2)) (hbound : ∀ i, ‖e i‖ ≤ K) (hσpos : 0 < σ)
    {z : X} (st : Coh act σ z) : U 𝕜 A :=
  Classical.choose (uOf_isUnit hK hC (pickedB act e he hstrong hbound hσpos st)
    (pickedB_spec act e he hstrong hbound hσpos st).1)

private lemma pickedφ_spec {ι : Type*} [Preorder ι] [Nonempty ι]
    [IsDirected ι (· ≤ ·)] (e : ι → A) (he : IsBoundedLeftApproximateIdentity e)
    (hstrong : ∀ x, Tendsto (fun i ↦ act (e i) x) atTop (𝓝 x)) {K C σ : ℝ}
    (hK : 1 ≤ K) (hC : C = 1 / (K + 2)) (hbound : ∀ i, ‖e i‖ ≤ K) (hσpos : 0 < σ)
    {z : X} (st : Coh act σ z) :
    uOf C (pickedB act e he hstrong hbound hσpos st) *
        pickedφ act e he hstrong hK hC hbound hσpos st = 1 ∧
      pickedφ act e he hstrong hK hC hbound hσpos st *
          uOf C (pickedB act e he hstrong hbound hσpos st) = 1 ∧
        ‖pickedφ act e he hstrong hK hC hbound hσpos st‖ ≤ K + 2 :=
  Classical.choose_spec (uOf_isUnit hK hC (pickedB act e he hstrong hbound hσpos st)
    (pickedB_spec act e he hstrong hbound hσpos st).1)

private noncomputable def cohNext {ι : Type*} [Preorder ι] [Nonempty ι]
    [IsDirected ι (· ≤ ·)]
    (hassoc : ∀ a b (x : X), act (a * b) x = act a (act b x)) (e : ι → A)
    (he : IsBoundedLeftApproximateIdentity e)
    (hstrong : ∀ x, Tendsto (fun i ↦ act (e i) x) atTop (𝓝 x)) {K C σ : ℝ}
    (hK : 1 ≤ K) (hC : C = 1 / (K + 2)) (hσ : σ = 1 - C) (hσpos : 0 < σ)
    (hbound : ∀ i, ‖e i‖ ≤ K) {z : X} (st : Coh act σ z) : Coh act σ z where
  n := st.n + 1
  sPrev := st.s
  yPrev := st.y
  s := (σ : 𝕜) • st.s +
      ((C * σ ^ st.n : ℝ) : 𝕜) • pickedB act e he hstrong hbound hσpos st +
      (C : 𝕜) • (pickedB act e he hstrong hbound hσpos st * st.s)
  a := uOf C (pickedB act e he hstrong hbound hσpos st) * st.a
  aInv := st.aInv * pickedφ act e he hstrong hK hC hbound hσpos st
  y := actU act (st.aInv * pickedφ act e he hstrong hK hC hbound hσpos st) z
  ha := by
    rw [st.ha, uOf_mul_pow hσ (pickedB act e he hstrong hbound hσpos st) st.s st.n]
  hmul := by
    set b : A := pickedB act e he hstrong hbound hσpos st
    set φ : U 𝕜 A := pickedφ act e he hstrong hK hC hbound hσpos st
    have hφ := pickedφ_spec act e he hstrong hK hC hbound hσpos st
    have hre : st.a * (st.aInv * φ) = st.a * st.aInv * φ := (mul_assoc _ _ _).symm
    change (uOf C b * st.a) * (st.aInv * φ) = 1
    rw [mul_assoc, hre, st.hmul, one_mul, hφ.1]
  hinv := by
    set b : A := pickedB act e he hstrong hbound hσpos st
    set φ : U 𝕜 A := pickedφ act e he hstrong hK hC hbound hσpos st
    have hφ := pickedφ_spec act e he hstrong hK hC hbound hσpos st
    have hre : φ * (uOf C b * st.a) = φ * uOf C b * st.a := (mul_assoc _ _ _).symm
    change (st.aInv * φ) * (uOf C b * st.a) = 1
    rw [mul_assoc, hre, hφ.2.1, one_mul, st.hinv]
  hy := rfl
  hds := norm_step_s hK hC hσ hσpos.le st.n
    (pickedB_spec act e he hstrong hbound hσpos st).1
    (pickedB_spec act e he hstrong hbound hσpos st).2.1
  hdy := by
    rw [st.hy]
    exact (norm_step_y act hK hC hassoc
        (pickedφ_spec act e he hstrong hK hC hbound hσpos st).2.1
        (pickedφ_spec act e he hstrong hK hC hbound hσpos st).2.2 st.aInv z
        (pickedB_spec act e he hstrong hbound hσpos st).2.2).trans
      (stepEps_scaled (max ‖act‖ 1) ‖st.aInv‖ st.n (le_max_right _ _) (norm_nonneg _))

private lemma factor_of_bai {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    [CompleteSpace X]
    (hassoc : ∀ a b (x : X), act (a * b) x = act a (act b x)) (e : ι → A)
    (he : IsBoundedLeftApproximateIdentity e)
    (hstrong : ∀ x, Tendsto (fun i ↦ act (e i) x) atTop (𝓝 x)) (z : X) :
    ∃ a : A, ∃ y : X, z = act a y := by
  obtain ⟨M, hM⟩ := he.1
  let K := max M 1
  have hK : 1 ≤ K := le_max_right _ _
  have hbound : ∀ i, ‖e i‖ ≤ K := fun i => (hM i).trans (le_max_left _ _)
  let C : ℝ := 1 / (K + 2)
  let σ : ℝ := 1 - C
  have hCdef : C = 1 / (K + 2) := rfl
  have hσdef : σ = 1 - C := rfl
  have hCpos : 0 < C := div_pos one_pos (by linarith : 0 < K + 2)
  have hClt : C < 1 := by rw [hCdef, div_lt_one (by linarith : 0 < K + 2)]; linarith
  have hσpos : 0 < σ := sub_pos.mpr hClt
  have hσlt : σ < 1 := sub_lt_self _ hCpos
  let seq : ℕ → Coh act σ z := Nat.rec (motive := fun _ => Coh act σ z) (cohZero act z)
    (fun _ st => cohNext act hassoc e he hstrong hK hCdef hσdef hσpos hbound st)
  have hsucc : ∀ n, seq (n + 1) =
      cohNext act hassoc e he hstrong hK hCdef hσdef hσpos hbound (seq n) := fun _ => rfl
  have hn : ∀ n, (seq n).n = n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        have hstep : (seq (n + 1)).n = (seq n).n + 1 := by rw [hsucc]; rfl
        rw [hstep, ih]
  have hsprev : ∀ n, (seq (n + 1)).sPrev = (seq n).s := by
    intro n; rw [hsucc]; rfl
  have hyprev : ∀ n, (seq (n + 1)).yPrev = (seq n).y := by
    intro n; rw [hsucc]; rfl
  let seqS : ℕ → A := fun n => (seq n).s
  let seqA : ℕ → U 𝕜 A := fun n => (seq n).a
  let seqY : ℕ → X := fun n => (seq n).y
  have hcauchyS : CauchySeq seqS := by
    refine cauchySeq_of_le_geometric σ σ hσlt ?_
    intro n
    rw [dist_eq_norm, norm_sub_rev]
    have hle := (seq (n + 1)).hds
    rw [hsprev n, hn (n + 1)] at hle
    simpa [seqS, pow_succ, mul_comm] using hle
  have hcauchyY : CauchySeq seqY := by
    refine cauchySeq_of_le_geometric ((1 : ℝ) / 2) ((1 : ℝ) / 2) (by norm_num) ?_
    intro n
    rw [dist_eq_norm, norm_sub_rev]
    have hle := (seq (n + 1)).hdy
    rw [hyprev n, hn (n + 1)] at hle
    simpa [seqY, pow_succ, mul_comm] using hle
  obtain ⟨sLim, hs⟩ := cauchySeq_tendsto_of_complete hcauchyS
  obtain ⟨yLim, hy⟩ := cauchySeq_tendsto_of_complete hcauchyY
  have ha : Tendsto seqA atTop (𝓝 (incl sLim)) := by
    have hpow : Tendsto (fun n : ℕ => (σ : 𝕜) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one <| by
        rw [RCLike.norm_ofReal, abs_of_nonneg hσpos.le]; exact hσlt
    have hof : Tendsto (fun n => ofS ((σ : 𝕜) ^ n)) atTop (𝓝 (0 : U 𝕜 A)) := by
      change Tendsto ((algebraMap 𝕜 (U 𝕜 A)) ∘ fun n => (σ : 𝕜) ^ n) atTop _
      rw [show (0 : U 𝕜 A) = algebraMap 𝕜 (U 𝕜 A) (0 : 𝕜) by simp]
      exact ((continuous_algebraMap 𝕜 (U 𝕜 A)).tendsto (0 : 𝕜)).comp hpow
    have hsi : Tendsto (fun n => incl (seqS n)) atTop (𝓝 (incl sLim)) :=
      ((unitization_isometry_inr (𝕜 := 𝕜) (A := A)).continuous.tendsto sLim).comp hs
    have hsum := (hof.add hsi)
    rw [zero_add] at hsum
    have hfun : seqA = fun n => ofS ((σ : 𝕜) ^ n) + incl (seqS n) := by
      funext n; simpa [seqA, seqS, hn n] using (seq n).ha
    rw [← hfun] at hsum
    exact hsum
  have hclose := Metric.tendsto_nhds.mp ha 1 one_pos
  rw [Filter.eventually_atTop] at hclose
  obtain ⟨N, hN⟩ := hclose
  let B : ℝ := ‖(incl sLim : U 𝕜 A)‖ + 1 +
    Finset.sum (Finset.range N) (fun i => ‖(seqA i : U 𝕜 A)‖)
  have hBdef : B = ‖(incl sLim : U 𝕜 A)‖ + 1 +
      Finset.sum (Finset.range N) (fun i => ‖(seqA i : U 𝕜 A)‖) := rfl
  have hB : ∀ n, ‖seqA n‖ ≤ B := by
    intro n
    rcases le_or_gt N n with hnN | hnN
    · have hlt : ‖seqA n - incl sLim‖ < 1 := by rw [← dist_eq_norm]; exact hN n hnN
      have hsum : 0 ≤ ∑ i ∈ Finset.range N, ‖seqA i‖ :=
        Finset.sum_nonneg fun _ _ => norm_nonneg _
      calc
        ‖seqA n‖ = ‖seqA n - incl sLim + incl sLim‖ := by rw [sub_add_cancel]
        _ ≤ ‖seqA n - incl sLim‖ + ‖incl sLim‖ := norm_add_le _ _
        _ ≤ ‖incl sLim‖ + 1 := by linarith
        _ ≤ B := by rw [hBdef]; linarith
    · have hsng := Finset.single_le_sum (f := fun i : ℕ => ‖(seqA i : U 𝕜 A)‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr hnN)
      calc
        ‖seqA n‖ ≤ Finset.sum (Finset.range N) (fun i => ‖(seqA i : U 𝕜 A)‖) := hsng
        _ ≤ B := by rw [hBdef]; linarith [norm_nonneg (incl sLim : U 𝕜 A)]
  set Mm := max ‖act‖ 1
  have hlim : Tendsto (fun n => actU act (seqA n) (seqY n)) atTop
      (𝓝 (actU act (incl sLim) yLim)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (g := fun n => (Mm * B) * ‖seqY n - yLim‖ +
        (Mm * ‖yLim‖) * ‖seqA n - incl sLim‖) (fun _ => norm_nonneg _) ?_ ?_
    · intro n
      have hEq : actU act (seqA n) (seqY n) - actU act (incl sLim) yLim =
          actU act (seqA n) (seqY n - yLim) + actU act (seqA n - incl sLim) yLim := by
        rw [actU_sub_right, actU_sub]; abel
      calc
        ‖actU act (seqA n) (seqY n) - actU act (incl sLim) yLim‖
          ≤ ‖actU act (seqA n) (seqY n - yLim)‖ +
              ‖actU act (seqA n - incl sLim) yLim‖ := by rw [hEq]; exact norm_add_le _ _
        _ ≤ Mm * ‖seqA n‖ * ‖seqY n - yLim‖ + Mm * ‖seqA n - incl sLim‖ * ‖yLim‖ := by
            gcongr <;> exact norm_actU_le act _ _
        _ ≤ (Mm * B) * ‖seqY n - yLim‖ + (Mm * ‖yLim‖) * ‖seqA n - incl sLim‖ := by
            calc
              Mm * ‖seqA n‖ * ‖seqY n - yLim‖ + Mm * ‖seqA n - incl sLim‖ * ‖yLim‖
                ≤ Mm * B * ‖seqY n - yLim‖ + Mm * ‖seqA n - incl sLim‖ * ‖yLim‖ := by
                  gcongr
                  exact hB n
              _ = (Mm * B) * ‖seqY n - yLim‖ +
                    (Mm * ‖yLim‖) * ‖seqA n - incl sLim‖ := by ring
    · have hy0 := (tendsto_iff_norm_sub_tendsto_zero.mp hy).const_mul (Mm * B)
      have ha0 := (tendsto_iff_norm_sub_tendsto_zero.mp ha).const_mul (Mm * ‖yLim‖)
      simpa [mul_zero, add_zero] using hy0.add ha0
  have hz : ∀ n, actU act (seqA n) (seqY n) = z := by
    intro n
    simp only [seqA, seqY]
    rw [(seq n).hy, ← actU_mul act hassoc, (seq n).hmul, actU_one]
  have hconst : Tendsto (fun n => actU act (seqA n) (seqY n)) atTop (𝓝 z) := by
    have hfun : (fun n => actU act (seqA n) (seqY n)) = fun _ => z := by
      funext n; exact hz n
    simpa [hfun] using tendsto_const_nhds (x := z)
  refine ⟨sLim, yLim, ?_⟩
  simpa [actU_incl] using tendsto_nhds_unique hconst hlim

end CohenHewitt

/-- **20.47**, Cohen–Hewitt factorization for a bounded directed approximate identity
acting strongly as the identity on a real or complex Banach module. The action is a continuous
bilinear map, which supports genuinely nonunital algebras without requiring a unital Module
instance. -/
theorem cohen_hewitt_factorization {𝕜 ι A X : Type*} [RCLike 𝕜] [Preorder ι] [Nonempty ι]
    [IsDirected ι (· ≤ ·)] [NonUnitalNormedRing A]
    [NormedSpace 𝕜 A] [CompleteSpace A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    (act : A →L[𝕜] X →L[𝕜] X)
    (hassoc : ∀ a b x, act (a * b) x = act a (act b x))
    (e : ι → A) (he : IsBoundedLeftApproximateIdentity e)
    (hstrong : ∀ x, Tendsto (fun i ↦ act (e i) x) atTop (𝓝 x)) :
    ∀ x : X, ∃ a : A, ∃ y : X, x = act a y :=
  fun x => factor_of_bai act hassoc e he hstrong x

end CKMA
