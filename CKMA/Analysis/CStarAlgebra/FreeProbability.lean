/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import TauCeti.Probability.FreeProbability.Cumulant.Series

import Batteries.Data.Nat.Lemmas
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.Nat.Choose.Central
import TauCeti.Combinatorics.Enumerative.Catalan
import TauCeti.Combinatorics.NoncrossingPartition.Norm
import TauCeti.Probability.FreeProbability.CentralLimit
import TauCeti.Probability.FreeProbability.Cumulant.Bounds
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Free moments, free cumulants, and the R-transform

Freeness of unital subalgebras is tested on nonempty alternating centered words; it is TauCeti's
free independence (`CKMA.areFreeSubalgebras_iff_isFreelyIndependent`). The free central limit
statement is convergence of each moment to the Catalan moments of the normalized semicircle law,
for a normalized functional and identically distributed free variables; it is derived from
TauCeti's free central limit theorem. No positivity of the functional and no self-adjointness or
boundedness of the variables is needed for this algebraic moment assertion.

Free cumulants are defined by a triangular moment recursion. For a normalized functional they are
the coefficients of TauCeti's free cumulant series
(`CKMA.freeCumulants_noncommutativeMoments`), and coefficientwise additivity follows from TauCeti's
additivity of the R-series on free subalgebras. Analytic R-transform additivity holds on a common
convergence disk for bounded variables and a continuous normalized functional; the radius comes
from TauCeti's exponential bounds on noncrossing Möbius coefficients. Sources: GAPS 23.65 and
23.68.

## Main definitions

* `CKMA.AreFreeSubalgebras`: algebraic freeness of unital subalgebras with respect to a linear
  functional.
* `CKMA.noncommutativeMoments`: scalar moments `φ (a ^ n)` of a noncommutative variable.
* `CKMA.semicircleMoment`: Catalan moments of the centered variance-one semicircle law.
* `CKMA.momentCompositionCoefficient`: composition coefficients of a scalar moment series.
* `CKMA.freeCumulants`: free cumulants defined by the triangular moment-cumulant recursion.
* `CKMA.freeRTransform`: formal power series of the R-transform near zero.

## Main results

* `CKMA.areFreeSubalgebras_iff_isFreelyIndependent`: the freeness predicate is TauCeti's
  `TauCeti.IsFreelyIndependent`.
* `CKMA.freeCumulants_noncommutativeMoments`: for a normalized functional, the free cumulants are
  the coefficients of `TauCeti.freeCumulantSeries`.
* `CKMA.free_central_limit`: free central limit theorem in moments (**23.65**).
* `CKMA.freeCumulants_add`: additivity of free cumulants for free variables (**23.68**).
* `CKMA.freeRTransform_add`: analytic R-transform additivity on a common disk of convergence.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped BigOperators

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- Algebraic freeness of unital subalgebras: nonempty alternating centered words have zero
expectation. Excluding the empty word is essential for a normalized functional. -/
def AreFreeSubalgebras {ι : Type*} (φ : A →ₗ[ℂ] ℂ) (S : ι → Subalgebra ℂ A) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ i : Fin n → ι, ∀ a : Fin n → A,
    (∀ j, a j ∈ S (i j)) → (∀ j, φ (a j) = 0) →
    (∀ j k : Fin n, j.val + 1 = k.val → i j ≠ i k) → φ (List.ofFn a).prod = 0

/-- The scalar moments of a noncommutative variable. -/
def noncommutativeMoments (φ : A →ₗ[ℂ] ℂ) (a : A) (n : ℕ) : ℂ := φ (a ^ n)

/-- Moments of the centered variance-one semicircle law, written in the closed Catalan form. -/
def semicircleMoment (n : ℕ) : ℂ :=
  if Even n then ((Nat.choose n (n / 2) / (n / 2 + 1) : ℕ) : ℂ) else 0

/-- A normalized positive functional in the star-algebra setting. -/
@[deprecated "no statement uses this predicate" (since := "2026-11-15")]
def IsPositiveNoncommutativeState {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]
    (φ : B →ₗ[ℂ] ℂ) : Prop :=
  φ 1 = 1 ∧ ∀ a : B, ∃ r : ℝ, 0 ≤ r ∧ φ (star a * a) = (r : ℂ)

/-- `AreFreeSubalgebras` is TauCeti's free independence of subalgebras: words indexed by `Fin n`
are lists of labelled letters. -/
theorem areFreeSubalgebras_iff_isFreelyIndependent {ι : Type*} {φ : A →ₗ[ℂ] ℂ}
    {S : ι → Subalgebra ℂ A} : AreFreeSubalgebras φ S ↔ TauCeti.IsFreelyIndependent φ S := by
  rw [TauCeti.isFreelyIndependent_iff]
  constructor
  · intro h w hne halt hmem hcen
    obtain ⟨n, f, rfl⟩ : ∃ n, ∃ f : Fin n → ι × A, List.ofFn f = w := ⟨_, _, List.ofFn_get w⟩
    rw [List.map_ofFn, List.isChain_ofFn] at halt
    rw [List.map_ofFn]
    refine h n (Nat.pos_of_ne_zero fun h0 => hne (by subst h0; exact List.ofFn_zero))
      (fun j => (f j).1) (fun j => (f j).2) (fun j => hmem _ (List.mem_ofFn.2 ⟨j, rfl⟩))
      (fun j => hcen _ (List.mem_ofFn.2 ⟨j, rfl⟩)) ?_
    rintro ⟨j, hj⟩ ⟨k, hk⟩ (hjk : j + 1 = k)
    subst hjk
    exact halt j hk
  · intro h n hn i a hmem hcen halt
    have := h (List.ofFn fun j => (i j, a j))
      (fun h0 => hn.ne' (List.ofFn_eq_nil_iff.1 h0))
      (by
        rw [List.map_ofFn, List.isChain_ofFn]
        exact fun j hj => halt ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl)
      (fun x hx => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
        exact hmem j)
      (fun x hx => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
        exact hcen j)
    rwa [List.map_ofFn] at this

/-- **23.65**, the free central limit theorem in moments. The functional is normalized, the
variables are centered with unit variance, and their complete moment sequences agree. No
positivity of the functional and no self-adjointness or boundedness of the variables is needed
for this algebraic moment assertion. -/
theorem free_central_limit {B : Type*} [Ring B] [Algebra ℂ B]
    (φ : B →ₗ[ℂ] ℂ) (hφ : φ 1 = 1) (X : ℕ → B) (hmean : ∀ i, φ (X i) = 0)
    (hvar : ∀ i, φ (X i ^ 2) = 1)
    (hlaw : ∀ i m, noncommutativeMoments φ (X i) m = noncommutativeMoments φ (X 0) m)
    (hfree : AreFreeSubalgebras φ (fun i ↦ Algebra.adjoin ℂ {X i})) (m : ℕ) :
    Tendsto (fun n : ℕ ↦ φ ((((Real.sqrt (n + 1) : ℂ)⁻¹) •
      (∑ i ∈ Finset.range (n + 1), X i)) ^ m)) atTop (𝓝 (semicircleMoment m)) := by
  have h : TauCeti.IsFreelyIndependentElements φ X :=
    TauCeti.isFreelyIndependentElements_iff.2 (areFreeSubalgebras_iff_isFreelyIndependent.1 hfree)
  have hbdd : ∀ k, ∃ M, ∀ j, ‖φ (X j ^ k)‖ ≤ M :=
    fun k => ⟨‖φ (X 0 ^ k)‖, fun j => (congrArg norm (hlaw j k)).le⟩
  have hlim : Tendsto (fun N : ℕ => φ (((√(N : ℝ) : ℂ)⁻¹ • ∑ j ∈ Finset.range N, X j) ^ m))
      atTop (𝓝 (semicircleMoment m)) := by
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
    · have hv : Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N, φ (X j ^ 2)) atTop
          (𝓝 1) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ne_atTop 0] with N hN
        rw [Finset.sum_congr rfl fun j _ => hvar j, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, mul_one, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hN)]
      convert h.tendsto_apply_inv_sqrt_smul_sum_pow_two_mul hφ hmean hbdd hv k using 2
      rw [semicircleMoment, ite_eq_left (even_two_mul k), one_pow, one_mul,
        Nat.mul_div_cancel_left k two_pos, catalan_eq_centralBinom_div,
        Nat.centralBinom_eq_two_mul_choose]
    · convert h.tendsto_apply_inv_sqrt_smul_sum_pow_two_mul_add_one hφ hmean hbdd k using 2
      rw [semicircleMoment, ite_eq_right (Nat.not_even_iff_odd.2 (odd_two_mul_add_one k))]
  refine ((tendsto_add_atTop_iff_nat 1).2 hlim).congr fun n => ?_
  simp only [Nat.cast_add, Nat.cast_one]

/-- The finite composition coefficient of the kth power of a scalar moment series. -/
def momentCompositionCoefficient (m : ℕ → ℂ) (k n : ℕ) : ℂ :=
  ∑ a : Fin k → Fin (n + 1), if (∑ j, (a j).val) = n then ∏ j, m (a j).val else 0

/-- Free cumulants defined by the triangular moment recursion obtained by distinguishing
the block containing the first point of a noncrossing partition. No existence theorem is used. -/
def freeCumulants (m : ℕ → ℂ) (n : ℕ) : ℂ := by
  classical
  exact Nat.strongRecOn n (fun k previous ↦ if hk : k = 0 then 0 else
    m k - ∑ j : Fin (k - 1), previous (j.val + 1) (by omega) *
      momentCompositionCoefficient m (j.val + 1) (k - (j.val + 1)))

/-- The R-transform represented by its convergent cumulant series near zero. Its analytic
convergence is a theorem for bounded variables; totalized sums outside that region are not used. -/
def freeRTransform (φ : A →ₗ[ℂ] ℂ) (a : A) (z : ℂ) : ℂ :=
  ∑' n, freeCumulants (noncommutativeMoments φ a) (n + 1) * z ^ n


/-- The free cumulant of order zero is zero. -/
@[simp]
theorem freeCumulants_zero (m : ℕ → ℂ) : freeCumulants m 0 = 0 := by
  rw [freeCumulants, Nat.strongRecOn_eq]
  dsimp only
  rw [dite_eq_left rfl]

/-- The triangular moment-cumulant recursion defining the free cumulants of positive order. -/
theorem freeCumulants_of_ne_zero (m : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    freeCumulants m n = m n - ∑ j : Fin (n - 1), freeCumulants m (j.val + 1) *
      momentCompositionCoefficient m (j.val + 1) (n - (j.val + 1)) := by
  rw [freeCumulants, Nat.strongRecOn_eq]
  dsimp only
  rw [dite_eq_right hn]
  rfl

/-- Sums over tuples with entries bounded by any `N ≥ n` compute the coefficient of `z ^ n` in a
power of the moment series. -/
private theorem sum_ite_prod_eq_coeff_pow (m : ℕ → ℂ) :
    ∀ (k : ℕ) {N n : ℕ}, n ≤ N →
      (∑ a : Fin k → Fin (N + 1), if (∑ j, (a j).val) = n then ∏ j, m (a j).val else 0) =
        PowerSeries.coeff n (PowerSeries.mk m ^ k)
  | 0, N, n, _ => by simp [PowerSeries.coeff_one, eq_comm]
  | k + 1, N, n, hn => by
    rw [← (Fin.consEquiv fun _ => Fin (N + 1)).sum_comp, Fintype.sum_prod_type]
    trans ∑ x : Fin (N + 1),
      if (x : ℕ) ≤ n then m x * PowerSeries.coeff (n - x) (PowerSeries.mk m ^ k) else 0
    · refine Finset.sum_congr rfl fun x _ => ?_
      simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.cons_zero,
        Fin.cons_succ]
      by_cases hxn : (x : ℕ) ≤ n
      · have key (s : ℕ) (P : ℂ) : (if (x : ℕ) + s = n then m x * P else 0) =
            m x * (if s = n - x then P else 0) := by
          split_ifs <;> first | rfl | (exfalso; omega) | simp
        rw [ite_eq_left hxn, ← sum_ite_prod_eq_coeff_pow m k (N := N) (n := n - x) (by omega),
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => key _ _
      · have key (s : ℕ) (P : ℂ) : (if (x : ℕ) + s = n then m x * P else 0) = 0 :=
          ite_eq_right (by omega)
        rw [ite_eq_right hxn]
        exact Finset.sum_eq_zero fun t _ => key _ _
    · have hr : (Finset.range (N + 1)).filter (· ≤ n) = Finset.range (n + 1) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      rw [Fin.sum_univ_eq_sum_range
          (fun i => if i ≤ n then m i * PowerSeries.coeff (n - i) (PowerSeries.mk m ^ k) else 0),
        ← Finset.sum_filter, hr, pow_succ', PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i (PowerSeries.mk m) *
            PowerSeries.coeff j (PowerSeries.mk m ^ k))]
      exact Finset.sum_congr rfl fun i _ => by rw [PowerSeries.coeff_mk]

/-- The composition coefficient `momentCompositionCoefficient m k n` is the coefficient of `z ^ n`
in the `k`-th power of the series `∑ m n z ^ n`. -/
theorem momentCompositionCoefficient_eq_coeff (m : ℕ → ℂ) (k n : ℕ) :
    momentCompositionCoefficient m k n = PowerSeries.coeff n (PowerSeries.mk m ^ k) :=
  sum_ite_prod_eq_coeff_pow m k le_rfl

/-- For a normalized functional, the free cumulants of positive order defined by the triangular
recursion are the coefficients of TauCeti's free cumulant series. -/
theorem freeCumulants_noncommutativeMoments (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1) (a : A) {n : ℕ}
    (hn : n ≠ 0) :
    freeCumulants (noncommutativeMoments φ a) n =
      PowerSeries.coeff n (TauCeti.freeCumulantSeries φ a) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hM : TauCeti.momentSeries φ a = PowerSeries.mk (noncommutativeMoments φ a) := by
    ext k
    rw [TauCeti.coeff_momentSeries, PowerSeries.coeff_mk]
    rfl
  have hterm (k : ℕ) (hk : k ≤ n + 1) :
      PowerSeries.coeff (n + 1)
          ((PowerSeries.X * PowerSeries.mk (noncommutativeMoments φ a)) ^ k) =
        PowerSeries.coeff (n + 1 - k) (PowerSeries.mk (noncommutativeMoments φ a) ^ k) := by
    rw [mul_pow, PowerSeries.coeff_X_pow_mul', ite_eq_left hk]
  have hsum : ∑ k ∈ Finset.range (n + 1 + 1),
      PowerSeries.coeff k (TauCeti.freeCumulantSeries φ a) •
        PowerSeries.coeff (n + 1)
          ((PowerSeries.X * PowerSeries.mk (noncommutativeMoments φ a)) ^ k) =
      ∑ k ∈ Finset.range (n + 1 + 1), PowerSeries.coeff k (TauCeti.freeCumulantSeries φ a) *
        PowerSeries.coeff (n + 1 - k) (PowerSeries.mk (noncommutativeMoments φ a) ^ k) :=
    Finset.sum_congr rfl fun k hk => by
      rw [smul_eq_mul, hterm k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]
  have h0 : PowerSeries.coeff 0 (TauCeti.freeCumulantSeries φ a) *
      PowerSeries.coeff (n + 1 - 0) (PowerSeries.mk (noncommutativeMoments φ a) ^ 0) = 0 := by
    simp
  have htop : PowerSeries.coeff (n + 1 - (n + 1))
      (PowerSeries.mk (noncommutativeMoments φ a) ^ (n + 1)) = 1 := by
    rw [Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, ← hM,
      TauCeti.constantCoeff_momentSeries, hφ, one_pow]
  have h := congrArg (PowerSeries.coeff (n + 1))
    (TauCeti.freeCumulantSeries_subst_X_mul_momentSeries a hφ)
  rw [PowerSeries.coeff_subst_eq_sum_range (TauCeti.freeCumulantSeries φ a)
      (g := PowerSeries.X * TauCeti.momentSeries φ a) (by simp) (n + 1), hM, hsum,
    Finset.sum_range_succ, Finset.sum_range_succ', h0, htop, PowerSeries.coeff_mk] at h
  have hmid : ∑ j ∈ Finset.range n, freeCumulants (noncommutativeMoments φ a) (j + 1) *
      momentCompositionCoefficient (noncommutativeMoments φ a) (j + 1) (n + 1 - (j + 1)) =
      ∑ k ∈ Finset.range n, PowerSeries.coeff (k + 1) (TauCeti.freeCumulantSeries φ a) *
        PowerSeries.coeff (n + 1 - (k + 1))
          (PowerSeries.mk (noncommutativeMoments φ a) ^ (k + 1)) :=
    Finset.sum_congr rfl fun j hj => by
      rw [ih (j + 1) (by simp only [Finset.mem_range] at hj; omega) j.add_one_ne_zero,
        momentCompositionCoefficient_eq_coeff]
  rw [freeCumulants_of_ne_zero _ n.add_one_ne_zero, Nat.add_sub_cancel,
    Fin.sum_univ_eq_sum_range (fun j => freeCumulants (noncommutativeMoments φ a) (j + 1) *
      momentCompositionCoefficient (noncommutativeMoments φ a) (j + 1) (n + 1 - (j + 1))), hmid]
  linear_combination -h

/-- **23.68**: for free variables `a` and `b`, every free cumulant of `a + b` is the sum of the
corresponding free cumulants of `a` and of `b`. At order zero all three cumulants vanish. -/
theorem freeCumulants_add (φ : A →ₗ[ℂ] ℂ) (hφ : φ 1 = 1)
    (S : Fin 2 → Subalgebra ℂ A) (hfree : AreFreeSubalgebras φ S)
    {a b : A} (ha : a ∈ S 0) (hb : b ∈ S 1) {n : ℕ} :
    freeCumulants (noncommutativeMoments φ (a + b)) n =
      freeCumulants (noncommutativeMoments φ a) n +
        freeCumulants (noncommutativeMoments φ b) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [freeCumulants_noncommutativeMoments φ hφ _ hn.ne',
    freeCumulants_noncommutativeMoments φ hφ _ hn.ne',
    freeCumulants_noncommutativeMoments φ hφ _ hn.ne']
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [TauCeti.coeff_succ_freeCumulantSeries, TauCeti.coeff_succ_freeCumulantSeries,
    TauCeti.coeff_succ_freeCumulantSeries,
    (areFreeSubalgebras_iff_isFreelyIndependent.1 hfree).rSeries_add hφ
      (by decide : (0 : Fin 2) ≠ 1) ha hb, map_add]

/-- Exponential bound for the free cumulants of a bounded element under a bounded functional:
`‖κₙ(x)‖ ≤ (16 K ‖x‖) ^ n` whenever `1 ≤ K` and `‖φ‖ ≤ K`. -/
private theorem norm_coeff_freeCumulantSeries_le {B : Type*} [NormedRing B] [NormedAlgebra ℂ B]
    (φ : B →L[ℂ] ℂ) {K : ℝ} (hK : 1 ≤ K) (hφK : ‖φ‖ ≤ K) (x : B) (n : ℕ) :
    ‖PowerSeries.coeff n (TauCeti.freeCumulantSeries φ x)‖ ≤ (16 * K * ‖x‖) ^ n := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hKx : 0 ≤ K * ‖x‖ := mul_nonneg hK0 (norm_nonneg x)
  have hM : ∀ k, 0 < k → k ≤ (Finset.univ : Finset (Fin n)).card →
      ‖φ (x ^ k)‖ ≤ (K * ‖x‖) ^ k := by
    intro k hk _
    calc ‖φ (x ^ k)‖ ≤ ‖φ‖ * ‖x ^ k‖ := φ.le_opNorm _
      _ ≤ K ^ k * ‖x‖ ^ k :=
        mul_le_mul (hφK.trans (le_self_pow₀ hK hk.ne')) (norm_pow_le' x hk) (norm_nonneg _)
          (pow_nonneg hK0 k)
      _ = (K * ‖x‖) ^ k := (mul_pow _ _ _).symm
  rw [TauCeti.coeff_freeCumulantSeries]
  refine (TauCeti.norm_freeCumulant_const_le _ x hM).trans ?_
  calc _ ≤ ∑ _π : TauCeti.NoncrossingPartition (Finset.univ : Finset (Fin n)),
        (4 : ℝ) ^ n * (K * ‖x‖) ^ n := by
        refine Finset.sum_le_sum fun π _ => ?_
        rw [Finset.prod_pow_eq_pow_sum, π.1.sum_card_parts, Finset.card_univ, Fintype.card_fin]
        exact mul_le_mul_of_nonneg_right (TauCeti.NoncrossingPartition.norm_mu_top_le π)
          (pow_nonneg hKx n)
    _ = catalan n * ((4 : ℝ) ^ n * (K * ‖x‖) ^ n) := by
        rw [Finset.sum_const, Finset.card_univ, TauCeti.NoncrossingPartition.card_fin_eq_catalan,
          nsmul_eq_mul]
    _ ≤ (4 : ℝ) ^ n * ((4 : ℝ) ^ n * (K * ‖x‖) ^ n) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.catalan_le_four_pow n)
          (mul_nonneg (pow_nonneg (by norm_num) n) (pow_nonneg hKx n))
    _ = (16 * K * ‖x‖) ^ n := by
        rw [show (16 : ℝ) * K * ‖x‖ = 4 * (4 * (K * ‖x‖)) by ring, mul_pow 4 (4 * (K * ‖x‖)),
          mul_pow 4 (K * ‖x‖)]

/-- The analytic R-transform identity on a genuine common convergence disk for bounded
variables and a bounded normalized functional. -/
theorem freeRTransform_add {B : Type*} [NormedRing B] [NormedAlgebra ℂ B]
    (φ : B →L[ℂ] ℂ) (hφ : φ 1 = 1)
    (S : Fin 2 → Subalgebra ℂ B) (hfree : AreFreeSubalgebras φ.toLinearMap S)
    {a b : B} (ha : a ∈ S 0) (hb : b ∈ S 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r →
      Summable (fun n ↦ freeCumulants (noncommutativeMoments φ.toLinearMap a) (n + 1) * z ^ n) ∧
      Summable (fun n ↦ freeCumulants (noncommutativeMoments φ.toLinearMap b) (n + 1) * z ^ n) ∧
      Summable (fun n ↦ freeCumulants (noncommutativeMoments φ.toLinearMap (a + b)) (n + 1) * z ^ n)
        ∧
      freeRTransform φ.toLinearMap (a + b) z =
        freeRTransform φ.toLinearMap a z + freeRTransform φ.toLinearMap b z := by
  have hφ' : φ.toLinearMap 1 = 1 := hφ
  obtain ⟨K, hK, hφK⟩ : ∃ K : ℝ, 1 ≤ K ∧ ‖φ‖ ≤ K := ⟨_, le_max_left 1 ‖φ‖, le_max_right _ _⟩
  set L := ‖a‖ + ‖b‖ + 1 with hL
  have hc : 0 < 16 * K * L := by
    have : 0 < L := by positivity
    have : 0 < K := zero_lt_one.trans_le hK
    positivity
  refine ⟨(16 * K * L)⁻¹, inv_pos.2 hc, fun z hz => ?_⟩
  have hq : 16 * K * L * ‖z‖ < 1 :=
    (mul_lt_mul_of_pos_left hz hc).trans_eq (mul_inv_cancel₀ hc.ne')
  have hsum : ∀ x : B, ‖x‖ ≤ L →
      Summable fun n => freeCumulants (noncommutativeMoments φ.toLinearMap x) (n + 1) * z ^ n := by
    intro x hx
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (by positivity) hq).mul_left (16 * K * L)) fun n => ?_
    calc ‖freeCumulants (noncommutativeMoments φ.toLinearMap x) (n + 1) * z ^ n‖
        = ‖PowerSeries.coeff (n + 1) (TauCeti.freeCumulantSeries φ.toLinearMap x)‖ *
            ‖z‖ ^ n := by
          rw [freeCumulants_noncommutativeMoments _ hφ' _ n.add_one_ne_zero, norm_mul, norm_pow]
      _ ≤ (16 * K * L) ^ (n + 1) * ‖z‖ ^ n := by
          refine mul_le_mul_of_nonneg_right
            ((norm_coeff_freeCumulantSeries_le φ hK hφK x (n + 1)).trans ?_) (by positivity)
          have : 0 ≤ K := zero_le_one.trans hK
          gcongr
      _ = 16 * K * L * (16 * K * L * ‖z‖) ^ n := by
          rw [pow_succ', mul_pow (16 * K * L) ‖z‖ n, mul_assoc (16 * K * L)]
  have ha' := hsum a (by linarith [norm_nonneg b])
  have hb' := hsum b (by linarith [norm_nonneg a])
  refine ⟨ha', hb', hsum (a + b) ((norm_add_le a b).trans (by linarith)), ?_⟩
  rw [freeRTransform, freeRTransform, freeRTransform, ← ha'.tsum_add hb']
  refine tsum_congr fun n => ?_
  rw [freeCumulants_add φ.toLinearMap hφ' S hfree ha hb, add_mul]

end CKMA
