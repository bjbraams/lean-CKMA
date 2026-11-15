/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.RoughPath.Sewing.VariationEstimate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Uniform grid approximations for the Young integral

Uniform partition sums of a Young increment are Cauchy when the paths are
continuous and have complementary finite `p`- and `q`-variation. The limit is
additive and continuous on the sewing triangle.

## Main definitions

* `CKMA.YoungLoeve.YoungData`: paths, exponents, and finiteness hypotheses for one Young integral.
* `CKMA.YoungLoeve.YoungData.youngGrid`: sum of Young increments on the uniform `k`-grid.
* `CKMA.YoungLoeve.YoungData.youngLimit`: limit of the uniform Young sums.

## Main results

* `CKMA.YoungLoeve.YoungData.tendsto_youngGrid`: uniform Young sums converge to `youngLimit`.
* `CKMA.YoungLoeve.YoungData.continuousOn_youngLimit`: `youngLimit` is continuous on
  `sewingTriangle D.a D.b`.
* `CKMA.YoungLoeve.YoungData.youngLimit_add`: `youngLimit` is additive on every subinterval.
-/

@[expose] public section

noncomputable section

namespace CKMA

namespace YoungLoeve

open scoped BigOperators NNReal ENNReal
open Finset Filter Topology Metric Sewing

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Paths, exponents, and finiteness hypotheses for one Young integral. -/
structure YoungData (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  /-- Left endpoint of the interval. -/
  a : ℝ
  /-- Right endpoint of the interval. -/
  b : ℝ
  /-- Variation exponent of the integrand path. -/
  p : ℝ
  /-- Variation exponent of the integrator path. -/
  q : ℝ
  /-- The interval runs from left to right. -/
  hab : a ≤ b
  /-- The integrand exponent is at least one. -/
  hp : 1 ≤ p
  /-- The integrator exponent is at least one. -/
  hq : 1 ≤ q
  /-- The variation exponents are Young-complementary. -/
  hpq : 1 < p⁻¹ + q⁻¹
  /-- Integrand path. -/
  X : ℝ → E
  /-- Integrator path. -/
  Y : ℝ → E →L[ℝ] F
  /-- The integrand path is continuous on `[a, b]`. -/
  hX : ContinuousOn X (Set.Icc a b)
  /-- The integrator path is continuous on `[a, b]`. -/
  hY : ContinuousOn Y (Set.Icc a b)
  /-- The integrand path has finite `p`-variation on `[a, b]`. -/
  hVp : pathVariationPower p X a b ≠ ∞
  /-- The integrator path has finite `q`-variation on `[a, b]`. -/
  hVq : pathVariationPower q Y a b ≠ ∞

/-- The point-removal series is nonnegative. -/
lemma youngLoose_nonneg (θ : ℝ) : 0 ≤ youngLoose θ :=
  tsum_nonneg fun k => youngPartial_pos_term θ k

namespace YoungData

variable {D : YoungData E F}

/-- Uniform node, frozen after the last index of a `k`-grid. -/
private def gridNode (s t : ℝ) (k i : ℕ) : ℝ :=
  equalNode s t k (min i k)

/-- The frozen uniform grid nodes are monotone when `s ≤ t`. -/
private lemma monotone_gridNode {s t : ℝ} (hst : s ≤ t) (k : ℕ) : Monotone (gridNode s t k) := by
  intro i j hij
  exact equalNode_mono hst k (min_le_min hij le_rfl)

/-- The first node of the frozen uniform grid is the left endpoint `s`. -/
private lemma gridNode_zero (s t : ℝ) (k : ℕ) : gridNode s t k 0 = s := by
  simp [gridNode, equalNode_zero]

/-- The `k`-th node of a positive frozen uniform grid is the right endpoint `t`. -/
private lemma gridNode_last {s t : ℝ} {k : ℕ} (hk : 0 < k) : gridNode s t k k = t := by
  simpa [gridNode, Nat.min_eq_left le_rfl] using equalNode_last s t hk

variable (D) in
/-- Sum of Young increments on the uniform `k`-grid. -/
def youngGrid (s t : ℝ) (k : ℕ) : F :=
  equalSewn (youngIncrement D.X D.Y) s t k

/-- The uniform grid sum equals the step sum along `gridNode`. -/
private lemma youngGrid_eq_step (s t : ℝ) (k : ℕ) :
    D.youngGrid s t k = stepSum (youngIncrement D.X D.Y) (gridNode s t k) k := by
  unfold youngGrid stepSum gridNode
  refine sum_congr rfl fun i hi => ?_
  have hi0 : i ≤ k := le_of_lt (mem_range.mp hi)
  have hi1 : i + 1 ≤ k := Nat.succ_le_of_lt (mem_range.mp hi)
  simp [Nat.min_eq_left hi0, Nat.min_eq_left hi1]

/-- A priori removal bound for one uniform Young sum. -/
private lemma norm_youngGrid_sub {s t : ℝ} (hs : D.a ≤ s) (hst : s ≤ t) (ht : t ≤ D.b) {k : ℕ}
    (hk : 0 < k) :
    ‖D.youngGrid s t k - youngIncrement D.X D.Y s t‖ ≤
      youngLoose (youngTheta D.p D.q) * youngModulus D.p D.q D.X D.Y s t := by
  have h0 := gridNode_zero s t k
  have hlast : gridNode s t k k = t := gridNode_last hk
  have hXfin : pathVariationPower D.p D.X s t ≠ ∞ :=
    ne_top_of_le_ne_top D.hVp (pathVariationPower_mono hs ht D.p D.X)
  have hYfin : pathVariationPower D.q D.Y s t ≠ ∞ :=
    ne_top_of_le_ne_top D.hVq (pathVariationPower_mono hs ht D.q D.Y)
  have hbound := young_step_bound D.hp D.hq D.hpq
    D.X D.Y k (gridNode s t k)
    (monotone_gridNode hst k) (by simpa [h0, hlast] using hXfin)
    (by simpa [h0, hlast] using hYfin)
  rw [← youngGrid_eq_step s t k, h0, hlast] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (youngPartial_le_loose (by simpa [youngTheta] using D.hpq) (k - 1))
    (youngModulus_nonneg D.X D.Y s t))

/-- Split a rectangular range into consecutive blocks. -/
private lemma sum_range_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k m : ℕ) :
    ∑ n ∈ range (k * m), f n =
      ∑ i ∈ range k, ∑ j ∈ range m, f (i * m + j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

/-- A uniform subgrid repeats the parent nodes. -/
private lemma equalNode_mul (s t : ℝ) {k j m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    equalNode s t (k * m) (j * m) = equalNode s t k j := by
  unfold equalNode
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [Nat.cast_mul, Nat.cast_mul]
  field_simp [hk0, hm0]

/-- One block of a refined uniform grid is the uniform grid of that block. -/
private lemma equalNode_block (s t : ℝ) (k m i j : ℕ) (hk : 0 < k) (hm : 0 < m) :
    equalNode s t (k * m) (i * m + j) =
      equalNode (equalNode s t k i) (equalNode s t k (i + 1)) m j := by
  unfold equalNode
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_add]
  field_simp [hk0, hm0]
  ring

/-- A product grid is the sum of the uniform grids of its blocks. -/
private lemma youngGrid_mul {s t : ℝ} {k m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    D.youngGrid s t (k * m) =
      ∑ i ∈ range k,
        D.youngGrid (equalNode s t k i) (equalNode s t k (i + 1)) m := by
  unfold youngGrid equalSewn
  rw [sum_range_mul (fun n => youngIncrement D.X D.Y (equalNode s t (k * m) n)
    (equalNode s t (k * m) (n + 1))) k m]
  refine sum_congr rfl fun i _ => ?_
  refine sum_congr rfl fun j _ => ?_
  have hL := equalNode_block s t k m i j hk hm
  have hR := equalNode_block s t k m i (j + 1) hk hm
  have hidx : i * m + (j + 1) = i * m + j + 1 := by omega
  rw [← hidx, hL, hR]

/-- `ctrl ^ θ ≤ η ^ (θ - 1) · ctrl` once `ctrl ≤ η`. -/
lemma youngModulus_le_eta {s t η : ℝ}
    (hctrl : youngCtrl D.p D.q D.X D.Y s t ≤ η) :
    youngModulus D.p D.q D.X D.Y s t ≤
      η ^ (youngTheta D.p D.q - 1) * youngCtrl D.p D.q D.X D.Y s t := by
  have hθ1 : 0 ≤ youngTheta D.p D.q - 1 :=
    sub_nonneg.mpr (by simpa [youngTheta] using D.hpq.le)
  rw [youngModulus_eq_ctrl_pow D.hp D.hq D.hpq
    D.X D.Y s t]
  rcases eq_or_lt_of_le (youngCtrl_nonneg D.X D.Y s t) with h0 | hpos
  · rw [← h0, Real.zero_rpow (youngTheta_pos D.hpq).ne', mul_zero]
  · have hsplit : youngCtrl D.p D.q D.X D.Y s t ^ youngTheta D.p D.q =
        youngCtrl D.p D.q D.X D.Y s t ^ (youngTheta D.p D.q - 1) *
          youngCtrl D.p D.q D.X D.Y s t := by
      have hsum : youngTheta D.p D.q - 1 + 1 = youngTheta D.p D.q := by ring
      conv_lhs => rw [← hsum]
      rw [Real.rpow_add hpos (youngTheta D.p D.q - 1) 1, Real.rpow_one]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (youngCtrl_nonneg D.X D.Y s t) hctrl hθ1)
      (youngCtrl_nonneg D.X D.Y s t)

/-- Controls of successive steps add up to the control of the whole chain. -/
lemma ctrl_sum_seq (n : ℕ) (c : ℕ → ℝ) (hc : Monotone c) (h0 : D.a ≤ c 0) (hn : c n ≤ D.b) :
    ∑ i ∈ range n, youngCtrl D.p D.q D.X D.Y (c i) (c (i + 1)) ≤
      youngCtrl D.p D.q D.X D.Y (c 0) (c n) := by
  induction n with
  | zero =>
    simp
    exact youngCtrl_nonneg D.X D.Y (c 0) (c 0)
  | succ n ih =>
    rw [sum_range_succ]
    have hstep : c n ≤ c (n + 1) := hc (Nat.le_succ n)
    have hmid : c 0 ≤ c n := hc (Nat.zero_le n)
    have hcn : c n ≤ D.b := hstep.trans hn
    have hfinX : pathVariationPower D.p D.X (c 0) (c (n + 1)) ≠ ∞ :=
      ne_top_of_le_ne_top D.hVp (pathVariationPower_mono h0 hn D.p D.X)
    have hfinY : pathVariationPower D.q D.Y (c 0) (c (n + 1)) ≠ ∞ :=
      ne_top_of_le_ne_top D.hVq (pathVariationPower_mono h0 hn D.q D.Y)
    exact (add_le_add (ih hcn) le_rfl).trans
      (youngCtrl_superadd hmid hstep D.hp D.hq D.hpq
        D.X D.Y hfinX hfinY)

/-- Refining every block of a short grid changes the Young sum by a small amount. -/
private lemma norm_youngGrid_mul_sub {s t η : ℝ} (hs : D.a ≤ s) (hst : s ≤ t) (ht : t ≤ D.b)
    {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (hη : 0 ≤ η)
    (hpiece : ∀ i < k, youngCtrl D.p D.q D.X D.Y (equalNode s t k i)
      (equalNode s t k (i + 1)) ≤ η) :
    ‖D.youngGrid s t (k * m) - D.youngGrid s t k‖ ≤
      youngLoose (youngTheta D.p D.q) * η ^ (youngTheta D.p D.q - 1) *
        youngCtrl D.p D.q D.X D.Y s t := by
  have hsum : D.youngGrid s t (k * m) - D.youngGrid s t k =
      ∑ i ∈ range k, (D.youngGrid (equalNode s t k i) (equalNode s t k (i + 1)) m -
        youngIncrement D.X D.Y (equalNode s t k i)
          (equalNode s t k (i + 1))) := by
    rw [youngGrid_mul hk hm]
    have hgrid : D.youngGrid s t k =
        ∑ i ∈ range k, youngIncrement D.X D.Y (equalNode s t k i)
          (equalNode s t k (i + 1)) := by
      simp [youngGrid, equalSewn]
    rw [hgrid, ← sum_sub_distrib]
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  have hθ : 1 < youngTheta D.p D.q := by simpa [youngTheta] using D.hpq
  have hcoef : 0 ≤ youngLoose (youngTheta D.p D.q) * η ^ (youngTheta D.p D.q - 1) :=
    mul_nonneg (youngLoose_nonneg _) (Real.rpow_nonneg hη _)
  have hterm : ∀ i ∈ range k,
      ‖D.youngGrid (equalNode s t k i) (equalNode s t k (i + 1)) m -
          youngIncrement D.X D.Y (equalNode s t k i)
            (equalNode s t k (i + 1))‖ ≤
        (youngLoose (youngTheta D.p D.q) * η ^ (youngTheta D.p D.q - 1)) *
          youngCtrl D.p D.q D.X D.Y (equalNode s t k i)
            (equalNode s t k (i + 1)) := by
    intro i hi
    have hi0 : i ≤ k := le_of_lt (mem_range.mp hi)
    have hi1 : i + 1 ≤ k := Nat.succ_le_of_lt (mem_range.mp hi)
    have hL := equalNode_mem hst hk hi0
    have hR := equalNode_mem hst hk hi1
    have hord := equalNode_mono hst k (Nat.le_succ i)
    have hmod := norm_youngGrid_sub (le_trans hs hL.1) hord (le_trans hR.2 ht) hm
    have hpow := youngModulus_le_eta (hpiece i (mem_range.mp hi))
    calc
      ‖D.youngGrid (equalNode s t k i) (equalNode s t k (i + 1)) m -
          youngIncrement D.X D.Y (equalNode s t k i)
            (equalNode s t k (i + 1))‖ ≤
          youngLoose (youngTheta D.p D.q) *
            youngModulus D.p D.q D.X D.Y (equalNode s t k i)
              (equalNode s t k (i + 1)) := hmod
      _ ≤ youngLoose (youngTheta D.p D.q) * (η ^ (youngTheta D.p D.q - 1) *
          youngCtrl D.p D.q D.X D.Y (equalNode s t k i)
            (equalNode s t k (i + 1))) :=
        mul_le_mul_of_nonneg_left hpow (youngLoose_nonneg _)
      _ = (youngLoose (youngTheta D.p D.q) * η ^ (youngTheta D.p D.q - 1)) *
          youngCtrl D.p D.q D.X D.Y (equalNode s t k i)
            (equalNode s t k (i + 1)) := by
        rw [mul_assoc]
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  have hmon : Monotone (equalNode s t k) := fun i j hij => equalNode_mono hst k hij
  have h0 : D.a ≤ equalNode s t k 0 := by simpa [equalNode_zero] using hs
  have hn : equalNode s t k k ≤ D.b := by simpa [equalNode_last s t hk] using ht
  have hchain := ctrl_sum_seq k (equalNode s t k) hmon h0 hn
  rw [equalNode_zero, equalNode_last s t hk] at hchain
  exact mul_le_mul_of_nonneg_left hchain hcoef

/-- Uniform Young sums form a Cauchy sequence, at a rate uniform on the triangle. -/
private lemma exists_youngGrid_cauchy (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∀ s t : ℝ, D.a ≤ s → s ≤ t → t ≤ D.b →
      ∀ k m : ℕ, K ≤ k → K ≤ m → ‖D.youngGrid s t k - D.youngGrid s t m‖ < ε := by
  have hθ : 1 < youngTheta D.p D.q := by simpa [youngTheta] using D.hpq
  have hθ1 : 0 < youngTheta D.p D.q - 1 := sub_pos.mpr hθ
  set Λ : ℝ := youngLoose (youngTheta D.p D.q)
  set Ω : ℝ := youngCtrl D.p D.q D.X D.Y D.a D.b
  have hΛ : 0 ≤ Λ := youngLoose_nonneg _
  have hΩ : 0 ≤ Ω := youngCtrl_nonneg D.X D.Y D.a D.b
  set C : ℝ := Λ * Ω
  have hC : 0 ≤ C := mul_nonneg hΛ hΩ
  set τ : ℝ := ε / (3 * (C + 1))
  have hτ : 0 < τ := div_pos hε (mul_pos (by norm_num) (by linarith))
  set η : ℝ := τ ^ (youngTheta D.p D.q - 1)⁻¹
  have hη : 0 < η := Real.rpow_pos_of_pos hτ _
  have hηpow : η ^ (youngTheta D.p D.q - 1) = τ := by
    rw [← Real.rpow_mul hτ.le]
    have hinv : (youngTheta D.p D.q - 1)⁻¹ * (youngTheta D.p D.q - 1) = 1 := by
      field_simp [hθ1.ne']
    rw [hinv, Real.rpow_one]
  have hτle : C * τ ≤ ε / 3 := by
    simp only [τ]
    rw [mul_div, div_le_iff₀ (by linarith : (0 : ℝ) < 3 * (C + 1))]
    have hclear : ε / 3 * (3 * (C + 1)) = ε * (C + 1) := by ring
    rw [hclear]
    linarith [hε, hC]
  obtain ⟨δ, hδ, hδc⟩ :=
    exists_ctrl_short D.hp D.hq D.hpq
      D.X D.Y D.hX D.hY
      D.hVp D.hVq η hη
  obtain ⟨K, hK⟩ := exists_nat_gt ((D.b - D.a) / δ)
  have hK0 : 0 < K := Nat.cast_pos.mp (lt_of_le_of_lt
    (div_nonneg (sub_nonneg.mpr D.hab) hδ.le) hK)
  refine ⟨K, hK0, fun s t hs hst ht k m hk hm => ?_⟩
  have hk0 : 0 < k := lt_of_lt_of_le hK0 hk
  have hm0 : 0 < m := lt_of_lt_of_le hK0 hm
  have hdiv : ∀ n : ℕ, K ≤ n → (D.b - D.a) / (n : ℝ) < δ := by
    intro n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (lt_of_lt_of_le hK0 hn)
    have hKcast : (D.b - D.a) / (K : ℝ) < δ := by
      rw [div_lt_iff₀ (Nat.cast_pos.mpr hK0)]
      have hmul : (D.b - D.a) / δ * δ < (K : ℝ) * δ :=
        mul_lt_mul_of_pos_right hK hδ
      simpa [div_mul_cancel₀ _ hδ.ne', mul_comm (K : ℝ) δ] using hmul
    exact lt_of_le_of_lt (div_le_div_of_nonneg_left (sub_nonneg.mpr D.hab)
      (Nat.cast_pos.mpr hK0) (Nat.cast_le.mpr hn)) hKcast
  have hpiece : ∀ n : ℕ, K ≤ n → ∀ i < n,
      youngCtrl D.p D.q D.X D.Y (equalNode s t n i)
        (equalNode s t n (i + 1)) ≤ η := by
    intro n hn i hi
    have hn0 : 0 < n := lt_of_lt_of_le hK0 hn
    have hi0 : i ≤ n := le_of_lt hi
    have hi1 : i + 1 ≤ n := Nat.succ_le_of_lt hi
    have hL := equalNode_mem hst hn0 hi0
    have hR := equalNode_mem hst hn0 hi1
    have hlen : equalNode s t n (i + 1) - equalNode s t n i = (t - s) / n :=
      equalNode_sub s t n i
    have hlt : equalNode s t n (i + 1) - equalNode s t n i < δ := by
      rw [hlen]
      exact lt_of_le_of_lt (div_le_div_of_nonneg_right (by linarith : t - s ≤ D.b - D.a)
        (Nat.cast_nonneg n)) (hdiv n hn)
    exact hδc _ _ (le_trans hs hL.1) (equalNode_mono hst n (Nat.le_succ i))
      (le_trans hR.2 ht) hlt
  have hctrl : youngCtrl D.p D.q D.X D.Y s t ≤ Ω := by
    simpa [Ω] using youngCtrl_mono hs hst ht D.hp D.hq
      D.hpq D.X D.Y
      D.hVp D.hVq
  have hsmall : youngLoose (youngTheta D.p D.q) * η ^ (youngTheta D.p D.q - 1) *
      youngCtrl D.p D.q D.X D.Y s t ≤ ε / 3 := by
    rw [hηpow]
    have hscale : Λ * τ * youngCtrl D.p D.q D.X D.Y s t ≤ Λ * τ * Ω :=
      mul_le_mul_of_nonneg_left hctrl (mul_nonneg hΛ hτ.le)
    have hprod : Λ * τ * Ω = C * τ := by
      simp only [C]
      ring
    exact (hscale.trans (le_of_eq hprod)).trans hτle
  have hgapk := norm_youngGrid_mul_sub hs hst ht hk0 hm0 hη.le (hpiece k hk)
  have hgapm := norm_youngGrid_mul_sub hs hst ht hm0 hk0 hη.le (hpiece m hm)
  have hcomm : m * k = k * m := Nat.mul_comm m k
  have hleft : ‖D.youngGrid s t k - D.youngGrid s t (k * m)‖ ≤ ε / 3 := by
    rw [norm_sub_rev]
    exact hgapk.trans hsmall
  have hright : ‖D.youngGrid s t (k * m) - D.youngGrid s t m‖ ≤ ε / 3 := by
    rw [← hcomm]
    exact hgapm.trans hsmall
  have hsplit : D.youngGrid s t k - D.youngGrid s t m =
      (D.youngGrid s t k - D.youngGrid s t (k * m)) +
        (D.youngGrid s t (k * m) - D.youngGrid s t m) := by abel
  calc
    ‖D.youngGrid s t k - D.youngGrid s t m‖ ≤
        ‖D.youngGrid s t k - D.youngGrid s t (k * m)‖ +
          ‖D.youngGrid s t (k * m) - D.youngGrid s t m‖ := by
      rw [hsplit]; exact norm_add_le _ _
    _ ≤ ε / 3 + ε / 3 := add_le_add hleft hright
    _ < ε := by linarith

variable [CompleteSpace F]

variable (D) in
/-- Limit of the uniform Young sums. -/
def youngLimit (s t : ℝ) : F :=
  limUnder atTop (fun k => D.youngGrid s t (k + 1))

/-- Uniform Young sums converge to `youngLimit` as the grid size tends to infinity. -/
lemma tendsto_youngGrid {s t : ℝ} (hs : D.a ≤ s) (hst : s ≤ t) (ht : t ≤ D.b) :
    Tendsto (fun k => D.youngGrid s t (k + 1)) atTop (𝓝 (D.youngLimit s t)) := by
  refine CauchySeq.tendsto_limUnder ?_
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨K, _, hK⟩ := exists_youngGrid_cauchy (D := D) ε hε
  refine ⟨K, fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  exact hK s t hs hst ht (m + 1) (n + 1)
    (le_trans hm (Nat.le_succ m)) (le_trans hn (Nat.le_succ n))

/-- The Young limit on a degenerate interval `[s, s]` vanishes. -/
lemma youngLimit_same {s : ℝ} (hs : D.a ≤ s) (hsb : s ≤ D.b) : D.youngLimit s s = 0 := by
  have hgrid : ∀ k, D.youngGrid s s (k + 1) = 0 := by
    intro k
    unfold youngGrid equalSewn
    refine sum_eq_zero fun i _ => ?_
    simp [equalNode, youngIncrement, map_zero]
  have htend := tendsto_youngGrid hs le_rfl hsb
  have hfun : (fun k => D.youngGrid s s (k + 1)) = fun _ => 0 := by
    funext k; exact hgrid k
  rw [hfun] at htend
  exact tendsto_nhds_unique htend tendsto_const_nhds

/-- The loose series controls the distance from the limit to the increment. -/
lemma norm_youngLimit_sub {s t : ℝ} (hs : D.a ≤ s) (hst : s ≤ t) (ht : t ≤ D.b) :
    ‖D.youngLimit s t - youngIncrement D.X D.Y s t‖ ≤
      youngLoose (youngTheta D.p D.q) * youngModulus D.p D.q D.X D.Y s t := by
  have htend : Tendsto
      (fun k => ‖D.youngGrid s t (k + 1) - youngIncrement D.X D.Y s t‖) atTop
      (𝓝 ‖D.youngLimit s t - youngIncrement D.X D.Y s t‖) :=
    ((tendsto_youngGrid hs hst ht).sub tendsto_const_nhds).norm
  refine le_of_tendsto' htend ?_
  intro k
  simpa [youngIncrement] using norm_youngGrid_sub hs hst ht (Nat.succ_pos k)

/-- Each uniform grid node depends continuously on the interval endpoints. -/
private lemma continuous_equalNode (k i : ℕ) :
    Continuous (fun z : ℝ × ℝ => equalNode z.1 z.2 k i) := by
  unfold equalNode
  exact continuous_fst.add (((continuous_snd.sub continuous_fst).mul continuous_const))

omit [CompleteSpace F] in
/-- Uniform grid nodes map `sewingTriangle a b` into `[a, b]`. -/
private lemma equalNode_mapsTo {k i : ℕ} (hk : 0 < k) (hi : i ≤ k) :
    Set.MapsTo (fun z : ℝ × ℝ => equalNode z.1 z.2 k i) (sewingTriangle D.a D.b)
      (Set.Icc D.a D.b) := by
  intro z hp
  have hmem := equalNode_mem hp.2.1 hk hi
  exact ⟨le_trans hp.1 hmem.1, le_trans hmem.2 hp.2.2⟩

omit [CompleteSpace F] in
/-- Each piece of a uniform Young sum is continuous on `sewingTriangle a b`. -/
private lemma continuousOn_youngPiece {k i : ℕ} (hk : 0 < k) (hi : i < k) :
    ContinuousOn (fun z : ℝ × ℝ => youngIncrement D.X D.Y
      (equalNode z.1 z.2 k i) (equalNode z.1 z.2 k (i + 1))) (sewingTriangle D.a D.b) := by
  have hYc := D.hY.comp (continuous_equalNode k i).continuousOn
    (equalNode_mapsTo hk (le_of_lt hi))
  have hsub :=
    (D.hX.comp (continuous_equalNode k (i + 1)).continuousOn
      (equalNode_mapsTo hk (Nat.succ_le_of_lt hi))).sub
      (D.hX.comp (continuous_equalNode k i).continuousOn
        (equalNode_mapsTo hk (le_of_lt hi)))
  simpa [youngIncrement] using hYc.clm_apply hsub

omit [CompleteSpace F] in
/-- Uniform Young grid sums are continuous on `sewingTriangle a b`. -/
private lemma continuousOn_youngGrid (k : ℕ) :
    ContinuousOn (fun z : ℝ × ℝ => D.youngGrid z.1 z.2 k) (sewingTriangle D.a D.b) := by
  unfold youngGrid equalSewn
  refine continuousOn_finsetSum _ fun i hi => ?_
  exact continuousOn_youngPiece (Nat.zero_lt_of_lt (mem_range.mp hi)) (mem_range.mp hi)

/-- For every positive tolerance, late uniform sums are uniformly close to the limit. -/
private lemma exists_youngGrid_close (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∀ s t : ℝ, D.a ≤ s → s ≤ t → t ≤ D.b → ∀ k ≥ K,
      ‖D.youngGrid s t k - D.youngLimit s t‖ ≤ ε := by
  obtain ⟨K, hK0, hK⟩ := exists_youngGrid_cauchy (D := D) ε hε
  refine ⟨K, hK0, fun s t hs hst ht k hk => ?_⟩
  have htend := tendsto_youngGrid hs hst ht
  have hdist : Tendsto (fun n => dist (D.youngGrid s t k) (D.youngGrid s t (n + 1))) atTop
      (𝓝 (dist (D.youngGrid s t k) (D.youngLimit s t))) :=
    tendsto_const_nhds.dist htend
  rw [← dist_eq_norm]
  refine le_of_tendsto hdist ?_
  refine eventually_atTop.mpr ⟨K, fun n hn => ?_⟩
  rw [dist_eq_norm]
  exact (hK s t hs hst ht k (n + 1) hk (le_trans hn (Nat.le_succ n))).le

/-- The Young limit is continuous on `sewingTriangle a b`. -/
lemma continuousOn_youngLimit :
    ContinuousOn (fun z : ℝ × ℝ => D.youngLimit z.1 z.2) (sewingTriangle D.a D.b) := by
  intro p0 hp0
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨K, hK0, hclose⟩ := exists_youngGrid_close (D := D) (ε / 3) (by linarith)
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousWithinAt_iff.mp
    ((continuousOn_youngGrid K).continuousWithinAt hp0) (ε / 3) (by linarith)
  refine ⟨δ, hδ, fun z hp hdp => ?_⟩
  have hL := hclose z.1 z.2 hp.1 hp.2.1 hp.2.2 K le_rfl
  have hR := hclose p0.1 p0.2 hp0.1 hp0.2.1 hp0.2.2 K le_rfl
  have hM := hδg hp hdp
  have htri : dist (D.youngLimit z.1 z.2) (D.youngLimit p0.1 p0.2) ≤
      dist (D.youngLimit z.1 z.2) (D.youngGrid z.1 z.2 K) +
        dist (D.youngGrid z.1 z.2 K) (D.youngGrid p0.1 p0.2 K) +
        dist (D.youngGrid p0.1 p0.2 K) (D.youngLimit p0.1 p0.2) :=
    dist_triangle4 _ _ _ _
  have h1 : dist (D.youngLimit z.1 z.2) (D.youngGrid z.1 z.2 K) ≤ ε / 3 := by
    rw [dist_comm, dist_eq_norm]; exact hL
  have h3 : dist (D.youngGrid p0.1 p0.2 K) (D.youngLimit p0.1 p0.2) ≤ ε / 3 := by
    rw [dist_eq_norm]; exact hR
  have hsum : dist (D.youngLimit z.1 z.2) (D.youngLimit p0.1 p0.2) ≤
      ε / 3 + dist (D.youngGrid z.1 z.2 K) (D.youngGrid p0.1 p0.2 K) + ε / 3 := by
    linarith
  linarith

/-- The limit adds across a positive uniform node. -/
private lemma youngLimit_grid_add {s t : ℝ} (hs : D.a ≤ s) (hst : s ≤ t) (ht : t ≤ D.b) {k j : ℕ}
    (hk : 0 < k) (hj0 : 0 < j) (hj : j < k) :
    D.youngLimit s t =
      D.youngLimit s (equalNode s t k j) + D.youngLimit (equalNode s t k j) t := by
  have hmem := equalNode_mem hst hk (le_of_lt hj)
  have hsplit : ∀ m : ℕ, D.youngGrid s t (k * (m + 1)) =
      D.youngGrid s (equalNode s t k j) (j * (m + 1)) +
        D.youngGrid (equalNode s t k j) t ((k - j) * (m + 1)) := by
    intro m
    have hm : 0 < m + 1 := Nat.succ_pos m
    have hcut := equalSewn_cut (youngIncrement D.X D.Y) s t (Nat.mul_pos hk hm)
      (Nat.mul_pos hj0 hm) (Nat.mul_lt_mul_of_pos_right hj hm)
    have hnode : equalNode s t (k * (m + 1)) (j * (m + 1)) =
        equalNode s t k j := equalNode_mul s t hk hm
    have hlen : k * (m + 1) - j * (m + 1) = (k - j) * (m + 1) :=
      (Nat.sub_mul k j (m + 1)).symm
    simpa [youngGrid, hnode, hlen] using hcut
  have hidx (c : ℕ) (hc : 0 < c) :
      Tendsto (fun m : ℕ => c * (m + 1) - 1) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro N
    refine ⟨N, fun m hm => ?_⟩
    have hc1 : 1 ≤ c := hc
    have hmul : m + 1 ≤ c * (m + 1) := by
      simpa [one_mul] using Nat.mul_le_mul_right (m + 1) hc1
    have hge : m ≤ c * (m + 1) - 1 := Nat.le_sub_of_add_le hmul
    exact hm.trans hge
  have hstep (c : ℕ) (hc : 0 < c) (m : ℕ) : 1 ≤ c * (m + 1) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.ne_of_gt hc) (Nat.succ_ne_zero m))
  have hbig : Tendsto (fun m => D.youngGrid s t (k * (m + 1))) atTop
      (𝓝 (D.youngLimit s t)) := by
    have hcomp := (tendsto_youngGrid hs hst ht).comp (hidx k hk)
    have hfun : ((fun n => D.youngGrid s t (n + 1)) ∘ fun m => k * (m + 1) - 1) =
        fun m => D.youngGrid s t (k * (m + 1)) := by
      funext m
      rw [Function.comp_apply]
      exact congrArg (D.youngGrid s t) (Nat.sub_add_cancel (hstep k hk m))
    rwa [hfun] at hcomp
  have hL : Tendsto (fun m => D.youngGrid s (equalNode s t k j) (j * (m + 1))) atTop
      (𝓝 (D.youngLimit s (equalNode s t k j))) := by
    have hcomp := (tendsto_youngGrid hs hmem.1 (hmem.2.trans ht)).comp (hidx j hj0)
    have hfun : ((fun n => D.youngGrid s (equalNode s t k j) (n + 1)) ∘
        fun m => j * (m + 1) - 1) =
        fun m => D.youngGrid s (equalNode s t k j) (j * (m + 1)) := by
      funext m
      rw [Function.comp_apply]
      exact congrArg (D.youngGrid s (equalNode s t k j)) (Nat.sub_add_cancel (hstep j hj0 m))
    rwa [hfun] at hcomp
  have hkj : 0 < k - j := Nat.sub_pos_of_lt hj
  have hR : Tendsto (fun m => D.youngGrid (equalNode s t k j) t ((k - j) * (m + 1))) atTop
      (𝓝 (D.youngLimit (equalNode s t k j) t)) := by
    have hcomp := (tendsto_youngGrid (hs.trans hmem.1) hmem.2 ht).comp (hidx (k - j) hkj)
    have hfun : ((fun n => D.youngGrid (equalNode s t k j) t (n + 1)) ∘
        fun m => (k - j) * (m + 1) - 1) =
        fun m => D.youngGrid (equalNode s t k j) t ((k - j) * (m + 1)) := by
      funext m
      rw [Function.comp_apply]
      exact congrArg (D.youngGrid (equalNode s t k j) t)
        (Nat.sub_add_cancel (hstep (k - j) hkj m))
    rwa [hfun] at hcomp
  have hfun : (fun m => D.youngGrid s t (k * (m + 1))) =
      fun m => D.youngGrid s (equalNode s t k j) (j * (m + 1)) +
        D.youngGrid (equalNode s t k j) t ((k - j) * (m + 1)) := funext hsplit
  rw [hfun] at hbig
  exact tendsto_nhds_unique hbig (hL.add hR)

/-- The Young limit is additive on every subinterval. -/
lemma youngLimit_add {s u t : ℝ} (hs : D.a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (ht : t ≤ D.b) :
    D.youngLimit s t = D.youngLimit s u + D.youngLimit u t := by
  rcases eq_or_lt_of_le hsu with rfl | hslt
  · rw [youngLimit_same hs (hut.trans ht), zero_add]
  rcases eq_or_lt_of_le hut with rfl | hult
  · rw [youngLimit_same (hs.trans hsu) ht, add_zero]
  have hus : 0 < u - s := sub_pos.mpr hslt
  obtain ⟨K0, hK0⟩ := exists_nat_gt ((t - s) / (u - s))
  have hK0pos : 0 < K0 := Nat.cast_pos.mp (lt_of_le_of_lt
    (div_nonneg (sub_nonneg.mpr (hslt.le.trans hult.le)) hus.le) hK0)
  let spec (k : ℕ) (hk : 0 < k) :=
    exists_least_index_gt k (equalNode s t k) u
      ⟨k, le_rfl, by simpa [equalNode_last s t hk] using hult⟩
  let L (k : ℕ) : ℝ :=
    if hk : 0 < k then equalNode s t k (Classical.choose (spec k hk) - 1) else s
  have hcut : ∀ k : ℕ, max K0 1 ≤ k →
      D.youngLimit s t = D.youngLimit s (L k) + D.youngLimit (L k) t ∧
        0 ≤ u - L k ∧ u - L k < (t - s) / k := by
    intro k hk
    have hk0 : 0 < k := lt_of_lt_of_le (lt_of_lt_of_le Nat.one_pos (le_max_right _ _)) hk
    have hspec := Classical.choose_spec (spec k hk0)
    set jk : ℕ := Classical.choose (spec k hk0)
    have hjle : jk ≤ k := hspec.1
    have hgt : u < equalNode s t k jk := hspec.2.1
    have hmin : ∀ i < jk, equalNode s t k i ≤ u := hspec.2.2
    have hjpos : 0 < jk := by
      have hne : jk ≠ 0 := by
        intro h0
        have := hgt
        rw [h0, equalNode_zero] at this
        exact lt_irrefl _ (this.trans_le hslt.le)
      omega
    have hdivk : (t - s) / (k : ℝ) < u - s := by
      have hkK : (K0 : ℝ) ≤ k := Nat.cast_le.mpr (le_trans (le_max_left _ _) hk)
      have hKδ : (t - s) / (K0 : ℝ) < u - s := by
        rw [div_lt_iff₀ (Nat.cast_pos.mpr hK0pos)]
        have hmul : (t - s) / (u - s) * (u - s) < (K0 : ℝ) * (u - s) :=
          mul_lt_mul_of_pos_right hK0 hus
        simpa [div_mul_cancel₀ _ hus.ne', mul_comm (K0 : ℝ) (u - s)] using hmul
      exact lt_of_le_of_lt (div_le_div_of_nonneg_left (sub_nonneg.mpr (hslt.le.trans hult.le))
        (Nat.cast_pos.mpr hK0pos) hkK) hKδ
    have hlt1 : equalNode s t k 1 < u := by
      have hsub := equalNode_sub s t k 0
      rw [equalNode_zero] at hsub
      linarith
    have hj2 : 1 < jk := by
      have hne : jk ≠ 1 := by
        intro h1
        rw [h1] at hgt
        exact lt_irrefl _ (hgt.trans hlt1)
      omega
    have hjpred : 0 < jk - 1 := by omega
    have hjlt : jk - 1 < k := by omega
    have hadd := youngLimit_grid_add hs (hslt.le.trans hult.le) ht hk0 hjpred hjlt
    have hLdef : L k = equalNode s t k (jk - 1) := by
      unfold L
      rw [dite_eq_left hk0]
    have hLle : L k ≤ u := by
      rw [hLdef]
      exact hmin (jk - 1) (by omega)
    have hgap : equalNode s t k jk - equalNode s t k (jk - 1) = (t - s) / k := by
      have hidx : (jk - 1) + 1 = jk := by omega
      simpa [hidx] using equalNode_sub s t k (jk - 1)
    refine ⟨by simpa [hLdef] using hadd, sub_nonneg.mpr hLle, ?_⟩
    rw [hLdef]
    linarith
  have hLtend : Tendsto L atTop (𝓝 u) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt ((t - s) / ε)
    refine ⟨max (max K0 1) N, fun k hk => ?_⟩
    have hcutk := hcut k (le_trans (le_max_left _ _) hk)
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg hcutk.2.1]
    have hkN : (N : ℝ) ≤ k := Nat.cast_le.mpr (le_trans (le_max_right _ _) hk)
    have hN0 : 0 < N := Nat.cast_pos.mp (lt_of_le_of_lt
      (div_nonneg (sub_nonneg.mpr (hslt.le.trans hult.le)) hε.le) hN)
    have hdiv : (t - s) / (k : ℝ) ≤ (t - s) / (N : ℝ) :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr (hslt.le.trans hult.le))
        (Nat.cast_pos.mpr hN0) hkN
    have hNδ : (t - s) / (N : ℝ) < ε := by
      rw [div_lt_iff₀ (Nat.cast_pos.mpr hN0)]
      have hmul : (t - s) / ε * ε < (N : ℝ) * ε := mul_lt_mul_of_pos_right hN hε
      simpa [div_mul_cancel₀ _ hε.ne', mul_comm (N : ℝ) ε] using hmul
    exact lt_of_lt_of_le (lt_of_lt_of_le hcutk.2.2 hdiv) hNδ.le
  have hmemL : ∀ k, (s, L k) ∈ sewingTriangle D.a D.b := by
    intro k
    by_cases hk0 : 0 < k
    · have hspec := Classical.choose_spec (spec k hk0)
      set jk : ℕ := Classical.choose (spec k hk0)
      have hjpos : 0 < jk := by
        have hne : jk ≠ 0 := by
          intro h0
          have hgt := hspec.2.1
          rw [h0, equalNode_zero] at hgt
          exact lt_irrefl _ (hgt.trans_le hslt.le)
        omega
      have hnode := equalNode_mem (hslt.le.trans hult.le) hk0 (by omega : jk - 1 ≤ k)
      have hLdef : L k = equalNode s t k (jk - 1) := by
        unfold L
        rw [dite_eq_left hk0]
      rw [hLdef]
      exact ⟨hs, hnode.1, le_trans hnode.2 ht⟩
    · have hkz : k = 0 := by omega
      have hLs : L k = s := by simp [L, hkz]
      rw [hLs]
      exact ⟨hs, le_rfl, (hslt.le.trans hult.le).trans ht⟩
  have hmemR : ∀ k, (L k, t) ∈ sewingTriangle D.a D.b := by
    intro k
    by_cases hk0 : 0 < k
    · have hspec := Classical.choose_spec (spec k hk0)
      set jk : ℕ := Classical.choose (spec k hk0)
      have hjpos : 0 < jk := by
        have hne : jk ≠ 0 := by
          intro h0
          have hgt := hspec.2.1
          rw [h0, equalNode_zero] at hgt
          exact lt_irrefl _ (hgt.trans_le hslt.le)
        omega
      have hnode := equalNode_mem (hslt.le.trans hult.le) hk0 (by omega : jk - 1 ≤ k)
      have hLdef : L k = equalNode s t k (jk - 1) := by
        unfold L
        rw [dite_eq_left hk0]
      rw [hLdef]
      exact ⟨le_trans hs hnode.1, hnode.2, ht⟩
    · have hkz : k = 0 := by omega
      have hLs : L k = s := by simp [L, hkz]
      rw [hLs]
      exact ⟨hs, hslt.le.trans hult.le, ht⟩
  have hsconst : Tendsto (fun _ : ℕ => s) atTop (𝓝 s) := tendsto_const_nhds
  have hpairL : Tendsto (fun k => (s, L k)) atTop (𝓝[sewingTriangle D.a D.b] (s, u)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hsconst.prodMk_nhds hLtend) (Filter.Eventually.of_forall hmemL)
  have htconst : Tendsto (fun _ : ℕ => t) atTop (𝓝 t) := tendsto_const_nhds
  have hpairR : Tendsto (fun k => (L k, t)) atTop (𝓝[sewingTriangle D.a D.b] (u, t)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hLtend.prodMk_nhds htconst) (Filter.Eventually.of_forall hmemR)
  have htendL := ((continuousOn_youngLimit).continuousWithinAt
    ⟨hs, hslt.le, hult.le.trans ht⟩).tendsto.comp hpairL
  have htendR := ((continuousOn_youngLimit).continuousWithinAt
    ⟨hs.trans hslt.le, hult.le, ht⟩).tendsto.comp hpairR
  have heq : ∀ᶠ k in atTop, D.youngLimit s (L k) + D.youngLimit (L k) t = D.youngLimit s t := by
    refine eventually_atTop.mpr ⟨max K0 1, fun k hk => (hcut k hk).1.symm⟩
  exact (tendsto_nhds_unique ((htendL.add htendR).congr' heq) tendsto_const_nhds).symm

end YoungData

end YoungLoeve

end CKMA
