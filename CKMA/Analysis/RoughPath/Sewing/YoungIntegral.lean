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
# Young integral from complementary finite variation

Uniform partition sums of a Young increment are Cauchy when the paths are
continuous and have complementary finite `p`- and `q`-variation. The limit is
additive and continuous, and the Young–Loeve remainder is
`sewingConstant (p⁻¹ + q⁻¹)` times the product of the variation moduli.
-/

@[expose] public section

noncomputable section

namespace CKMA

namespace YoungLoeve

open scoped BigOperators NNReal ENNReal
open Finset Filter Topology Metric Sewing

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Paths, exponents, and finiteness hypotheses for one Young integral. -/
class YoungData (E : outParam Type*) (F : outParam Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] where
  a : ℝ
  b : ℝ
  p : ℝ
  q : ℝ
  hab : a ≤ b
  hp : 1 ≤ p
  hq : 1 ≤ q
  hpq : 1 < p⁻¹ + q⁻¹
  X : ℝ → E
  Y : ℝ → E →L[ℝ] F
  hX : ContinuousOn X (Set.Icc a b)
  hY : ContinuousOn Y (Set.Icc a b)
  hVp : pathVariationPower p X a b ≠ ∞
  hVq : pathVariationPower q Y a b ≠ ∞

variable [D : YoungData E F]

/-- Left endpoint of the active Young datum. -/
def a : ℝ := D.a
/-- Right endpoint of the active Young datum. -/
def b : ℝ := D.b
/-- Variation exponent of the integrand path. -/
def p : ℝ := D.p
/-- Variation exponent of the integrator path. -/
def q : ℝ := D.q
/-- The datum interval runs from left to right. -/
theorem hab : a ≤ b := D.hab
/-- The integrand exponent is at least one. -/
theorem hp : 1 ≤ p := D.hp
/-- The integrator exponent is at least one. -/
theorem hq : 1 ≤ q := D.hq
/-- The variation exponents are Young-complementary. -/
theorem hpq : 1 < p⁻¹ + q⁻¹ := D.hpq
/-- Integrand path of the active Young datum. -/
def X : ℝ → E := D.X
/-- Integrator path of the active Young datum. -/
def Y : ℝ → E →L[ℝ] F := D.Y
/-- The integrand is continuous on the datum interval. -/
theorem hX : ContinuousOn X (Set.Icc a b) := D.hX
/-- The integrator is continuous on the datum interval. -/
theorem hY : ContinuousOn Y (Set.Icc a b) := D.hY
/-- The integrand has finite `p`-variation on the datum interval. -/
theorem hVp : pathVariationPower p X a b ≠ ∞ := D.hVp
/-- The integrator has finite `q`-variation on the datum interval. -/
theorem hVq : pathVariationPower q Y a b ≠ ∞ := D.hVq

/-- Uniform node, frozen after the last index of a `k`-grid. -/
def gridNode (s t : ℝ) (k i : ℕ) : ℝ :=
  equalNode s t k (min i k)

lemma monotone_gridNode {s t : ℝ} (hst : s ≤ t) (k : ℕ) : Monotone (gridNode s t k) := by
  intro i j hij
  exact equalNode_mono hst k (min_le_min hij le_rfl)

lemma gridNode_zero (s t : ℝ) (k : ℕ) : gridNode s t k 0 = s := by
  simp [gridNode, equalNode_zero]

lemma gridNode_last {s t : ℝ} {k : ℕ} (hk : 0 < k) : gridNode s t k k = t := by
  simpa [gridNode, Nat.min_eq_left le_rfl] using equalNode_last s t hk

/-- Sum of Young increments on the uniform `k`-grid. -/
def youngGrid (s t : ℝ) (k : ℕ) : F :=
  equalSewn (youngStep X Y) s t k

lemma youngGrid_eq_step (s t : ℝ) (k : ℕ) :
    youngGrid s t k = stepSum (youngStep X Y) (gridNode s t k) k := by
  unfold youngGrid stepSum gridNode
  refine sum_congr rfl fun i hi => ?_
  have hi0 : i ≤ k := le_of_lt (mem_range.mp hi)
  have hi1 : i + 1 ≤ k := Nat.succ_le_of_lt (mem_range.mp hi)
  simp [Nat.min_eq_left hi0, Nat.min_eq_left hi1]

/-- A priori removal bound for one uniform Young sum. -/
lemma norm_youngGrid_sub {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) {k : ℕ}
    (hk : 0 < k) :
    ‖youngGrid s t k - youngStep X Y s t‖ ≤
      youngLoose (youngTheta p q) * youngModulus p q X Y s t := by
  have h0 := gridNode_zero s t k
  have hlast : gridNode s t k k = t := gridNode_last hk
  have hXfin : pathVariationPower p X s t ≠ ∞ :=
    ne_top_of_le_ne_top hVp (pathVariationPower_mono hs ht p X)
  have hYfin : pathVariationPower q Y s t ≠ ∞ :=
    ne_top_of_le_ne_top hVq (pathVariationPower_mono hs ht q Y)
  have hbound := young_step_bound hp hq hpq X Y k (gridNode s t k)
    (monotone_gridNode hst k) (by simpa [h0, hlast] using hXfin)
    (by simpa [h0, hlast] using hYfin)
  rw [← youngGrid_eq_step s t k, h0, hlast] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (youngPartial_le_loose (by simpa [youngTheta] using hpq) (k - 1))
    (youngModulus_nonneg X Y s t))

/-- Split a rectangular range into consecutive blocks. -/
lemma sum_range_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k m : ℕ) :
    ∑ n ∈ range (k * m), f n =
      ∑ i ∈ range k, ∑ j ∈ range m, f (i * m + j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

/-- A uniform subgrid repeats the parent nodes. -/
lemma equalNode_mul (s t : ℝ) {k j m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    equalNode s t (k * m) (j * m) = equalNode s t k j := by
  unfold equalNode
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [Nat.cast_mul, Nat.cast_mul]
  field_simp [hk0, hm0]

/-- One block of a refined uniform grid is the uniform grid of that block. -/
lemma equalNode_block (s t : ℝ) (k m i j : ℕ) (hk : 0 < k) (hm : 0 < m) :
    equalNode s t (k * m) (i * m + j) =
      equalNode (equalNode s t k i) (equalNode s t k (i + 1)) m j := by
  unfold equalNode
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_add]
  field_simp [hk0, hm0]
  ring

/-- A product grid is the sum of the uniform grids of its blocks. -/
lemma youngGrid_mul {s t : ℝ} {k m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    youngGrid s t (k * m) =
      ∑ i ∈ range k,
        youngGrid (equalNode s t k i) (equalNode s t k (i + 1)) m := by
  unfold youngGrid equalSewn
  rw [sum_range_mul (fun n => youngStep X Y (equalNode s t (k * m) n)
    (equalNode s t (k * m) (n + 1))) k m]
  refine sum_congr rfl fun i _ => ?_
  refine sum_congr rfl fun j _ => ?_
  have hL := equalNode_block s t k m i j hk hm
  have hR := equalNode_block s t k m i (j + 1) hk hm
  have hidx : i * m + (j + 1) = i * m + j + 1 := by omega
  rw [← hidx, hL, hR]

/-- The point-removal series is nonnegative for exponents greater than one. -/
lemma youngLoose_nonneg {θ : ℝ} (_hθ : 1 < θ) : 0 ≤ youngLoose θ :=
  tsum_nonneg fun k => youngPartial_pos_term θ k

/-- `ctrl ^ θ ≤ η ^ (θ - 1) · ctrl` once `ctrl ≤ η`. -/
lemma youngModulus_le_eta {s t η : ℝ} (_hη : 0 ≤ η)
    (hctrl : youngCtrl p q X Y s t ≤ η) :
    youngModulus p q X Y s t ≤
      η ^ (youngTheta p q - 1) * youngCtrl p q X Y s t := by
  have hθ1 : 0 ≤ youngTheta p q - 1 :=
    sub_nonneg.mpr (by simpa [youngTheta] using hpq.le)
  rw [youngModulus_eq_ctrl_pow hp hq hpq X Y s t]
  rcases eq_or_lt_of_le (youngCtrl_nonneg X Y s t) with h0 | hpos
  · rw [← h0, Real.zero_rpow (youngTheta_pos hpq).ne', mul_zero]
  · have hsplit : youngCtrl p q X Y s t ^ youngTheta p q =
        youngCtrl p q X Y s t ^ (youngTheta p q - 1) * youngCtrl p q X Y s t := by
      have hsum : youngTheta p q - 1 + 1 = youngTheta p q := by ring
      conv_lhs => rw [← hsum]
      rw [Real.rpow_add hpos (youngTheta p q - 1) 1, Real.rpow_one]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (youngCtrl_nonneg X Y s t) hctrl hθ1)
      (youngCtrl_nonneg X Y s t)

/-- Controls of successive steps add up to the control of the whole chain. -/
lemma ctrl_sum_seq (n : ℕ) (c : ℕ → ℝ) (hc : Monotone c) (h0 : a ≤ c 0) (hn : c n ≤ b) :
    ∑ i ∈ range n, youngCtrl p q X Y (c i) (c (i + 1)) ≤
      youngCtrl p q X Y (c 0) (c n) := by
  induction n with
  | zero =>
    simp
    exact youngCtrl_nonneg X Y (c 0) (c 0)
  | succ n ih =>
    rw [sum_range_succ]
    have hstep : c n ≤ c (n + 1) := hc (Nat.le_succ n)
    have hmid : c 0 ≤ c n := hc (Nat.zero_le n)
    have hcn : c n ≤ b := hstep.trans hn
    have hfinX : pathVariationPower p X (c 0) (c (n + 1)) ≠ ∞ :=
      ne_top_of_le_ne_top hVp (pathVariationPower_mono h0 hn p X)
    have hfinY : pathVariationPower q Y (c 0) (c (n + 1)) ≠ ∞ :=
      ne_top_of_le_ne_top hVq (pathVariationPower_mono h0 hn q Y)
    exact (add_le_add (ih hcn) le_rfl).trans
      (youngCtrl_superadd hmid hstep hp hq hpq X Y hfinX hfinY)

/-- Refining every block of a short grid changes the Young sum by a small amount. -/
lemma norm_youngGrid_mul_sub {s t η : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b)
    {k m : ℕ} (hk : 0 < k) (hm : 0 < m) (hη : 0 ≤ η)
    (hpiece : ∀ i < k, youngCtrl p q X Y (equalNode s t k i)
      (equalNode s t k (i + 1)) ≤ η) :
    ‖youngGrid s t (k * m) - youngGrid s t k‖ ≤
      youngLoose (youngTheta p q) * η ^ (youngTheta p q - 1) *
        youngCtrl p q X Y s t := by
  have hsum : youngGrid s t (k * m) - youngGrid s t k =
      ∑ i ∈ range k, (youngGrid (equalNode s t k i) (equalNode s t k (i + 1)) m -
        youngStep X Y (equalNode s t k i) (equalNode s t k (i + 1))) := by
    rw [youngGrid_mul hk hm]
    have hgrid : youngGrid s t k =
        ∑ i ∈ range k, youngStep X Y (equalNode s t k i) (equalNode s t k (i + 1)) := by
      simp [youngGrid, equalSewn]
    rw [hgrid, ← sum_sub_distrib]
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  have hθ : 1 < youngTheta p q := by simpa [youngTheta] using hpq
  have hcoef : 0 ≤ youngLoose (youngTheta p q) * η ^ (youngTheta p q - 1) :=
    mul_nonneg (youngLoose_nonneg hθ) (Real.rpow_nonneg hη _)
  have hterm : ∀ i ∈ range k,
      ‖youngGrid (equalNode s t k i) (equalNode s t k (i + 1)) m -
          youngStep X Y (equalNode s t k i) (equalNode s t k (i + 1))‖ ≤
        (youngLoose (youngTheta p q) * η ^ (youngTheta p q - 1)) *
          youngCtrl p q X Y (equalNode s t k i) (equalNode s t k (i + 1)) := by
    intro i hi
    have hi0 : i ≤ k := le_of_lt (mem_range.mp hi)
    have hi1 : i + 1 ≤ k := Nat.succ_le_of_lt (mem_range.mp hi)
    have hL := equalNode_mem hst hk hi0
    have hR := equalNode_mem hst hk hi1
    have hord := equalNode_mono hst k (Nat.le_succ i)
    have hmod := norm_youngGrid_sub (le_trans hs hL.1) hord (le_trans hR.2 ht) hm
    have hpow := youngModulus_le_eta hη (hpiece i (mem_range.mp hi))
    calc
      ‖youngGrid (equalNode s t k i) (equalNode s t k (i + 1)) m -
          youngStep X Y (equalNode s t k i) (equalNode s t k (i + 1))‖ ≤
          youngLoose (youngTheta p q) *
            youngModulus p q X Y (equalNode s t k i) (equalNode s t k (i + 1)) := hmod
      _ ≤ youngLoose (youngTheta p q) * (η ^ (youngTheta p q - 1) *
          youngCtrl p q X Y (equalNode s t k i) (equalNode s t k (i + 1))) :=
        mul_le_mul_of_nonneg_left hpow (youngLoose_nonneg hθ)
      _ = (youngLoose (youngTheta p q) * η ^ (youngTheta p q - 1)) *
          youngCtrl p q X Y (equalNode s t k i) (equalNode s t k (i + 1)) := by
        rw [mul_assoc]
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  have hmon : Monotone (equalNode s t k) := fun i j hij => equalNode_mono hst k hij
  have h0 : a ≤ equalNode s t k 0 := by simpa [equalNode_zero] using hs
  have hn : equalNode s t k k ≤ b := by simpa [equalNode_last s t hk] using ht
  have hchain := ctrl_sum_seq k (equalNode s t k) hmon h0 hn
  rw [equalNode_zero, equalNode_last s t hk] at hchain
  exact mul_le_mul_of_nonneg_left hchain hcoef

/-- Uniform Young sums form a Cauchy sequence, at a rate uniform on the triangle. -/
lemma exists_youngGrid_cauchy (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b →
      ∀ k m : ℕ, K ≤ k → K ≤ m → ‖youngGrid s t k - youngGrid s t m‖ < ε := by
  have hθ : 1 < youngTheta p q := by simpa [youngTheta] using hpq
  have hθ1 : 0 < youngTheta p q - 1 := sub_pos.mpr hθ
  set Λ : ℝ := youngLoose (youngTheta p q)
  set Ω : ℝ := youngCtrl p q X Y a b
  have hΛ : 0 ≤ Λ := youngLoose_nonneg hθ
  have hΩ : 0 ≤ Ω := youngCtrl_nonneg X Y a b
  set C : ℝ := Λ * Ω
  have hC : 0 ≤ C := mul_nonneg hΛ hΩ
  set τ : ℝ := ε / (3 * (C + 1))
  have hτ : 0 < τ := div_pos hε (mul_pos (by norm_num) (by linarith))
  set η : ℝ := τ ^ (youngTheta p q - 1)⁻¹
  have hη : 0 < η := Real.rpow_pos_of_pos hτ _
  have hηpow : η ^ (youngTheta p q - 1) = τ := by
    rw [← Real.rpow_mul hτ.le]
    have hinv : (youngTheta p q - 1)⁻¹ * (youngTheta p q - 1) = 1 := by
      field_simp [hθ1.ne']
    rw [hinv, Real.rpow_one]
  have hτle : C * τ ≤ ε / 3 := by
    simp only [τ]
    rw [mul_div, div_le_iff₀ (by linarith : (0 : ℝ) < 3 * (C + 1))]
    have hclear : ε / 3 * (3 * (C + 1)) = ε * (C + 1) := by ring
    rw [hclear]
    linarith [hε, hC]
  obtain ⟨δ, hδ, hδc⟩ :=
    exists_ctrl_short hp hq hpq X Y hX hY hVp hVq η hη
  obtain ⟨K, hK⟩ := exists_nat_gt ((b - a) / δ)
  have hK0 : 0 < K := Nat.cast_pos.mp (lt_of_le_of_lt
    (div_nonneg (sub_nonneg.mpr hab) hδ.le) hK)
  refine ⟨K, hK0, fun s t hs hst ht k m hk hm => ?_⟩
  have hk0 : 0 < k := lt_of_lt_of_le hK0 hk
  have hm0 : 0 < m := lt_of_lt_of_le hK0 hm
  have hdiv : ∀ n : ℕ, K ≤ n → (b - a) / (n : ℝ) < δ := by
    intro n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (lt_of_lt_of_le hK0 hn)
    have hKcast : (b - a) / (K : ℝ) < δ := by
      rw [div_lt_iff₀ (Nat.cast_pos.mpr hK0)]
      have hmul : (b - a) / δ * δ < (K : ℝ) * δ :=
        mul_lt_mul_of_pos_right hK hδ
      simpa [div_mul_cancel₀ _ hδ.ne', mul_comm (K : ℝ) δ] using hmul
    exact lt_of_le_of_lt (div_le_div_of_nonneg_left (sub_nonneg.mpr hab)
      (Nat.cast_pos.mpr hK0) (Nat.cast_le.mpr hn)) hKcast
  have hpiece : ∀ n : ℕ, K ≤ n → ∀ i < n,
      youngCtrl p q X Y (equalNode s t n i) (equalNode s t n (i + 1)) ≤ η := by
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
      exact lt_of_le_of_lt (div_le_div_of_nonneg_right (by linarith : t - s ≤ b - a)
        (Nat.cast_nonneg n)) (hdiv n hn)
    exact hδc _ _ (le_trans hs hL.1) (equalNode_mono hst n (Nat.le_succ i))
      (le_trans hR.2 ht) hlt
  have hctrl : youngCtrl p q X Y s t ≤ Ω := by
    simpa [Ω] using youngCtrl_mono hs hst ht hp hq hpq X Y hVp hVq
  have hsmall : youngLoose (youngTheta p q) * η ^ (youngTheta p q - 1) *
      youngCtrl p q X Y s t ≤ ε / 3 := by
    rw [hηpow]
    have hscale : Λ * τ * youngCtrl p q X Y s t ≤ Λ * τ * Ω :=
      mul_le_mul_of_nonneg_left hctrl (mul_nonneg hΛ hτ.le)
    have hprod : Λ * τ * Ω = C * τ := by
      simp only [C]
      ring
    exact (hscale.trans (le_of_eq hprod)).trans hτle
  have hgapk := norm_youngGrid_mul_sub hs hst ht hk0 hm0 hη.le (hpiece k hk)
  have hgapm := norm_youngGrid_mul_sub hs hst ht hm0 hk0 hη.le (hpiece m hm)
  have hcomm : m * k = k * m := Nat.mul_comm m k
  have hleft : ‖youngGrid s t k - youngGrid s t (k * m)‖ ≤ ε / 3 := by
    rw [norm_sub_rev]
    exact hgapk.trans hsmall
  have hright : ‖youngGrid s t (k * m) - youngGrid s t m‖ ≤ ε / 3 := by
    rw [← hcomm]
    exact hgapm.trans hsmall
  have hsplit : youngGrid s t k - youngGrid s t m =
      (youngGrid s t k - youngGrid s t (k * m)) +
        (youngGrid s t (k * m) - youngGrid s t m) := by abel
  calc
    ‖youngGrid s t k - youngGrid s t m‖ ≤
        ‖youngGrid s t k - youngGrid s t (k * m)‖ +
          ‖youngGrid s t (k * m) - youngGrid s t m‖ := by
      rw [hsplit]; exact norm_add_le _ _
    _ ≤ ε / 3 + ε / 3 := add_le_add hleft hright
    _ < ε := by linarith

/-- Limit of the uniform Young sums. -/
def youngLimit (s t : ℝ) : F :=
  limUnder atTop (fun k => youngGrid s t (k + 1))

lemma tendsto_youngGrid {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
    Tendsto (fun k => youngGrid s t (k + 1)) atTop (𝓝 (youngLimit s t)) := by
  refine CauchySeq.tendsto_limUnder ?_
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨K, _, hK⟩ := exists_youngGrid_cauchy ε hε
  refine ⟨K, fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  exact hK s t hs hst ht (m + 1) (n + 1)
    (le_trans hm (Nat.le_succ m)) (le_trans hn (Nat.le_succ n))

lemma youngLimit_same {s : ℝ} (hs : a ≤ s) (hsb : s ≤ b) : youngLimit s s = 0 := by
  have hgrid : ∀ k, youngGrid s s (k + 1) = 0 := by
    intro k
    unfold youngGrid equalSewn
    refine sum_eq_zero fun i _ => ?_
    simp [equalNode, youngStep, map_zero]
  have htend := tendsto_youngGrid hs le_rfl hsb
  have hfun : (fun k => youngGrid s s (k + 1)) = fun _ => 0 := by
    funext k; exact hgrid k
  rw [hfun] at htend
  exact tendsto_nhds_unique htend tendsto_const_nhds

/-- The loose series controls the distance from the limit to the increment. -/
lemma norm_youngLimit_sub {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
    ‖youngLimit s t - youngStep X Y s t‖ ≤
      youngLoose (youngTheta p q) * youngModulus p q X Y s t := by
  have htend : Tendsto (fun k => ‖youngGrid s t (k + 1) - youngStep X Y s t‖) atTop
      (𝓝 ‖youngLimit s t - youngStep X Y s t‖) :=
    ((tendsto_youngGrid hs hst ht).sub tendsto_const_nhds).norm
  refine le_of_tendsto' htend ?_
  intro k
  simpa [youngStep] using norm_youngGrid_sub hs hst ht (Nat.succ_pos k)

lemma continuous_equalNode (k i : ℕ) :
    Continuous (fun p : ℝ × ℝ => equalNode p.1 p.2 k i) := by
  unfold equalNode
  exact continuous_fst.add (((continuous_snd.sub continuous_fst).mul continuous_const))

lemma equalNode_mapsTo {k i : ℕ} (hk : 0 < k) (hi : i ≤ k) :
    Set.MapsTo (fun p : ℝ × ℝ => equalNode p.1 p.2 k i) (sewingTriangle a b)
      (Set.Icc a b) := by
  intro p hp
  have hmem := equalNode_mem hp.2.1 hk hi
  exact ⟨le_trans hp.1 hmem.1, le_trans hmem.2 hp.2.2⟩

lemma continuousOn_youngPiece {k i : ℕ} (hk : 0 < k) (hi : i < k) :
    ContinuousOn (fun p : ℝ × ℝ => youngStep X Y (equalNode p.1 p.2 k i)
      (equalNode p.1 p.2 k (i + 1))) (sewingTriangle a b) := by
  have hYc := hY.comp (continuous_equalNode k i).continuousOn
    (equalNode_mapsTo hk (le_of_lt hi))
  have hsub :=
    (hX.comp (continuous_equalNode k (i + 1)).continuousOn
      (equalNode_mapsTo hk (Nat.succ_le_of_lt hi))).sub
      (hX.comp (continuous_equalNode k i).continuousOn
        (equalNode_mapsTo hk (le_of_lt hi)))
  simpa [youngStep] using hYc.clm_apply hsub

lemma continuousOn_youngGrid (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => youngGrid p.1 p.2 k) (sewingTriangle a b) := by
  unfold youngGrid equalSewn
  refine continuousOn_finsetSum _ fun i hi => ?_
  exact continuousOn_youngPiece (Nat.zero_lt_of_lt (mem_range.mp hi)) (mem_range.mp hi)

/-- For every positive tolerance, late uniform sums are uniformly close to the limit. -/
lemma exists_youngGrid_close (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b → ∀ k ≥ K,
      ‖youngGrid s t k - youngLimit s t‖ ≤ ε := by
  obtain ⟨K, hK0, hK⟩ := exists_youngGrid_cauchy ε hε
  refine ⟨K, hK0, fun s t hs hst ht k hk => ?_⟩
  have htend := tendsto_youngGrid hs hst ht
  have hdist : Tendsto (fun n => dist (youngGrid s t k) (youngGrid s t (n + 1))) atTop
      (𝓝 (dist (youngGrid s t k) (youngLimit s t))) :=
    tendsto_const_nhds.dist htend
  rw [← dist_eq_norm]
  refine le_of_tendsto hdist ?_
  refine eventually_atTop.mpr ⟨K, fun n hn => ?_⟩
  rw [dist_eq_norm]
  exact (hK s t hs hst ht k (n + 1) hk (le_trans hn (Nat.le_succ n))).le

lemma continuousOn_youngLimit :
    ContinuousOn (fun p : ℝ × ℝ => youngLimit p.1 p.2) (sewingTriangle a b) := by
  intro p0 hp0
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨K, hK0, hclose⟩ := exists_youngGrid_close (ε / 3) (by linarith)
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousWithinAt_iff.mp
    ((continuousOn_youngGrid K).continuousWithinAt hp0) (ε / 3) (by linarith)
  refine ⟨δ, hδ, fun p hp hdp => ?_⟩
  have hL := hclose p.1 p.2 hp.1 hp.2.1 hp.2.2 K le_rfl
  have hR := hclose p0.1 p0.2 hp0.1 hp0.2.1 hp0.2.2 K le_rfl
  have hM := hδg hp hdp
  have htri : dist (youngLimit p.1 p.2) (youngLimit p0.1 p0.2) ≤
      dist (youngLimit p.1 p.2) (youngGrid p.1 p.2 K) +
        dist (youngGrid p.1 p.2 K) (youngGrid p0.1 p0.2 K) +
        dist (youngGrid p0.1 p0.2 K) (youngLimit p0.1 p0.2) :=
    dist_triangle4 _ _ _ _
  have h1 : dist (youngLimit p.1 p.2) (youngGrid p.1 p.2 K) ≤ ε / 3 := by
    rw [dist_comm, dist_eq_norm]; exact hL
  have h3 : dist (youngGrid p0.1 p0.2 K) (youngLimit p0.1 p0.2) ≤ ε / 3 := by
    rw [dist_eq_norm]; exact hR
  have hsum : dist (youngLimit p.1 p.2) (youngLimit p0.1 p0.2) ≤
      ε / 3 + dist (youngGrid p.1 p.2 K) (youngGrid p0.1 p0.2 K) + ε / 3 := by
    linarith
  linarith

/-- The limit adds across a positive uniform node. -/
lemma youngLimit_grid_add {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) {k j : ℕ}
    (hk : 0 < k) (hj0 : 0 < j) (hj : j < k) :
    youngLimit s t =
      youngLimit s (equalNode s t k j) + youngLimit (equalNode s t k j) t := by
  have hmem := equalNode_mem hst hk (le_of_lt hj)
  have hsplit : ∀ m : ℕ, youngGrid s t (k * (m + 1)) =
      youngGrid s (equalNode s t k j) (j * (m + 1)) +
        youngGrid (equalNode s t k j) t ((k - j) * (m + 1)) := by
    intro m
    have hm : 0 < m + 1 := Nat.succ_pos m
    have hcut := equalSewn_cut (youngStep X Y) s t (Nat.mul_pos hk hm)
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
  have hbig : Tendsto (fun m => youngGrid s t (k * (m + 1))) atTop
      (𝓝 (youngLimit s t)) := by
    have hcomp := (tendsto_youngGrid hs hst ht).comp (hidx k hk)
    have hfun : ((fun n => youngGrid s t (n + 1)) ∘ fun m => k * (m + 1) - 1) =
        fun m => youngGrid s t (k * (m + 1)) := by
      funext m
      rw [Function.comp_apply]
      exact congrArg (youngGrid s t) (Nat.sub_add_cancel (hstep k hk m))
    rwa [hfun] at hcomp
  have hL : Tendsto (fun m => youngGrid s (equalNode s t k j) (j * (m + 1))) atTop
      (𝓝 (youngLimit s (equalNode s t k j))) := by
    have hcomp := (tendsto_youngGrid hs hmem.1 (hmem.2.trans ht)).comp (hidx j hj0)
    have hfun : ((fun n => youngGrid s (equalNode s t k j) (n + 1)) ∘
        fun m => j * (m + 1) - 1) =
        fun m => youngGrid s (equalNode s t k j) (j * (m + 1)) := by
      funext m
      rw [Function.comp_apply]
      exact congrArg (youngGrid s (equalNode s t k j)) (Nat.sub_add_cancel (hstep j hj0 m))
    rwa [hfun] at hcomp
  have hkj : 0 < k - j := Nat.sub_pos_of_lt hj
  have hR : Tendsto (fun m => youngGrid (equalNode s t k j) t ((k - j) * (m + 1))) atTop
      (𝓝 (youngLimit (equalNode s t k j) t)) := by
    have hcomp := (tendsto_youngGrid (hs.trans hmem.1) hmem.2 ht).comp (hidx (k - j) hkj)
    have hfun : ((fun n => youngGrid (equalNode s t k j) t (n + 1)) ∘
        fun m => (k - j) * (m + 1) - 1) =
        fun m => youngGrid (equalNode s t k j) t ((k - j) * (m + 1)) := by
      funext m
      rw [Function.comp_apply]
      exact congrArg (youngGrid (equalNode s t k j) t)
        (Nat.sub_add_cancel (hstep (k - j) hkj m))
    rwa [hfun] at hcomp
  have hfun : (fun m => youngGrid s t (k * (m + 1))) =
      fun m => youngGrid s (equalNode s t k j) (j * (m + 1)) +
        youngGrid (equalNode s t k j) t ((k - j) * (m + 1)) := funext hsplit
  rw [hfun] at hbig
  exact tendsto_nhds_unique hbig (hL.add hR)

/-- The Young limit is additive on every subinterval. -/
lemma youngLimit_add {s u t : ℝ} (hs : a ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (ht : t ≤ b) :
    youngLimit s t = youngLimit s u + youngLimit u t := by
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
      youngLimit s t = youngLimit s (L k) + youngLimit (L k) t ∧
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
  have hmemL : ∀ k, (s, L k) ∈ sewingTriangle a b := by
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
  have hmemR : ∀ k, (L k, t) ∈ sewingTriangle a b := by
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
  have hpairL : Tendsto (fun k => (s, L k)) atTop (𝓝[sewingTriangle a b] (s, u)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hsconst.prodMk_nhds hLtend) (Filter.Eventually.of_forall hmemL)
  have htconst : Tendsto (fun _ : ℕ => t) atTop (𝓝 t) := tendsto_const_nhds
  have hpairR : Tendsto (fun k => (L k, t)) atTop (𝓝[sewingTriangle a b] (u, t)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hLtend.prodMk_nhds htconst) (Filter.Eventually.of_forall hmemR)
  have htendL := ((continuousOn_youngLimit).continuousWithinAt
    ⟨hs, hslt.le, hult.le.trans ht⟩).tendsto.comp hpairL
  have htendR := ((continuousOn_youngLimit).continuousWithinAt
    ⟨hs.trans hslt.le, hult.le, ht⟩).tendsto.comp hpairR
  have heq : ∀ᶠ k in atTop, youngLimit s (L k) + youngLimit (L k) t = youngLimit s t := by
    refine eventually_atTop.mpr ⟨max K0 1, fun k hk => (hcut k hk).1.symm⟩
  exact (tendsto_nhds_unique ((htendL.add htendR).congr' heq) tendsto_const_nhds).symm

lemma youngCtrl_same (s : ℝ) : youngCtrl p q X Y s s = 0 := by
  rw [youngCtrl, variationReal_point (lt_of_lt_of_le zero_lt_one hp) X s,
    variationReal_point (lt_of_lt_of_le zero_lt_one hq) Y s,
    Real.zero_rpow (youngAlpha_pos hp hpq).ne',
    Real.zero_rpow (youngBeta_pos hq hpq).ne', zero_mul]

lemma continuousOn_ctrl_right {s : ℝ} (hs : a ≤ s) (_hsb : s ≤ b) :
    ContinuousOn (fun r => youngCtrl p q X Y s r) (Set.Icc s b) := by
  have hXs : ContinuousOn X (Set.Icc s b) := hX.mono (Set.Icc_subset_Icc hs le_rfl)
  have hYs : ContinuousOn Y (Set.Icc s b) := hY.mono (Set.Icc_subset_Icc hs le_rfl)
  have hfinX : pathVariationPower p X s b ≠ ∞ :=
    ne_top_of_le_ne_top hVp (pathVariationPower_mono hs le_rfl p X)
  have hfinY : pathVariationPower q Y s b ≠ ∞ :=
    ne_top_of_le_ne_top hVq (pathVariationPower_mono hs le_rfl q Y)
  have hvX := (continuousOn_variationReal hp X hXs hfinX).rpow_const
    (fun _ _ => Or.inr (youngAlpha_pos hp hpq).le)
  have hvY := (continuousOn_variationReal hq Y hYs hfinY).rpow_const
    (fun _ _ => Or.inr (youngBeta_pos hq hpq).le)
  refine (hvX.mul hvY).congr fun r _ => ?_
  simp [youngCtrl, Pi.mul_apply]

lemma two_rpow_neg (θ : ℝ) : (2 : ℝ) * (2 : ℝ) ^ (-θ) = (2 : ℝ) ^ (1 - θ) := by
  have h2 : (2 : ℝ) ^ (1 : ℝ) = 2 := Real.rpow_one _
  calc
    (2 : ℝ) * (2 : ℝ) ^ (-θ) = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-θ) := by
      conv_lhs => arg 1; rw [← h2]
    _ = (2 : ℝ) ^ ((1 : ℝ) + -θ) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2) (1 : ℝ) (-θ)]
    _ = (2 : ℝ) ^ (1 - θ) := by
      congr 1

lemma sewingConstant_shift {θ : ℝ} (hθ : 1 < θ) :
    sewingConstant θ * (2 : ℝ) ^ (1 - θ) + 1 = sewingConstant θ := by
  have hr := Sewing.sewingRatio_mem hθ
  have hne : (1 : ℝ) - (2 : ℝ) ^ (1 - θ) ≠ 0 := (sub_ne_zero.mpr (ne_of_lt hr.2).symm)
  rw [sewingConstant]
  field_simp [hne]
  ring

/-- Removing one medial point upgrades the loose bound to the sewing constant. -/
lemma norm_defect_iterate {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (n : ℕ) :
    ‖youngLimit s t - youngStep X Y s t‖ ≤
      sewingConstant (youngTheta p q) * youngModulus p q X Y s t +
        ((2 : ℝ) ^ (1 - youngTheta p q)) ^ n * youngLoose (youngTheta p q) *
          youngModulus p q X Y s t := by
  induction n generalizing s t with
  | zero =>
    have hloose := norm_youngLimit_sub hs hst ht
    have hκ : 0 ≤ sewingConstant (youngTheta p q) :=
      (Sewing.sewingConstant_pos (by simpa [youngTheta] using hpq)).le
    rw [pow_zero, one_mul]
    exact hloose.trans (le_add_of_nonneg_left
      (mul_nonneg hκ (youngModulus_nonneg X Y s t)))
  | succ n ih =>
    rcases eq_or_lt_of_le (youngCtrl_nonneg X Y s t) with hzero | hpos
    · have hmod0 : youngModulus p q X Y s t = 0 := by
        rw [youngModulus_eq_ctrl_pow hp hq hpq X Y s t, hzero.symm,
          Real.zero_rpow (youngTheta_pos hpq).ne']
      have hloose := norm_youngLimit_sub hs hst ht
      rw [hmod0, mul_zero] at hloose
      simpa [hmod0, mul_zero, add_zero] using hloose
    · have hcont := continuousOn_ctrl_right hs (hst.trans ht)
      have hhalf : youngCtrl p q X Y s t / 2 ∈
          Set.Icc (youngCtrl p q X Y s s) (youngCtrl p q X Y s t) := by
        rw [youngCtrl_same s]
        exact ⟨div_nonneg (youngCtrl_nonneg X Y s t) (by norm_num),
          half_le_self (youngCtrl_nonneg X Y s t)⟩
      obtain ⟨m, hm, hfm⟩ :=
        (intermediate_value_Icc hst (hcont.mono (Set.Icc_subset_Icc le_rfl ht))) hhalf
      have hsm : youngCtrl p q X Y s m = youngCtrl p q X Y s t / 2 := hfm
      have hfinX : pathVariationPower p X s t ≠ ∞ :=
        ne_top_of_le_ne_top hVp (pathVariationPower_mono hs ht p X)
      have hfinY : pathVariationPower q Y s t ≠ ∞ :=
        ne_top_of_le_ne_top hVq (pathVariationPower_mono hs ht q Y)
      have hsuper := youngCtrl_superadd hm.1 hm.2 hp hq hpq X Y hfinX hfinY
      have hright : youngCtrl p q X Y m t ≤ youngCtrl p q X Y s t / 2 := by
        rw [hsm] at hsuper
        linarith
      have hρL : youngModulus p q X Y s m =
          (2 : ℝ) ^ (-youngTheta p q) * youngModulus p q X Y s t := by
        rw [youngModulus_eq_ctrl_pow hp hq hpq X Y s m, hsm,
          youngModulus_eq_ctrl_pow hp hq hpq X Y s t,
          Real.div_rpow (youngCtrl_nonneg X Y s t) (by norm_num : (0 : ℝ) ≤ 2),
          div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        exact mul_comm _ _
      have hρR : youngModulus p q X Y m t ≤
          (2 : ℝ) ^ (-youngTheta p q) * youngModulus p q X Y s t := by
        rw [youngModulus_eq_ctrl_pow hp hq hpq X Y m t,
          youngModulus_eq_ctrl_pow hp hq hpq X Y s t]
        have hle := Real.rpow_le_rpow (youngCtrl_nonneg X Y m t) hright
          (youngTheta_pos hpq).le
        rw [Real.div_rpow (youngCtrl_nonneg X Y s t) (by norm_num : (0 : ℝ) ≤ 2),
          div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
          mul_comm (youngCtrl p q X Y s t ^ youngTheta p q)] at hle
        exact hle
      set ρ : ℝ := youngModulus p q X Y s t
      set r : ℝ := (2 : ℝ) ^ (1 - youngTheta p q)
      set Λ : ℝ := youngLoose (youngTheta p q)
      set κ : ℝ := sewingConstant (youngTheta p q)
      have hadd := youngLimit_add hs hm.1 hm.2 ht
      have hAlg : youngLimit s t - youngStep X Y s t =
          (youngLimit s m - youngStep X Y s m) +
            (youngLimit m t - youngStep X Y m t) +
            (youngStep X Y s m + youngStep X Y m t - youngStep X Y s t) := by
        rw [hadd]
        abel
      have hδ := norm_young_defect hm.1 hm.2 hp hq X Y hfinX hfinY
      have ihL := ih hs hm.1 (hm.2.trans ht)
      have ihR := ih (hs.trans hm.1) hm.2 ht
      have hsumρ : youngModulus p q X Y s m + youngModulus p q X Y m t ≤ r * ρ := by
        calc
          youngModulus p q X Y s m + youngModulus p q X Y m t ≤
              (2 : ℝ) ^ (-youngTheta p q) * ρ + (2 : ℝ) ^ (-youngTheta p q) * ρ := by
            rw [hρL]; exact add_le_add le_rfl hρR
          _ = ((2 : ℝ) * (2 : ℝ) ^ (-youngTheta p q)) * ρ := by ring
          _ = r * ρ := by rw [two_rpow_neg]
      have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
      have hΛ0 : 0 ≤ Λ := youngLoose_nonneg (by simpa [youngTheta] using hpq)
      have hκ0 : 0 ≤ κ := (Sewing.sewingConstant_pos (by simpa [youngTheta] using hpq)).le
      have hcoef : 0 ≤ κ + r ^ n * Λ :=
        add_nonneg hκ0 (mul_nonneg (pow_nonneg hr0 n) hΛ0)
      have hmul := mul_le_mul_of_nonneg_left hsumρ hcoef
      have hthree : ‖youngLimit s t - youngStep X Y s t‖ ≤
          ‖youngLimit s m - youngStep X Y s m‖ +
            ‖youngLimit m t - youngStep X Y m t‖ + ρ := by
        simp only [ρ]
        rw [hAlg]
        refine (norm_add_le _ _).trans ?_
        refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
        exact add_le_add le_rfl hδ
      have hbound : ‖youngLimit s t - youngStep X Y s t‖ ≤
          (κ + r ^ n * Λ) * (r * ρ) + ρ := by
        calc
          ‖youngLimit s t - youngStep X Y s t‖ ≤
              ‖youngLimit s m - youngStep X Y s m‖ +
                ‖youngLimit m t - youngStep X Y m t‖ + ρ := hthree
          _ ≤ (κ * youngModulus p q X Y s m + r ^ n * Λ * youngModulus p q X Y s m) +
                (κ * youngModulus p q X Y m t + r ^ n * Λ * youngModulus p q X Y m t) + ρ :=
            add_le_add (add_le_add ihL ihR) le_rfl
          _ = (κ + r ^ n * Λ) * (youngModulus p q X Y s m + youngModulus p q X Y m t) + ρ := by
            ring
          _ ≤ (κ + r ^ n * Λ) * (r * ρ) + ρ := add_le_add hmul le_rfl
      have hsew := sewingConstant_shift (by simpa [youngTheta] using hpq)
      have hrκ : κ * r + 1 = κ := by simpa [κ, r, youngTheta] using hsew
      calc
        ‖youngLimit s t - youngStep X Y s t‖ ≤ (κ + r ^ n * Λ) * (r * ρ) + ρ := hbound
        _ = κ * r * ρ + r ^ n * r * Λ * ρ + ρ := by ring
        _ = (κ * r + 1) * ρ + (r ^ n * r) * Λ * ρ := by ring
        _ = κ * ρ + r ^ (n + 1) * Λ * ρ := by rw [← pow_succ, hrκ]

lemma norm_youngLimit_sharp {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
    ‖youngLimit s t - youngStep X Y s t‖ ≤
      sewingConstant (p⁻¹ + q⁻¹) * (pathVariationPower p X s t).toReal ^ p⁻¹ *
        (pathVariationPower q Y s t).toReal ^ q⁻¹ := by
  have hr := Sewing.sewingRatio_mem (by simpa [youngTheta] using hpq)
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr.1 hr.2
  set ρ : ℝ := youngModulus p q X Y s t
  set κ : ℝ := sewingConstant (youngTheta p q)
  set Λ : ℝ := youngLoose (youngTheta p q)
  set r : ℝ := (2 : ℝ) ^ (1 - youngTheta p q)
  have hstep : ∀ n, ‖youngLimit s t - youngStep X Y s t‖ ≤ κ * ρ + r ^ n * Λ * ρ :=
    fun n => norm_defect_iterate hs hst ht n
  have hlim : ‖youngLimit s t - youngStep X Y s t‖ ≤ κ * ρ := by
    have htend : Tendsto (fun n : ℕ => κ * ρ + r ^ n * Λ * ρ) atTop (𝓝 (κ * ρ)) := by
      have hzero : Tendsto (fun n : ℕ => r ^ n * (Λ * ρ)) atTop (𝓝 0) := by
        have hrθ : r = (2 : ℝ) ^ (1 - (p⁻¹ + q⁻¹)) := by simp [r, youngTheta]
        rw [hrθ]
        simpa [zero_mul] using hpow.mul_const (Λ * ρ)
      have hfun : (fun n : ℕ => κ * ρ + r ^ n * Λ * ρ) =
          fun n => κ * ρ + r ^ n * (Λ * ρ) := by
        funext n; ring
      simpa [hfun] using tendsto_const_nhds.add hzero
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds htend hstep
  have hassoc : κ * ρ =
      sewingConstant (p⁻¹ + q⁻¹) * (pathVariationPower p X s t).toReal ^ p⁻¹ *
        (pathVariationPower q Y s t).toReal ^ q⁻¹ := by
    simp [κ, ρ, youngModulus, variationReal, youngTheta, mul_assoc]
  simpa [hassoc] using hlim

lemma youngLimit_seq (n : ℕ) (c : ℕ → ℝ) (hc : Monotone c) (h0 : a ≤ c 0) (hn : c n ≤ b) :
    youngLimit (c 0) (c n) = ∑ i ∈ range n, youngLimit (c i) (c (i + 1)) := by
  induction n with
  | zero =>
    simp
    exact youngLimit_same h0 hn
  | succ n ih =>
    rw [sum_range_succ]
    have hstep : c n ≤ c (n + 1) := hc (Nat.le_succ n)
    have hmid : c 0 ≤ c n := hc (Nat.zero_le n)
    rw [youngLimit_add h0 hmid hstep hn, ih (hstep.trans hn)]

lemma youngLimit_nodes {s t : ℝ} (hs : a ≤ s) (ht : t ≤ b) (π : OrderedIntervalPartition s t) :
    youngLimit s t =
      ∑ i : Fin π.size, youngLimit (π.node i.castSucc) (π.node i.succ) := by
  have hseq := youngLimit_seq π.size (nodeSeq π) (monotone_nodeSeq π)
    (by simpa [nodeSeq_zero] using hs) (by simpa [nodeSeq_size] using ht)
  rw [nodeSeq_zero, nodeSeq_size] at hseq
  have hterm : ∀ i : Fin π.size,
      youngLimit (π.node i.castSucc) (π.node i.succ) =
        youngLimit (nodeSeq π (i : ℕ)) (nodeSeq π ((i : ℕ) + 1)) := by
    intro i
    have hi : (i : ℕ) ≤ π.size := le_of_lt i.isLt
    have hi1 : (i : ℕ) + 1 ≤ π.size := Nat.succ_le_of_lt i.isLt
    have hs' : i.succ = ⟨(i : ℕ) + 1, by omega⟩ := by ext; simp [Fin.val_succ]
    have hc : i.castSucc = ⟨(i : ℕ), by omega⟩ := by ext; simp [Fin.val_castSucc]
    simp [hs', hc, nodeSeq_of_le, hi, hi1]
  rw [Finset.sum_congr rfl fun i _ => hterm i,
    Fin.sum_univ_eq_sum_range
      (fun i => youngLimit (nodeSeq π i) (nodeSeq π (i + 1))) π.size, hseq]

lemma partition_step_le_mesh {s t : ℝ} (π : OrderedIntervalPartition s t) (i : Fin π.size) :
    π.node i.succ - π.node i.castSucc ≤ (π.mesh : ℝ) := by
  have hxy : π.node i.castSucc ≤ π.node i.succ :=
    π.monotone_node (Fin.castSucc_le_succ i)
  have hΔ : 0 ≤ π.node i.succ - π.node i.castSucc := sub_nonneg.mpr hxy
  let fmesh : Fin π.size → ℝ≥0 := fun j =>
    (π.node j.succ - π.node j.castSucc).toNNReal
  have hsup : fmesh i ≤ Finset.univ.sup fmesh := Finset.le_sup (Finset.mem_univ i)
  have hcoe : (fmesh i : ℝ) ≤ (π.mesh : ℝ) := by
    unfold OrderedIntervalPartition.mesh
    exact NNReal.coe_le_coe.mpr hsup
  have hcoe' : (fmesh i : ℝ) = π.node i.succ - π.node i.castSucc := by
    simp [fmesh, Real.coe_toNNReal', max_eq_left hΔ]
  linarith [hcoe, hcoe']

/-- Partition sums approach the additive Young limit once the mesh is small. -/
lemma exists_partition_close {s t : ℝ} (hs : a ≤ s) (_hst : s ≤ t) (ht : t ≤ b) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ π : OrderedIntervalPartition s t, (π.mesh : ℝ) < δ →
      ‖π.incrementSum (youngStep X Y) - youngLimit s t‖ < ε := by
  have hθ : 1 < youngTheta p q := by simpa [youngTheta] using hpq
  have hθ1 : 0 < youngTheta p q - 1 := sub_pos.mpr hθ
  set κ : ℝ := sewingConstant (youngTheta p q)
  set Ω : ℝ := youngCtrl p q X Y s t
  have hκ : 0 ≤ κ := (Sewing.sewingConstant_pos hθ).le
  have hΩ : 0 ≤ Ω := youngCtrl_nonneg X Y s t
  set C : ℝ := κ * Ω
  set τ : ℝ := ε / (2 * (C + 1))
  have hτ : 0 < τ := div_pos hε (mul_pos (by norm_num) (by linarith [mul_nonneg hκ hΩ]))
  set η : ℝ := τ ^ (youngTheta p q - 1)⁻¹
  have hη : 0 < η := Real.rpow_pos_of_pos hτ _
  have hηpow : η ^ (youngTheta p q - 1) = τ := by
    rw [← Real.rpow_mul hτ.le]
    have hinv : (youngTheta p q - 1)⁻¹ * (youngTheta p q - 1) = 1 := by
      field_simp [hθ1.ne']
    rw [hinv, Real.rpow_one]
  have hτle : C * τ ≤ ε / 2 := by
    simp only [τ]
    rw [mul_div, div_le_iff₀ (by linarith [mul_nonneg hκ hΩ] : (0 : ℝ) < 2 * (C + 1))]
    have hclear : ε / 2 * (2 * (C + 1)) = ε * (C + 1) := by ring
    rw [hclear]
    linarith [hε]
  obtain ⟨δ, hδ, hδc⟩ := exists_ctrl_short hp hq hpq X Y hX hY hVp hVq η hη
  refine ⟨δ, hδ, fun π hmesh => ?_⟩
  rw [youngLimit_nodes hs ht π, OrderedIntervalPartition.incrementSum, ← sum_sub_distrib]
  refine lt_of_le_of_lt ((norm_sum_le _ _).trans ?_) (by linarith : ε / 2 < ε)
  have hpiece : ∀ i : Fin π.size,
      ‖youngStep X Y (π.node i.castSucc) (π.node i.succ) -
        youngLimit (π.node i.castSucc) (π.node i.succ)‖ ≤
        κ * η ^ (youngTheta p q - 1) *
          youngCtrl p q X Y (π.node i.castSucc) (π.node i.succ) := by
    intro i
    have hxy : π.node i.castSucc ≤ π.node i.succ :=
      π.monotone_node (Fin.castSucc_le_succ i)
    have hx : a ≤ π.node i.castSucc := by
      have h0 : s ≤ π.node i.castSucc := by
        simpa [π.node_zero] using π.monotone_node (Fin.zero_le i.castSucc)
      exact le_trans hs h0
    have hy : π.node i.succ ≤ b := by
      have hlast : π.node i.succ ≤ π.node (Fin.last π.size) := π.monotone_node (Fin.le_last _)
      exact hlast.trans (by simpa [π.node_last] using ht)
    have hlen : π.node i.succ - π.node i.castSucc < δ :=
      lt_of_le_of_lt (partition_step_le_mesh π i) hmesh
    have hctrl := hδc _ _ hx hxy hy hlen
    have hsharp := norm_youngLimit_sharp hx hxy hy
    rw [norm_sub_rev]
    have hmod : youngModulus p q X Y (π.node i.castSucc) (π.node i.succ) ≤
        η ^ (youngTheta p q - 1) *
          youngCtrl p q X Y (π.node i.castSucc) (π.node i.succ) :=
      youngModulus_le_eta hη.le hctrl
    have hκmod : sewingConstant (p⁻¹ + q⁻¹) *
        (pathVariationPower p X (π.node i.castSucc) (π.node i.succ)).toReal ^ p⁻¹ *
        (pathVariationPower q Y (π.node i.castSucc) (π.node i.succ)).toReal ^ q⁻¹ =
        κ * youngModulus p q X Y (π.node i.castSucc) (π.node i.succ) := by
      simp [κ, youngModulus, variationReal, youngTheta, mul_assoc]
    exact (hsharp.trans (le_of_eq hκmod)).trans
      (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left hmod hκ)
  refine (sum_le_sum fun i _ => hpiece i).trans ?_
  rw [← mul_sum]
  have hmon : Monotone (nodeSeq π) := monotone_nodeSeq π
  have hctrl := ctrl_sum_seq π.size (nodeSeq π) hmon
    (by simpa [nodeSeq_zero] using hs) (by simpa [nodeSeq_size] using ht)
  have hfin : ∑ i : Fin π.size, youngCtrl p q X Y (π.node i.castSucc) (π.node i.succ) ≤ Ω := by
    have hterm : ∀ i : Fin π.size,
        youngCtrl p q X Y (π.node i.castSucc) (π.node i.succ) =
          youngCtrl p q X Y (nodeSeq π (i : ℕ)) (nodeSeq π ((i : ℕ) + 1)) := by
      intro i
      have hi : (i : ℕ) ≤ π.size := le_of_lt i.isLt
      have hi1 : (i : ℕ) + 1 ≤ π.size := Nat.succ_le_of_lt i.isLt
      have hs' : i.succ = ⟨(i : ℕ) + 1, by omega⟩ := by ext; simp [Fin.val_succ]
      have hc : i.castSucc = ⟨(i : ℕ), by omega⟩ := by ext; simp [Fin.val_castSucc]
      simp [hs', hc, nodeSeq_of_le, hi, hi1]
    rw [Finset.sum_congr rfl fun i _ => hterm i,
      Fin.sum_univ_eq_sum_range
        (fun i => youngCtrl p q X Y (nodeSeq π i) (nodeSeq π (i + 1))) π.size]
    simpa [Ω, nodeSeq_zero, nodeSeq_size] using hctrl
  have hC : κ * η ^ (youngTheta p q - 1) * Ω ≤ ε / 2 := by
    calc
      κ * η ^ (youngTheta p q - 1) * Ω = κ * τ * Ω := by rw [hηpow]
      _ = C * τ := by simp only [C]; ring
      _ ≤ ε / 2 := hτle
  exact (mul_le_mul_of_nonneg_left hfin
    (mul_nonneg hκ (Real.rpow_nonneg hη.le _))).trans hC

omit [YoungData E F] in
/-- **09.21**, variation form: the Young integral of complementary finite-variation paths. -/
theorem young_integral {a b p q : ℝ} (hab : a ≤ b) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : 1 < p⁻¹ + q⁻¹) (X : ℝ → E) (Y : ℝ → E →L[ℝ] F)
    (hX : ContinuousOn X (Set.Icc a b)) (hY : ContinuousOn Y (Set.Icc a b))
    (hVp : pathVariationPower p X a b ≠ ∞) (hVq : pathVariationPower q Y a b ≠ ∞) :
    ∃! I : C(Set.Icc a b, F), IsLeftNormalized I ∧
      HasPartitionSumLimit (youngStep X Y) I ∧
      ∀ s t : Set.Icc a b, s.val ≤ t.val →
        ‖(I t - I s) - youngStep X Y s.val t.val‖ ≤
          sewingConstant (p⁻¹ + q⁻¹) *
            (pathVariationPower p X s.val t.val).toReal ^ p⁻¹ *
            (pathVariationPower q Y s.val t.val).toReal ^ q⁻¹ := by
  letI : YoungData E F :=
    ⟨a, b, p, q, hab, hp, hq, hpq, X, Y, hX, hY, hVp, hVq⟩
  let g : Set.Icc a b → ℝ × ℝ := fun x => (a, x.val)
  have hg : Continuous g := continuous_const.prodMk continuous_subtype_val
  have hcomp : Continuous ((fun p : ℝ × ℝ => youngLimit p.1 p.2) ∘ g) :=
    continuousOn_youngLimit.comp_continuous hg fun x => ⟨le_rfl, x.2.1, x.2.2⟩
  have hfun : (fun p : ℝ × ℝ => youngLimit p.1 p.2) ∘ g = fun x => youngLimit a x.val := by
    funext x; rfl
  let I : C(Set.Icc a b, F) := ⟨fun x => youngLimit a x.val, hfun ▸ hcomp⟩
  have hinc : ∀ {s t : Set.Icc a b}, s.val ≤ t.val →
      I t - I s = youngLimit s.val t.val := by
    intro s t hst
    have hadd : youngLimit a t.val = youngLimit a s.val + youngLimit s.val t.val :=
      youngLimit_add le_rfl s.2.1 hst t.2.2
    change youngLimit a t.val - youngLimit a s.val = youngLimit s.val t.val
    rw [hadd]
    abel
  have hleft : IsLeftNormalized I := by
    intro x hx
    change youngLimit a x.val = 0
    rw [hx]
    exact youngLimit_same le_rfl hab
  have hlim : HasPartitionSumLimit (youngStep X Y) I := by
    intro s t hst ε hε
    obtain ⟨δ, hδ, hδπ⟩ := exists_partition_close s.2.1 hst t.2.2 ε hε
    refine ⟨δ, hδ, fun π hmesh => ?_⟩
    rw [hinc hst]
    exact hδπ π hmesh
  refine ⟨I, ⟨⟨hleft, hlim, ?_⟩, ?_⟩⟩
  · intro s t hst
    rw [hinc hst]
    exact norm_youngLimit_sharp s.2.1 hst t.2.2
  · intro J hJ
    apply ContinuousMap.ext
    intro x
    let a0 : Set.Icc a b := ⟨a, ⟨le_rfl, hab⟩⟩
    have hI0 := hleft a0 rfl
    have hJ0 := hJ.1 a0 rfl
    have hEq := Sewing.partitionLimit_unique x.2.1 (hlim a0 x x.2.1) (hJ.2.1 a0 x x.2.1)
    simpa [hI0, hJ0] using hEq.symm

end YoungLoeve

end CKMA
