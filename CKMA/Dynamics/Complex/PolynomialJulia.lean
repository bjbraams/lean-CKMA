/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.Orbit.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Algebra.Polynomial.Derivative

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Polynomial Julia sets and escape rates (46)

The filled Julia set consists of bounded forward polynomial orbits, using the general
bornological `HasBoundedOrbit` interface. Its boundary defines the polynomial Julia set.
The main targets relate repelling cycles, the logarithmic escape-rate limit and
connectedness through finite critical orbits for degree at least two. An attracting
cycle lies in the interior of the filled set for any polynomial.

Derivatives and iteration use Mathlib's conventions. The Mandelbrot set is in
`CKMA.Dynamics.Complex.Mandelbrot` and escaping sets of entire functions in
`CKMA.Dynamics.Complex.EscapingSet`.

## Main definitions

* `CKMA.polynomialFilledJuliaSet`: the filled Julia set of a complex polynomial.
* `CKMA.polynomialJuliaSet`: the polynomial Julia set as the boundary of the filled Julia set.
* `CKMA.repellingComplexPeriodicPoints`: repelling periodic points of a complex map.
* `CKMA.polynomialEscapeRate`: the logarithmic escape-rate function of a polynomial.

## Main results

* `CKMA.closure_repellingComplexPeriodicPoints`: density of repelling periodic points in the
  Julia set (**46.6**).
* `CKMA.closure_repellingComplexPeriodicPoints_subset`: every limit of repelling periodic points
  belongs to the Julia set.
* `CKMA.attractingPeriodicPoint_notMem_polynomialJuliaSet`: an attracting cycle is interior to the
  filled set.
* `CKMA.polynomial_escapeRate_properties`: existence and properties of the Green escape-rate limit.
  Its clauses are also stated separately: `CKMA.tendsto_polynomialEscapeRateApproximation`,
  `CKMA.continuous_polynomialEscapeRate`, `CKMA.polynomialEscapeRate_nonneg`,
  `CKMA.polynomialEscapeRate_eval` and `CKMA.polynomialEscapeRate_eq_zero_iff`.
* `CKMA.polynomialFilledJuliaSet_nonempty_isCompact`: the filled set is nonempty and compact for
  degree at least two.
* `CKMA.isConnected_polynomialFilledJuliaSet_iff`: critical-orbit characterization of connectedness
  (**46.29**).
-/

public section

noncomputable section

namespace CKMA

open Bornology Filter Function Metric Polynomial Set Topology

/-- The filled Julia set of a complex polynomial, by bounded forward iteration. -/
@[expose]
def polynomialFilledJuliaSet (p : ℂ[X]) : Set ℂ :=
  {z | HasBoundedOrbit (fun w ↦ p.eval w) z}

/-- Membership in `polynomialFilledJuliaSet`. -/
theorem mem_polynomialFilledJuliaSet_iff {p : ℂ[X]} {z : ℂ} :
    z ∈ polynomialFilledJuliaSet p ↔ HasBoundedOrbit (fun w ↦ p.eval w) z := Iff.rfl

/-- Filled Julia sets are completely invariant under one polynomial step. -/
theorem eval_mem_polynomialFilledJuliaSet_iff (p : ℂ[X]) (z : ℂ) :
    p.eval z ∈ polynomialFilledJuliaSet p ↔ z ∈ polynomialFilledJuliaSet p := by
  change HasBoundedOrbit (fun w ↦ p.eval w) (p.eval z) ↔
    HasBoundedOrbit (fun w ↦ p.eval w) z
  exact ⟨HasBoundedOrbit.of_map (f := fun w ↦ p.eval w), HasBoundedOrbit.map⟩

/-- The polynomial Julia set as the boundary of its filled set.
Its equality to the nonnormality Julia set is a separate analytic interface. -/
@[expose]
def polynomialJuliaSet (p : ℂ[X]) : Set ℂ := frontier (polynomialFilledJuliaSet p)

/-- Defining equation of `polynomialJuliaSet`. -/
theorem polynomialJuliaSet_def (p : ℂ[X]) :
    polynomialJuliaSet p = frontier (polynomialFilledJuliaSet p) := rfl

/-- A periodic point is repelling when its return multiplier has norm greater than one. -/
@[expose]
def repellingComplexPeriodicPoints (f : ℂ → ℂ) : Set ℂ :=
  {z | ∃ n : ℕ, 0 < n ∧ (f^[n]) z = z ∧ 1 < ‖deriv (f^[n]) z‖}

/-- Membership in `repellingComplexPeriodicPoints`. -/
theorem mem_repellingComplexPeriodicPoints_iff {f : ℂ → ℂ} {z : ℂ} :
    z ∈ repellingComplexPeriodicPoints f ↔
      ∃ n : ℕ, 0 < n ∧ (f^[n]) z = z ∧ 1 < ‖deriv (f^[n]) z‖ := Iff.rfl

/-- An attracting periodic point lies in the interior of the filled Julia set, hence outside
the Julia set. The degree of `p` is not required. -/
theorem attractingPeriodicPoint_notMem_polynomialJuliaSet {p : ℂ[X]} {z : ℂ} {n : ℕ}
    (hn : 0 < n) (hperiod : ((fun w ↦ p.eval w)^[n]) z = z)
    (hattr : ‖deriv ((fun w ↦ p.eval w)^[n]) z‖ < 1) : z ∉ polynomialJuliaSet p := by
  set f : ℂ → ℂ := fun w ↦ p.eval w
  set g : ℂ → ℂ := f^[n]
  have hdiff : ∀ k, Differentiable ℂ (f^[k]) := by
    intro k
    induction k with
    | zero =>
      rw [iterate_zero]
      exact differentiable_id
    | succ k ih =>
      rw [iterate_succ']
      exact p.differentiable.comp ih
  have hder : HasDerivAt g (deriv g z) z := (hdiff n z).hasDerivAt
  obtain ⟨κ, hmul, hκ1⟩ := exists_between hattr
  have hκ0 : 0 ≤ κ := (norm_nonneg (deriv g z)).trans hmul.le
  have hcontr : {y | ‖g y - z‖ ≤ κ * ‖y - z‖} ∈ 𝓝 z := by
    have hlittle := hder.isLittleO.def (sub_pos.mpr hmul)
    rw [hperiod] at hlittle
    filter_upwards [hlittle] with y hy
    simp only [smul_eq_mul] at hy
    calc
      ‖g y - z‖ = ‖(g y - z - (y - z) * deriv g z) + (y - z) * deriv g z‖ := by
        congr 1
        ring
      _ ≤ ‖g y - z - (y - z) * deriv g z‖ + ‖(y - z) * deriv g z‖ :=
        norm_add_le (g y - z - (y - z) * deriv g z) ((y - z) * deriv g z)
      _ ≤ (κ - ‖deriv g z‖) * ‖y - z‖ + ‖deriv g z‖ * ‖y - z‖ := by
        refine add_le_add hy ?_
        rw [norm_mul, mul_comm]
      _ = κ * ‖y - z‖ := by ring
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hcontr
  have hstep : ∀ {y : ℂ}, dist y z < δ → ∀ m, dist ((g^[m]) y) z ≤ κ ^ m * dist y z := by
    intro y hy m
    induction m with
    | zero => simp [iterate_zero, pow_zero, one_mul]
    | succ m ih =>
      have hmem : dist ((g^[m]) y) z < δ := by
        have hpow : κ ^ m ≤ 1 := pow_le_one₀ hκ0 hκ1.le
        calc
          dist ((g^[m]) y) z ≤ κ ^ m * dist y z := ih
          _ ≤ dist y z :=
            le_trans (mul_le_mul_of_nonneg_right hpow dist_nonneg) (by rw [one_mul])
          _ < δ := hy
      have hg : ‖g ((g^[m]) y) - z‖ ≤ κ * ‖(g^[m]) y - z‖ :=
        hball (mem_ball.mpr hmem)
      calc
        dist ((g^[m + 1]) y) z = ‖g ((g^[m]) y) - z‖ := by
          rw [iterate_succ_apply', dist_eq_norm]
        _ ≤ κ * dist ((g^[m]) y) z := by simpa [dist_eq_norm] using hg
        _ ≤ κ * (κ ^ m * dist y z) := by
          exact mul_le_mul_of_nonneg_left ih hκ0
        _ = κ ^ (m + 1) * dist y z := by ring
  have hS : IsBounded (⋃ j ∈ Finset.range n, (f^[j]) '' closedBall z δ) := by
    rw [isBounded_biUnion_finset]
    intro j _hj
    exact ((isCompact_closedBall z δ).image ((p.continuous).iterate j)).isBounded
  have hsub : ball z δ ⊆ polynomialFilledJuliaSet p := by
    intro y hy
    simp only [polynomialFilledJuliaSet, mem_ofPred_eq, hasBoundedOrbit_iff_exists_norm_le]
    obtain ⟨C, hC⟩ := hS.exists_norm_le
    refine ⟨C, fun m => hC _ ?_⟩
    have hdiv : m % n + n * (m / n) = m := Nat.mod_add_div m n
    have hiter : (f^[m]) y = (f^[m % n]) ((g^[m / n]) y) := by
      calc
        (f^[m]) y = (f^[m % n + n * (m / n)]) y := by rw [hdiv]
        _ = (f^[m % n]) ((f^[n * (m / n)]) y) := iterate_add_apply _ _ _ _
        _ = (f^[m % n]) (((f^[n])^[m / n]) y) := by rw [iterate_mul f n (m / n)]
        _ = (f^[m % n]) ((g^[m / n]) y) := rfl
    rw [hiter]
    refine mem_iUnion₂.mpr ⟨m % n, Finset.mem_range.mpr (Nat.mod_lt m hn), ?_⟩
    refine mem_image_of_mem _ ?_
    rw [mem_closedBall]
    have hle := hstep (mem_ball.mp hy) (m / n)
    have hshrink : dist ((g^[m / n]) y) z ≤ dist y z := by
      rw [← one_mul (dist y z)]
      exact le_trans hle (mul_le_mul_of_nonneg_right (pow_le_one₀ hκ0 hκ1.le) dist_nonneg)
    exact hshrink.trans (mem_ball.mp hy).le
  have hint : z ∈ interior (polynomialFilledJuliaSet p) :=
    mem_interior_iff_mem_nhds.mpr (mem_of_superset (ball_mem_nhds z hδ) hsub)
  intro hzJ
  rw [polynomialJuliaSet, frontier, Set.mem_sdiff] at hzJ
  exact hzJ.2 hint

/-- Polynomial escape-rate approximants with the standard `log⁺` normalization.
`Real.log` is applied only to `max 1 ‖·‖`, hence only to arguments at least `1`. -/
@[expose]
def polynomialEscapeRateApproximation (p : ℂ[X]) (z : ℂ) (n : ℕ) : ℝ :=
  (p.natDegree : ℝ)⁻¹ ^ n * Real.log (max 1 ‖((fun w ↦ p.eval w)^[n]) z‖)

/-- Defining equation of `polynomialEscapeRateApproximation`. -/
theorem polynomialEscapeRateApproximation_def (p : ℂ[X]) (z : ℂ) (n : ℕ) :
    polynomialEscapeRateApproximation p z n =
      (p.natDegree : ℝ)⁻¹ ^ n * Real.log (max 1 ‖((fun w ↦ p.eval w)^[n]) z‖) := rfl

/-- The escape-rate function as a totalized limit. Convergence of the approximants is proved
below for `2 ≤ natDegree`; for `natDegree ≤ 1` the value is an unspecified limit. -/
@[expose]
def polynomialEscapeRate (p : ℂ[X]) (z : ℂ) : ℝ :=
  Filter.limUnder atTop (polynomialEscapeRateApproximation p z)

/-- Defining equation of `polynomialEscapeRate`. -/
theorem polynomialEscapeRate_def (p : ℂ[X]) (z : ℂ) :
    polynomialEscapeRate p z = Filter.limUnder atTop (polynomialEscapeRateApproximation p z) :=
  rfl

/-- Escape radius and a uniform bound on the one-step defect `log⁺ ‖p(z)‖ - d log⁺ ‖z‖`.
The radius satisfies `2 / κ ≤ R`. `Real.log` is applied only to arguments at least `1`. -/
private theorem exists_polynomial_escape_data {p : ℂ[X]} (hp : 2 ≤ p.natDegree) :
    ∃ R κ M : ℝ, 1 ≤ R ∧ 0 < κ ∧ 0 ≤ M ∧ κ = ‖p.leadingCoeff‖ / 2 ∧
      (∀ z : ℂ, R ≤ ‖z‖ → κ * ‖z‖ ^ p.natDegree ≤ ‖p.eval z‖) ∧
      (∀ z : ℂ, R ≤ ‖z‖ → 2 * ‖z‖ ≤ ‖p.eval z‖) ∧ 2 / κ ≤ R ∧
      ∀ z : ℂ, |Real.log (max 1 ‖p.eval z‖) -
        (p.natDegree : ℝ) * Real.log (max 1 ‖z‖)| ≤ M := by
  have hp0 : p ≠ 0 := by
    intro h
    simp [h, Polynomial.natDegree_zero] at hp
  set d := p.natDegree
  have hd1 : 1 ≤ d := by omega
  set a := p.leadingCoeff
  have ha0 : a ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
  have ha : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  set S : ℝ := ∑ i ∈ Finset.range d, ‖p.coeff i‖
  set R : ℝ := max 1 (max (2 * S / ‖a‖) (4 / ‖a‖))
  have hR1 : 1 ≤ R := le_max_left _ _
  set κ : ℝ := ‖a‖ / 2
  have hκ : 0 < κ := div_pos ha (by norm_num)
  have hpow : ∀ z : ℂ, R ≤ ‖z‖ → κ * ‖z‖ ^ d ≤ ‖p.eval z‖ := by
    intro z hz
    have hz1 : 1 ≤ ‖z‖ := hR1.trans hz
    set low := ∑ i ∈ Finset.range d, p.coeff i * z ^ i
    set lead := a * z ^ d
    have heval : p.eval z = low + lead := by
      rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ]
      have hcoeff : p.coeff d = a := by
        unfold a Polynomial.leadingCoeff d
        rfl
      rw [hcoeff]
    have hlow : ‖low‖ ≤ S * ‖z‖ ^ (d - 1) := by
      calc
        ‖low‖ ≤ ∑ i ∈ Finset.range d, ‖p.coeff i * z ^ i‖ := norm_sum_le _ _
        _ = ∑ i ∈ Finset.range d, ‖p.coeff i‖ * ‖z‖ ^ i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_mul, norm_pow]
        _ ≤ ∑ i ∈ Finset.range d, ‖p.coeff i‖ * ‖z‖ ^ (d - 1) := by
          refine Finset.sum_le_sum fun i hi => ?_
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hz1 (Nat.le_sub_one_of_lt (Finset.mem_range.mp hi)))
            (norm_nonneg _)
        _ = S * ‖z‖ ^ (d - 1) := by rw [← Finset.sum_mul]
    have hlead : ‖lead‖ = ‖a‖ * ‖z‖ ^ d := by rw [norm_mul, norm_pow]
    have hrev : ‖lead‖ - ‖low‖ ≤ ‖p.eval z‖ := by
      have h := norm_add_le (low + lead) (-low)
      have hsum : low + lead + -low = lead := by ring
      rw [hsum, norm_neg, ← heval] at h
      linarith
    have hSbound : 2 * S / ‖a‖ ≤ ‖z‖ :=
      (le_max_left (2 * S / ‖a‖) (4 / ‖a‖)).trans ((le_max_right 1 _).trans hz)
    have hSle : S ≤ ‖a‖ * ‖z‖ / 2 :=
      (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr <| by
        rw [mul_comm S 2, mul_comm ‖a‖ ‖z‖]
        exact (div_le_iff₀ ha).mp hSbound
    have hpowd : ‖z‖ ^ d = ‖z‖ ^ (d - 1) * ‖z‖ := by
      rw [← Nat.sub_add_cancel hd1]
      exact pow_succ _ _
    have hdiff : κ * ‖z‖ ^ d ≤ ‖a‖ * ‖z‖ ^ d - S * ‖z‖ ^ (d - 1) := by
      have hlin : ‖a‖ * ‖z‖ / 2 ≤ ‖a‖ * ‖z‖ - S := by linarith
      calc
        κ * ‖z‖ ^ d = ‖z‖ ^ (d - 1) * (‖a‖ * ‖z‖ / 2) := by
          rw [hpowd]
          ring
        _ ≤ ‖z‖ ^ (d - 1) * (‖a‖ * ‖z‖ - S) := by
          exact mul_le_mul_of_nonneg_left hlin (pow_nonneg (norm_nonneg _) _)
        _ = ‖a‖ * ‖z‖ ^ d - S * ‖z‖ ^ (d - 1) := by
          rw [hpowd]
          ring
    have : ‖a‖ * ‖z‖ ^ d - S * ‖z‖ ^ (d - 1) ≤ ‖p.eval z‖ := by linarith [hrev, hlow, hlead]
    exact hdiff.trans this
  have hdouble : ∀ z : ℂ, R ≤ ‖z‖ → 2 * ‖z‖ ≤ ‖p.eval z‖ := by
    intro z hz
    have hz1 : 1 ≤ ‖z‖ := hR1.trans hz
    have h4 : 4 / ‖a‖ ≤ ‖z‖ :=
      (le_max_right (2 * S / ‖a‖) (4 / ‖a‖)).trans ((le_max_right 1 _).trans hz)
    have htwo : 2 ≤ κ * ‖z‖ := by
      have hκ4 : κ * (4 / ‖a‖) = 2 := by
        field_simp [ha.ne']
        ring
      exact (le_of_eq hκ4.symm).trans (mul_le_mul_of_nonneg_left h4 hκ.le)
    have hpow1 : ‖z‖ ≤ ‖z‖ ^ (d - 1) := by
      simpa [pow_one] using pow_le_pow_right₀ hz1 (by omega : 1 ≤ d - 1)
    have hbig : 2 ≤ κ * ‖z‖ ^ (d - 1) :=
      le_trans htwo (mul_le_mul_of_nonneg_left hpow1 hκ.le)
    have hscale : 2 * ‖z‖ ≤ κ * ‖z‖ ^ d := by
      have hpowd : ‖z‖ ^ d = ‖z‖ ^ (d - 1) * ‖z‖ := by
        rw [← Nat.sub_add_cancel hd1]
        exact pow_succ _ _
      calc
        2 * ‖z‖ ≤ κ * ‖z‖ ^ (d - 1) * ‖z‖ :=
          mul_le_mul_of_nonneg_right hbig (norm_nonneg _)
        _ = κ * ‖z‖ ^ d := by rw [mul_assoc, ← hpowd]
    exact hscale.trans (hpow z hz)
  set K : ℝ := ∑ i ∈ Finset.range (d + 1), ‖p.coeff i‖
  set C : ℝ := max K 1
  have hC1 : 1 ≤ C := le_max_right _ _
  have hCpos : 0 < C := zero_lt_one.trans_le hC1
  have hnorm_le : ∀ z : ℂ, ‖p.eval z‖ ≤ K * (max 1 ‖z‖) ^ d := by
    intro z
    have ht1 : (1 : ℝ) ≤ max 1 ‖z‖ := le_max_left _ _
    have hzn : ‖z‖ ≤ max 1 ‖z‖ := le_max_right _ _
    calc
      ‖p.eval z‖ = ‖∑ i ∈ Finset.range (d + 1), p.coeff i * z ^ i‖ := by
        rw [Polynomial.eval_eq_sum_range]
      _ ≤ ∑ i ∈ Finset.range (d + 1), ‖p.coeff i * z ^ i‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range (d + 1), ‖p.coeff i‖ * ‖z‖ ^ i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, norm_pow]
      _ ≤ ∑ i ∈ Finset.range (d + 1), ‖p.coeff i‖ * (max 1 ‖z‖) ^ d := by
        refine Finset.sum_le_sum fun i hi => ?_
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact le_trans (pow_le_pow_left₀ (norm_nonneg _) hzn i)
          (pow_le_pow_right₀ ht1 hi')
      _ = K * (max 1 ‖z‖) ^ d := by rw [← Finset.sum_mul]
  let φ : ℂ → ℝ := fun z =>
    Real.log (max 1 ‖p.eval z‖) - (d : ℝ) * Real.log (max 1 ‖z‖)
  have hφ_le : ∀ z, φ z ≤ Real.log C := by
    intro z
    have ht1 : (1 : ℝ) ≤ max 1 ‖z‖ := le_max_left _ _
    have hmax : max 1 ‖p.eval z‖ ≤ C * (max 1 ‖z‖) ^ d := by
      refine max_le ?_ ((hnorm_le z).trans (mul_le_mul_of_nonneg_right (le_max_left K 1)
        (pow_nonneg (le_trans zero_le_one ht1) _)))
      exact hC1.trans (le_mul_of_one_le_right hCpos.le (one_le_pow₀ ht1))
    have hlog := Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hmax
    rw [Real.log_mul hCpos.ne' (pow_ne_zero _ (by positivity)), Real.log_pow] at hlog
    linarith
  have hφ_ge : ∀ z, R ≤ ‖z‖ → Real.log κ ≤ φ z := by
    intro z hz
    have hz1 : 1 ≤ ‖z‖ := hR1.trans hz
    have hp1 : 1 ≤ ‖p.eval z‖ := by
      have h2z : (2 : ℝ) ≤ 2 * ‖z‖ := by nlinarith
      exact le_trans (by norm_num) (h2z.trans (hdouble z hz))
    have harg : 0 < κ * ‖z‖ ^ d := mul_pos hκ (pow_pos (lt_of_lt_of_le zero_lt_one hz1) _)
    have hlog := Real.log_le_log harg (hpow z hz)
    rw [Real.log_mul hκ.ne' (pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one hz1))),
      Real.log_pow] at hlog
    have hmaxz : max (1 : ℝ) ‖z‖ = ‖z‖ := max_eq_right hz1
    have hmaxp : max (1 : ℝ) ‖p.eval z‖ = ‖p.eval z‖ := max_eq_right hp1
    dsimp only [φ]
    rw [hmaxz, hmaxp]
    linarith
  have hlogc : Continuous fun t : ℝ => Real.log (max 1 t) :=
    (Real.continuousOn_log.mono fun t ht =>
      (lt_of_lt_of_le zero_lt_one (mem_Ici.mp ht)).ne').comp_continuous
      (continuous_const.max continuous_id) fun t => le_max_left 1 t
  have hφcont : Continuous φ :=
    (hlogc.comp (continuous_norm.comp p.continuous)).sub
      ((hlogc.comp continuous_norm).const_mul (d : ℝ))
  obtain ⟨r, hr⟩ :=
    ((isCompact_closedBall (0 : ℂ) R).image hφcont).isBounded.subset_closedBall (0 : ℝ)
  have hin : ∀ z, ‖z‖ ≤ R → |φ z| ≤ r := by
    intro z hz
    have hmem : φ z ∈ closedBall (0 : ℝ) r :=
      hr (mem_image_of_mem _ (by rw [mem_closedBall, dist_zero_right]; exact hz))
    simpa [mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hmem
  let M : ℝ := max r (max (Real.log C) |Real.log κ|)
  have hM0 : 0 ≤ M :=
    le_trans (Real.log_nonneg hC1) (le_trans (le_max_left _ _) (le_max_right _ _))
  have hout : ∀ z, R ≤ ‖z‖ → |φ z| ≤ max (Real.log C) |Real.log κ| := by
    intro z hz
    rw [abs_le']
    refine ⟨(hφ_le z).trans (le_max_left _ _), ?_⟩
    have hneg : -(max (Real.log C) |Real.log κ|) ≤ φ z := by
      calc
        -(max (Real.log C) |Real.log κ|) ≤ -|Real.log κ| :=
          neg_le_neg (le_max_right _ _)
        _ ≤ Real.log κ := neg_abs_le _
        _ ≤ φ z := hφ_ge z hz
    linarith
  have h2R : 2 / κ ≤ R := by
    have h4 : 4 / ‖a‖ ≤ R :=
      (le_max_right (2 * S / ‖a‖) (4 / ‖a‖)).trans (le_max_right 1 _)
    have hκeq : 2 / κ = 4 / ‖a‖ := by
      dsimp [κ]
      field_simp [ha.ne']
      ring
    exact (le_of_eq hκeq).trans h4
  refine ⟨R, κ, M, hR1, hκ, hM0, rfl, hpow, hdouble, h2R, ?_⟩
  intro z
  by_cases hz : ‖z‖ ≤ R
  · exact (hin z hz).trans (le_max_left _ _)
  · exact (hout z (le_of_not_ge hz)).trans (le_max_right _ _)

/-- Forward iterates grow at least geometrically outside an escape radius. -/
private theorem norm_iterate_ge_mul_two_pow {p : ℂ[X]} {R : ℝ}
    (hdouble : ∀ z : ℂ, R ≤ ‖z‖ → 2 * ‖z‖ ≤ ‖p.eval z‖) {z : ℂ} (hz : R ≤ ‖z‖) (n : ℕ) :
    2 ^ n * ‖z‖ ≤ ‖((fun w ↦ p.eval w)^[n]) z‖ := by
  induction n with
  | zero => simp [iterate_zero, pow_zero, one_mul]
  | succ n ih =>
    rw [iterate_succ_apply']
    have hbase : R ≤ ‖((fun w ↦ p.eval w)^[n]) z‖ := by
      refine hz.trans ?_
      have hone : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      exact le_trans (le_mul_of_one_le_left (norm_nonneg _) hone) ih
    calc
      2 ^ (n + 1) * ‖z‖ = 2 * (2 ^ n * ‖z‖) := by ring
      _ ≤ 2 * ‖((fun w ↦ p.eval w)^[n]) z‖ :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ ≤ ‖p.eval (((fun w ↦ p.eval w)^[n]) z)‖ := hdouble _ hbase

/-- The Green escape-rate limit exists, is continuous and vanishes precisely on the filled set. -/
theorem polynomial_escapeRate_properties {p : ℂ[X]} (hp : 2 ≤ p.natDegree) :
    (∀ z, Tendsto (polynomialEscapeRateApproximation p z) atTop (𝓝 (polynomialEscapeRate p z))) ∧
      Continuous (polynomialEscapeRate p) ∧
      (∀ z, 0 ≤ polynomialEscapeRate p z) ∧
      (∀ z, polynomialEscapeRate p (p.eval z) = p.natDegree * polynomialEscapeRate p z) ∧
      ∀ z, polynomialEscapeRate p z = 0 ↔ z ∈ polynomialFilledJuliaSet p := by
  obtain ⟨R, κ, M, hR1, hκ, hM0, -, hpow, hdouble, h2R, hdefect⟩ :=
    exists_polynomial_escape_data hp
  set d := p.natDegree
  set ρ : ℝ := (d : ℝ)⁻¹
  set f : ℂ → ℂ := fun w ↦ p.eval w
  set u : ℂ → ℕ → ℝ := fun z n ↦ polynomialEscapeRateApproximation p z n
  have hdposℝ : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hρ0 : 0 < ρ := inv_pos.mpr hdposℝ
  have hρ1 : ρ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < d))
  have hDρ : (d : ℝ) * ρ = 1 := mul_inv_cancel₀ hdposℝ.ne'
  have hD1 : (d : ℝ) - 1 ≠ 0 :=
    (sub_pos.mpr (by exact_mod_cast (by omega : 1 < d))).ne.symm
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hp
  have hcoef : ∀ n, (d : ℝ) * ρ ^ (n + 1) = ρ ^ n := by
    intro n
    calc
      (d : ℝ) * ρ ^ (n + 1) = (d : ℝ) * (ρ ^ n * ρ) := by rw [pow_succ]
      _ = (d : ℝ) * (ρ * ρ ^ n) := by rw [mul_comm (ρ ^ n) ρ]
      _ = ((d : ℝ) * ρ) * ρ ^ n := by rw [← mul_assoc]
      _ = 1 * ρ ^ n := by rw [hDρ]
      _ = ρ ^ n := by rw [one_mul]
  have hstep : ∀ z n, dist (u z n) (u z (n + 1)) ≤ M * ρ ^ (n + 1) := by
    intro z n
    set w := (f^[n]) z
    have hdiff : u z (n + 1) - u z n =
        ρ ^ (n + 1) * (Real.log (max 1 ‖p.eval w‖) -
          (d : ℝ) * Real.log (max 1 ‖w‖)) := by
      have hiter : (f^[n]) (f z) = p.eval w := by
        rw [← iterate_succ_apply f, iterate_succ_apply']
      dsimp [u, polynomialEscapeRateApproximation]
      rw [hiter, ← hcoef n]
      ring
    rw [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm, hdiff, abs_mul,
      abs_of_nonneg (pow_nonneg hρ0.le _)]
    refine le_trans (mul_le_mul_of_nonneg_left (hdefect w) (pow_nonneg hρ0.le _)) ?_
    exact le_of_eq (mul_comm _ _)
  have hsum : Summable fun n ↦ M * ρ ^ (n + 1) :=
    ((summable_geometric_of_lt_one hρ0.le hρ1).comp_injective Nat.succ_injective).mul_left M
  have hcauchy : ∀ z, CauchySeq (u z) := fun z ↦
    cauchySeq_of_dist_le_of_summable (fun n ↦ M * ρ ^ (n + 1)) (hstep z) hsum
  have htendsto : ∀ z, Tendsto (u z) atTop (𝓝 (polynomialEscapeRate p z)) := by
    intro z
    simpa [polynomialEscapeRate, u] using (hcauchy z).tendsto_limUnder
  have happrox_nonneg : ∀ z n, 0 ≤ u z n := by
    intro z n
    dsimp [u, polynomialEscapeRateApproximation]
    exact mul_nonneg (pow_nonneg hρ0.le _) (Real.log_nonneg (le_max_left _ _))
  have hG0 : ∀ z, 0 ≤ polynomialEscapeRate p z := by
    intro z
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds (htendsto z) (happrox_nonneg z)
  have htsum : ∀ n, ∑' m : ℕ, M * ρ ^ (n + m + 1) =
      M * ρ ^ (n + 1) * (1 - ρ)⁻¹ := by
    intro n
    have hrewrite : ∀ m, M * ρ ^ (n + m + 1) = (M * ρ ^ (n + 1)) * ρ ^ m := by
      intro m
      have hidx : n + m + 1 = n + 1 + m := by omega
      rw [hidx, pow_add]
      ring
    rw [tsum_congr hrewrite, tsum_mul_left, tsum_geometric_of_lt_one hρ0.le hρ1]
  have htail : ∀ z n, dist (u z n) (polynomialEscapeRate p z) ≤
      ∑' m : ℕ, M * ρ ^ (n + m + 1) := fun z n ↦
    dist_le_tsum_of_dist_le_of_tendsto (fun k ↦ M * ρ ^ (k + 1)) (hstep z) hsum
      (htendsto z) n
  have hlogc : Continuous fun t : ℝ ↦ Real.log (max 1 t) :=
    (Real.continuousOn_log.mono fun t ht ↦
      (lt_of_lt_of_le zero_lt_one (mem_Ici.mp ht)).ne').comp_continuous
      (continuous_const.max continuous_id) fun t ↦ le_max_left 1 t
  have hucont : ∀ n, Continuous fun z ↦ u z n := by
    intro n
    dsimp [u, polynomialEscapeRateApproximation]
    exact (hlogc.comp (continuous_norm.comp ((p.continuous).iterate n))).const_mul (ρ ^ n)
  have hbound_tend :
      Tendsto (fun n : ℕ ↦ M * ρ ^ (n + 1) * (1 - ρ)⁻¹) atTop (𝓝 0) := by
    have hpow : Tendsto (fun n : ℕ ↦ ρ ^ (n + 1)) atTop (𝓝 0) := by
      refine ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).comp
        (tendsto_add_atTop_nat 1)).congr fun n ↦ ?_
      rw [Function.comp_apply]
    have hmul := hpow.const_mul (M * (1 - ρ)⁻¹)
    rw [mul_zero] at hmul
    exact hmul.congr fun n ↦ by ring
  have hcont : Continuous (polynomialEscapeRate p) := by
    refine continuous_of_uniform_approx_of_continuous fun s hs ↦ ?_
    obtain ⟨ε, hε, hsε⟩ := mem_uniformity_dist.mp hs
    obtain ⟨n, hn⟩ := (hbound_tend.eventually (ball_mem_nhds (0 : ℝ) hε)).exists
    refine ⟨fun z ↦ u z n, hucont n, fun y ↦ ?_⟩
    have hb : 0 ≤ M * ρ ^ (n + 1) * (1 - ρ)⁻¹ :=
      mul_nonneg (mul_nonneg hM0 (pow_nonneg hρ0.le _))
        (inv_nonneg.mpr (sub_nonneg.mpr hρ1.le))
    have hlt : M * ρ ^ (n + 1) * (1 - ρ)⁻¹ < ε := by
      rw [dist_eq_norm, Real.norm_eq_abs, sub_zero, abs_of_nonneg hb] at hn
      exact hn
    have hle : dist (u y n) (polynomialEscapeRate p y) ≤
        M * ρ ^ (n + 1) * (1 - ρ)⁻¹ := by
      rw [← htsum n]
      exact htail y n
    exact hsε <| by
      rw [dist_comm]
      exact lt_of_le_of_lt hle hlt
  have hfun_approx : ∀ z n, u (p.eval z) n = (d : ℝ) * u z (n + 1) := by
    intro z n
    have hiter : (f^[n]) (f z) = (f^[n + 1]) z := by
      rw [← iterate_succ_apply f]
    dsimp [u, polynomialEscapeRateApproximation]
    rw [hiter, ← hcoef n]
    ring
  have hfun : ∀ z, polynomialEscapeRate p (p.eval z) =
      (d : ℝ) * polynomialEscapeRate p z := by
    intro z
    have hshift := (htendsto z).comp (tendsto_add_atTop_nat 1)
    have hmul := hshift.const_mul (d : ℝ)
    exact tendsto_nhds_unique (htendsto (p.eval z))
      (hmul.congr fun n ↦ (hfun_approx z n).symm)
  have hpos_out : ∀ z, R ≤ ‖z‖ → 0 < polynomialEscapeRate p z := by
    intro z hz
    have hnorm_ge : ∀ m, R ≤ ‖(f^[m]) z‖ := by
      intro m
      have hone : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
      calc
        R ≤ ‖z‖ := hz
        _ ≤ 2 ^ m * ‖z‖ := le_mul_of_one_le_left (norm_nonneg _) hone
        _ ≤ ‖(f^[m]) z‖ := norm_iterate_ge_mul_two_pow hdouble hz m
    let bound (m : ℕ) : ℝ :=
      (d : ℝ) ^ m * Real.log ‖z‖ +
        ((d : ℝ) ^ m - 1) / ((d : ℝ) - 1) * Real.log κ
    have hlog_iter : ∀ m, bound m ≤ Real.log ‖(f^[m]) z‖ := by
      intro m
      induction m with
      | zero =>
        dsimp [bound]
        rw [pow_zero, sub_self, zero_div, zero_mul, add_zero, one_mul]
      | succ m ih =>
        dsimp [bound] at ih ⊢
        set w := (f^[m]) z
        have hposw : 0 < ‖w‖ := lt_of_lt_of_le zero_lt_one (hR1.trans (hnorm_ge m))
        have harg : 0 < κ * ‖w‖ ^ d := mul_pos hκ (pow_pos hposw _)
        have hlogp : Real.log κ + (d : ℝ) * Real.log ‖w‖ ≤ Real.log ‖p.eval w‖ := by
          have hlog := Real.log_le_log harg (hpow w (hnorm_ge m))
          rw [Real.log_mul hκ.ne' (pow_ne_zero _ hposw.ne'), Real.log_pow] at hlog
          exact hlog
        have hnext : (f^[m + 1]) z = p.eval w := by
          rw [iterate_succ_apply']
        have hcoeff : ((d : ℝ) ^ (m + 1) - 1) / ((d : ℝ) - 1) =
            1 + (d : ℝ) * (((d : ℝ) ^ m - 1) / ((d : ℝ) - 1)) := by
          field_simp [hD1]
          ring
        calc
          (d : ℝ) ^ (m + 1) * Real.log ‖z‖ +
              ((d : ℝ) ^ (m + 1) - 1) / ((d : ℝ) - 1) * Real.log κ =
              (d : ℝ) ^ (m + 1) * Real.log ‖z‖ +
                (1 + (d : ℝ) * (((d : ℝ) ^ m - 1) / ((d : ℝ) - 1))) * Real.log κ := by
                  rw [hcoeff]
          _ = Real.log κ + (d : ℝ) * ((d : ℝ) ^ m * Real.log ‖z‖ +
                ((d : ℝ) ^ m - 1) / ((d : ℝ) - 1) * Real.log κ) := by ring
          _ ≤ Real.log κ + (d : ℝ) * Real.log ‖w‖ := by
              exact add_le_add_right
                (mul_le_mul_of_nonneg_left ih (le_trans (by norm_num) hdR))
                (Real.log κ)
          _ ≤ Real.log ‖p.eval w‖ := hlogp
          _ = Real.log ‖(f^[m + 1]) z‖ := by rw [hnext]
    let lower (m : ℕ) : ℝ :=
      Real.log ‖z‖ + (1 - ρ ^ m) / ((d : ℝ) - 1) * Real.log κ
    have hlower : ∀ m, lower m ≤ u z m := by
      intro m
      have hpow1 : ρ ^ m * (d : ℝ) ^ m = 1 := by
        rw [← mul_pow, mul_comm ρ (d : ℝ), hDρ, one_pow]
      have hsub : ρ ^ m * ((d : ℝ) ^ m - 1) = 1 - ρ ^ m := by
        rw [mul_sub, hpow1, mul_one]
      have hrewrite : ρ ^ m * bound m = lower m := by
        dsimp [bound, lower]
        calc
          ρ ^ m * ((d : ℝ) ^ m * Real.log ‖z‖ +
              ((d : ℝ) ^ m - 1) / ((d : ℝ) - 1) * Real.log κ) =
              ρ ^ m * (d : ℝ) ^ m * Real.log ‖z‖ +
                ρ ^ m * (((d : ℝ) ^ m - 1) / ((d : ℝ) - 1)) * Real.log κ := by ring
          _ = Real.log ‖z‖ +
                (ρ ^ m * ((d : ℝ) ^ m - 1) / ((d : ℝ) - 1)) * Real.log κ := by
                  rw [hpow1]
                  ring
          _ = Real.log ‖z‖ + ((1 - ρ ^ m) / ((d : ℝ) - 1)) * Real.log κ := by rw [hsub]
      have hmax : max (1 : ℝ) ‖(f^[m]) z‖ = ‖(f^[m]) z‖ :=
        max_eq_right (hR1.trans (hnorm_ge m))
      have hmul := mul_le_mul_of_nonneg_left (hlog_iter m) (pow_nonneg hρ0.le m)
      dsimp [u, polynomialEscapeRateApproximation]
      rw [hmax, ← hrewrite]
      exact hmul
    let L : ℝ := Real.log ‖z‖ + Real.log κ / ((d : ℝ) - 1)
    have htendL : Tendsto lower atTop (𝓝 L) := by
      have hρm := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1
      have hsub : Tendsto (fun n ↦ (1 : ℝ) - ρ ^ n) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub hρm
      have hdiv := hsub.mul_const ((d : ℝ) - 1)⁻¹
      have hmul := hdiv.mul_const (Real.log κ)
      have hraw := hmul.const_add (Real.log ‖z‖)
      have hfunL : ∀ m, lower m =
          Real.log ‖z‖ + (1 - ρ ^ m) * ((d : ℝ) - 1)⁻¹ * Real.log κ := by
        intro m
        dsimp [lower]
        ring
      have hlim : L = Real.log ‖z‖ + (1 - 0) * ((d : ℝ) - 1)⁻¹ * Real.log κ := by
        dsimp [L]
        ring
      rw [hlim]
      exact hraw.congr fun m ↦ (hfunL m).symm
    have hLle : L ≤ polynomialEscapeRate p z :=
      le_of_tendsto_of_tendsto' htendL (htendsto z) hlower
    have hLpos : 0 < L := by
      by_cases hlogκ : Real.log κ ≤ 0
      · have htwo_pos : (0 : ℝ) < 2 / κ := div_pos (by norm_num) hκ
        have hlog_le : Real.log (2 / κ) ≤ Real.log ‖z‖ :=
          Real.log_le_log htwo_pos (h2R.trans hz)
        have hsplit : Real.log (2 / κ) = Real.log 2 - Real.log κ :=
          Real.log_div (by norm_num) hκ.ne'
        have halg : Real.log (2 / κ) + Real.log κ / ((d : ℝ) - 1) =
            Real.log 2 + Real.log κ * ((2 - (d : ℝ)) / ((d : ℝ) - 1)) := by
          rw [hsplit]
          field_simp [hD1]
          ring
        have hprod : 0 ≤ Real.log κ * ((2 - (d : ℝ)) / ((d : ℝ) - 1)) :=
          mul_nonneg_of_nonpos_of_nonpos hlogκ (div_nonpos_iff.mpr
            (Or.inr ⟨by linarith [hdR], by linarith [hdR]⟩))
        have hcmp : Real.log (2 / κ) + Real.log κ / ((d : ℝ) - 1) ≤ L := by
          dsimp [L]
          linarith [hlog_le]
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hge : Real.log 2 ≤ L := by
          calc
            Real.log 2 ≤ Real.log 2 +
                Real.log κ * ((2 - (d : ℝ)) / ((d : ℝ) - 1)) := by linarith [hprod]
            _ = Real.log (2 / κ) + Real.log κ / ((d : ℝ) - 1) := by rw [← halg]
            _ ≤ L := hcmp
        exact lt_of_lt_of_le hlog2 hge
      · have hlogκ' : 0 < Real.log κ := lt_of_not_ge hlogκ
        have hlogz : 0 ≤ Real.log ‖z‖ := Real.log_nonneg (hR1.trans hz)
        have hquot : 0 < Real.log κ / ((d : ℝ) - 1) :=
          div_pos hlogκ' (sub_pos.mpr (by exact_mod_cast (by omega : 1 < d)))
        dsimp [L]
        exact add_pos_of_nonneg_of_pos hlogz hquot
    exact lt_of_lt_of_le hLpos hLle
  have hscale : ∀ k z, polynomialEscapeRate p ((f^[k]) z) =
      (d : ℝ) ^ k * polynomialEscapeRate p z := by
    intro k
    induction k with
    | zero =>
      intro z
      rw [iterate_zero, pow_zero, one_mul]
      exact rfl
    | succ k ih =>
      intro z
      rw [iterate_succ_apply', hfun ((f^[k]) z), ih z, pow_succ]
      ring
  refine ⟨fun z ↦ by simpa [u] using htendsto z, hcont, hG0, ?_, ?_⟩
  · intro z
    exact hfun z
  · intro z
    constructor
    · intro hzero
      by_contra hz
      simp only [polynomialFilledJuliaSet, mem_ofPred_eq,
        hasBoundedOrbit_iff_exists_norm_le] at hz
      push Not at hz
      obtain ⟨n, hn⟩ := hz R
      have hnlt : R < ‖(f^[n]) z‖ := by simpa using hn
      have hpos := hpos_out _ hnlt.le
      rw [hscale n z, hzero, mul_zero] at hpos
      exact lt_irrefl (0 : ℝ) hpos
    · intro hz
      simp only [polynomialFilledJuliaSet, mem_ofPred_eq,
        hasBoundedOrbit_iff_exists_norm_le] at hz
      obtain ⟨B, hB⟩ := hz
      have hupper : ∀ n, u z n ≤ ρ ^ n * Real.log (max 1 B) := by
        intro n
        dsimp [u, polynomialEscapeRateApproximation]
        have hmax : max 1 ‖(f^[n]) z‖ ≤ max 1 B := max_le_max le_rfl (hB n)
        have hlog := Real.log_le_log
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hmax
        exact mul_le_mul_of_nonneg_left hlog (pow_nonneg hρ0.le _)
      have hupper_tend :
          Tendsto (fun n ↦ ρ ^ n * Real.log (max 1 B)) atTop (𝓝 0) := by
        have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1
        have hmul := hpow.mul_const (Real.log (max 1 B))
        simpa [zero_mul] using hmul
      have hto0 : Tendsto (u z) atTop (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper_tend
          (happrox_nonneg z) hupper
      exact (tendsto_nhds_unique hto0 (htendsto z)).symm

/-- The filled Julia set is nonempty and compact for a polynomial of degree at least two. -/
theorem polynomialFilledJuliaSet_nonempty_isCompact {p : ℂ[X]} (hp : 2 ≤ p.natDegree) :
    (polynomialFilledJuliaSet p).Nonempty ∧ IsCompact (polynomialFilledJuliaSet p) := by
  obtain ⟨R, -, -, hR1, -, -, -, -, hdouble, -, -⟩ := exists_polynomial_escape_data hp
  set f : ℂ → ℂ := fun w ↦ p.eval w
  have hnonempty : (polynomialFilledJuliaSet p).Nonempty := by
    have hlt : natDegree (-(X : ℂ[X])) < p.natDegree := by
      rw [Polynomial.natDegree_neg, Polynomial.natDegree_X]
      omega
    have hdeg : 0 < (p - X).natDegree := by
      rw [sub_eq_add_neg, Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt]
      omega
    obtain ⟨z, hz⟩ := Complex.exists_root (Polynomial.natDegree_pos_iff_degree_pos.mp hdeg)
    have hzfix : p.eval z = z := by
      have hz0 : (p - X).eval z = 0 := Polynomial.IsRoot.eq_zero hz
      rw [Polynomial.eval_sub, Polynomial.eval_X] at hz0
      exact sub_eq_zero.mp hz0
    refine ⟨z, ?_⟩
    simp only [polynomialFilledJuliaSet, mem_ofPred_eq, hasBoundedOrbit_iff_exists_norm_le]
    refine ⟨‖z‖, fun n => ?_⟩
    rw [iterate_fixed hzfix]
  refine ⟨hnonempty, ?_⟩
  rw [isCompact_iff_isClosed_bounded]
  refine ⟨?_, ?_⟩
  · rw [← isOpen_compl_iff]
    refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    simp only [mem_compl_iff, polynomialFilledJuliaSet, mem_ofPred_eq,
      hasBoundedOrbit_iff_exists_norm_le] at hz
    push Not at hz
    obtain ⟨n, hn⟩ := hz R
    have hnlt : R < ‖(f^[n]) z‖ := by simpa using hn
    have hopen : IsOpen {w | R < ‖(f^[n]) w‖} :=
      isOpen_lt continuous_const (continuous_norm.comp ((p.continuous).iterate n))
    refine mem_of_superset (hopen.mem_nhds hnlt) ?_
    intro w hw
    simp only [mem_compl_iff, polynomialFilledJuliaSet, mem_ofPred_eq,
      hasBoundedOrbit_iff_exists_norm_le]
    push Not
    intro B
    have hstart : R ≤ ‖(f^[n]) w‖ := hw.le
    have hnormpos : 0 < ‖(f^[n]) w‖ := lt_trans zero_lt_one (lt_of_le_of_lt hR1 hw)
    obtain ⟨k, hk⟩ :=
      ((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).atTop_mul_const' hnormpos
        |>.eventually_gt_atTop B).exists
    have hge := norm_iterate_ge_mul_two_pow hdouble hstart k
    rw [← iterate_add_apply f k n w] at hge
    exact ⟨k + n, lt_of_lt_of_le hk hge⟩
  · refine (isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset ?_
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    by_contra hgt
    have hgt' : R < ‖z‖ := not_le.mp hgt
    simp only [polynomialFilledJuliaSet, mem_ofPred_eq, hasBoundedOrbit_iff_exists_norm_le] at hz
    obtain ⟨B, hB⟩ := hz
    have hnormpos : 0 < ‖z‖ := lt_trans zero_lt_one (lt_of_le_of_lt hR1 hgt')
    obtain ⟨n, hn⟩ :=
      ((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).atTop_mul_const' hnormpos
        |>.eventually_gt_atTop B).exists
    exact (not_le.mpr (lt_of_lt_of_le hn (norm_iterate_ge_mul_two_pow hdouble hgt'.le n))) (hB n)

/-- The escape-rate approximants converge to `polynomialEscapeRate` in degree at least two. -/
theorem tendsto_polynomialEscapeRateApproximation {p : ℂ[X]} (hp : 2 ≤ p.natDegree) (z : ℂ) :
    Tendsto (polynomialEscapeRateApproximation p z) atTop (𝓝 (polynomialEscapeRate p z)) :=
  (polynomial_escapeRate_properties hp).1 z

/-- The escape rate is continuous in degree at least two. -/
theorem continuous_polynomialEscapeRate {p : ℂ[X]} (hp : 2 ≤ p.natDegree) :
    Continuous (polynomialEscapeRate p) :=
  (polynomial_escapeRate_properties hp).2.1

/-- The escape rate is nonnegative in degree at least two. -/
theorem polynomialEscapeRate_nonneg {p : ℂ[X]} (hp : 2 ≤ p.natDegree) (z : ℂ) :
    0 ≤ polynomialEscapeRate p z :=
  (polynomial_escapeRate_properties hp).2.2.1 z

/-- The escape rate multiplies by the degree under one application of `p`. -/
theorem polynomialEscapeRate_eval {p : ℂ[X]} (hp : 2 ≤ p.natDegree) (z : ℂ) :
    polynomialEscapeRate p (p.eval z) = p.natDegree * polynomialEscapeRate p z :=
  (polynomial_escapeRate_properties hp).2.2.2.1 z

/-- The escape rate vanishes exactly on the filled Julia set. -/
theorem polynomialEscapeRate_eq_zero_iff {p : ℂ[X]} (hp : 2 ≤ p.natDegree) (z : ℂ) :
    polynomialEscapeRate p z = 0 ↔ z ∈ polynomialFilledJuliaSet p :=
  (polynomial_escapeRate_properties hp).2.2.2.2 z

/-- The filled Julia set is nonempty in degree at least two. -/
theorem polynomialFilledJuliaSet_nonempty {p : ℂ[X]} (hp : 2 ≤ p.natDegree) :
    (polynomialFilledJuliaSet p).Nonempty :=
  (polynomialFilledJuliaSet_nonempty_isCompact hp).1

/-- The filled Julia set is compact in degree at least two. -/
theorem isCompact_polynomialFilledJuliaSet {p : ℂ[X]} (hp : 2 ≤ p.natDegree) :
    IsCompact (polynomialFilledJuliaSet p) :=
  (polynomialFilledJuliaSet_nonempty_isCompact hp).2

/-- Limits of repelling periodic points lie in the Julia set. -/
theorem closure_repellingComplexPeriodicPoints_subset {p : ℂ[X]} (hp : 2 ≤ p.natDegree) :
    closure (repellingComplexPeriodicPoints (fun z ↦ p.eval z)) ⊆ polynomialJuliaSet p := by
  set f : ℂ → ℂ := fun w ↦ p.eval w
  have hK := (polynomialFilledJuliaSet_nonempty_isCompact hp).2
  obtain ⟨B, hB⟩ := hK.isBounded.exists_norm_le
  refine closure_minimal (fun z hz ↦ ?_) isClosed_frontier
  obtain ⟨n, hn, hfix, hrep⟩ := hz
  have hzK : z ∈ polynomialFilledJuliaSet p := by
    refine (hasBoundedOrbit_iff_exists_norm_le f z).mpr ⟨
      ∑ j ∈ Finset.range n, ‖(f^[j]) z‖, fun m ↦ ?_⟩
    have hre : (f^[m]) z = (f^[m % n]) z := by
      conv_lhs => rw [← Nat.mod_add_div m n, iterate_add_apply, iterate_mul, iterate_fixed hfix]
    rw [hre]
    exact Finset.single_le_sum (fun j _ ↦ norm_nonneg ((f^[j]) z))
      (Finset.mem_range.mpr (Nat.mod_lt m hn))
  rw [polynomialJuliaSet, hK.isClosed.frontier_eq]
  refine ⟨hzK, fun hint ↦ ?_⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
  set g : ℂ → ℂ := f^[n]
  have hd : Differentiable ℂ g := p.differentiable.iterate n
  have hbound (k : ℕ) : ‖deriv g z‖ ^ k ≤ B / (r / 2) := by
    rw [← norm_pow, ← (HasDerivAt.iterate z (hd z).hasDerivAt hfix k).deriv]
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (half_pos hr)
      (hd.iterate k).diffContOnCl (fun w hw ↦ hB _ ?_)
    have hwK : w ∈ polynomialFilledJuliaSet p :=
      hball (mem_ball.mpr ((mem_sphere.mp hw).trans_lt (half_lt_self hr)))
    have hstep (m : ℕ) : (f^[m]) w ∈ polynomialFilledJuliaSet p := by
      induction m with
      | zero => exact hwK
      | succ m ih =>
        rw [iterate_succ_apply']
        exact (eval_mem_polynomialFilledJuliaSet_iff p _).mpr ih
    rw [← iterate_mul]
    exact hstep (n * k)
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hrep).eventually_gt_atTop
    (B / (r / 2))).exists
  exact hk.not_ge (hbound k)

/-- **46.6**, polynomial scope: repelling periodic points are dense in the polynomial Julia set. -/
theorem closure_repellingComplexPeriodicPoints {p : ℂ[X]} (hp : 2 ≤ p.natDegree) :
    closure (repellingComplexPeriodicPoints (fun z ↦ p.eval z)) = polynomialJuliaSet p := by
  refine Subset.antisymm (closure_repellingComplexPeriodicPoints_subset hp) ?_
  sorry

/-- **46.29**: polynomial connectedness is equivalent to boundedness of every finite critical orbit.
  -/
theorem isConnected_polynomialFilledJuliaSet_iff {p : ℂ[X]} (hp : 2 ≤ p.natDegree) :
    (IsConnected (polynomialFilledJuliaSet p) ↔
      ∀ z : ℂ, p.derivative.eval z = 0 → z ∈ polynomialFilledJuliaSet p) ∧
    (IsConnected (polynomialJuliaSet p) ↔ IsConnected (polynomialFilledJuliaSet p)) := by
  sorry

end CKMA
