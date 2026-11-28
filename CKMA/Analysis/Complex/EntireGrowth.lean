/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import CKMA.Analysis.Complex.EntireGrowth.Product
public import TauCeti.Analysis.Complex.GrowthOrder

import CKMA.Analysis.Complex.EntireGrowth.Factor
import CKMA.Analysis.Complex.EntireGrowth.Removal

/-!
# Entire growth, canonical products and value uniqueness

Maximum modulus and extended logarithmic indicators measure entire-function growth.
Hadamard factorization uses fixed-genus canonical products with normal convergence.
Cartwright functions have radial zero density and concentration near the real axis.
Logarithmic-derivative estimates permit an exceptional set of finite linear measure;
four shared finite values determine a nonconstant entire function.

Sources: GAPS 41.10, 41.26, 41.38 and 41.48.

## Main definitions

* `CKMA.maximumModulus`, `CKMA.entireGrowthOrder`: maximum modulus on circles and order of growth.
* `CKMA.IsEntireExponentialType`: entire functions of finite exponential type.
* `CKMA.fixedGenusCanonicalProduct`: the Weierstrass canonical product of fixed genus over an
  `Option`-valued zero list, built from `CKMA.genusFactor`.
* `CKMA.entireIndicator`: Phragmén–Lindelöf indicator function.
* `CKMA.IsCartwrightFunction`, `CKMA.entireZeroCountingMeasure`: Cartwright class and zero-counting
  measure.

## Main results

* `CKMA.orderLE_of_entireGrowthOrder_le`: a bound on `entireGrowthOrder` is an order bound in the
  sense of `TauCeti.OrderLE`.
* `CKMA.hadamard_factorization`: Hadamard's factorization theorem for finite-order entire functions.
* `CKMA.cartwright_zero_distribution`: Cartwright's theorem on zero distribution.
* `CKMA.logarithmic_derivative_estimate`: Nevanlinna's lemma on the logarithmic derivative.
* `CKMA.four_value_entire`: Nevanlinna's four-value theorem for entire functions.
-/

public section

noncomputable section

namespace CKMA

open Filter Topology MeasureTheory Polynomial
open scoped BigOperators ENNReal

/-- Maximum modulus on the circle of radius `r`, as a real supremum.
`sSup` of the empty set is `0`, and `sSup` of a set that is not bounded above is `0`. -/
@[expose]
def maximumModulus (f : ℂ → ℂ) (r : ℝ) : ℝ := sSup ((fun z ↦ ‖f z‖) '' Metric.sphere 0 r)

/-- Entire-function order, retaining the possibility of infinite order.
The `max e` cutoff gives the usual order zero for constants and does not affect growth order. -/
@[expose]
def entireGrowthOrder (f : ℂ → ℂ) : EReal :=
  limsup (fun r : ℝ ↦ ((Real.log (Real.log (max (Real.exp 1) (maximumModulus f r))) /
    Real.log r : ℝ) : EReal)) atTop

/-- Exponential type at most `σ`, allowing an arbitrarily small increase in the exponent. -/
@[expose]
def IsEntireExponentialType (f : ℂ → ℂ) (σ : ℝ) : Prop :=
  Differentiable ℂ f ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp ((σ + ε) * ‖z‖)

/-- The canonical product of fixed genus `∏ E_p(z / w)` over a zero list, evaluated pointwise.
Its convergence is asserted explicitly in factorization targets, so the totalized infinite product
is not mistaken for a proof. -/
@[expose]
def fixedGenusCanonicalProduct (p : ℕ) (a : ℕ → Option ℂ) (z : ℂ) : ℂ :=
  ∏' n : ℕ, genusFactor p a n z

/-- The canonical product is the infinite product of the genus factors. -/
theorem fixedGenusCanonicalProduct_def (p : ℕ) (a : ℕ → Option ℂ) (z : ℂ) :
    fixedGenusCanonicalProduct p a z = ∏' n : ℕ, genusFactor p a n z :=
  rfl

/-- The maximum modulus is the supremum of `‖f‖` over the circle of radius `r`. -/
theorem maximumModulus_def (f : ℂ → ℂ) (r : ℝ) :
    maximumModulus f r = sSup ((fun z ↦ ‖f z‖) '' Metric.sphere 0 r) :=
  rfl

/-- For a continuous `f`, the modulus at a point is at most the maximum modulus on its circle. -/
theorem norm_le_maximumModulus {f : ℂ → ℂ} (hf : Continuous f) (z : ℂ) :
    ‖f z‖ ≤ maximumModulus f ‖z‖ :=
  le_csSup ((isCompact_sphere (0 : ℂ) ‖z‖).bddAbove_image
    (continuous_norm.comp hf).continuousOn) ⟨z, by simp, rfl⟩

/-- The order of growth is the `limsup` of `log log max (e, M(f, r)) / log r`. -/
theorem entireGrowthOrder_def (f : ℂ → ℂ) :
    entireGrowthOrder f = limsup (fun r : ℝ ↦ ((Real.log (Real.log (max (Real.exp 1)
      (maximumModulus f r))) / Real.log r : ℝ) : EReal)) atTop :=
  rfl

/-- Exponential type at most `σ` unfolds to its defining bound. -/
theorem isEntireExponentialType_iff {f : ℂ → ℂ} {σ : ℝ} :
    IsEntireExponentialType f σ ↔ Differentiable ℂ f ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp ((σ + ε) * ‖z‖) :=
  Iff.rfl

/-- A real upper bound on `entireGrowthOrder` is an order bound at infinity. -/
theorem orderLE_of_entireGrowthOrder_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) {ρ : ℝ}
    (horder : entireGrowthOrder f ≤ (ρ : EReal)) : TauCeti.OrderLE f ρ := by
  refine TauCeti.orderLE_def.mpr ?_
  intro A' hA
  let β : ℝ := (ρ + A') / 2
  have hβ : ρ < β := by dsimp [β]; linarith
  have hβA : β < A' := by dsimp [β]; linarith
  have hfz := norm_le_maximumModulus hf.continuous
  rw [entireGrowthOrder, Filter.limsup_eq] at horder
  have hlt := horder.trans_lt ((EReal.coe_lt_coe_iff).mpr hβ)
  obtain ⟨γE, hγE, hγβ⟩ := sInf_lt_iff.mp hlt
  have hEv : ∀ᶠ n : ℝ in atTop,
      ((Real.log (Real.log (max (Real.exp 1) (maximumModulus f n))) /
        Real.log n : ℝ) : EReal) ≤ γE := by
    simpa using hγE
  have hbot : γE ≠ ⊥ := by
    rintro rfl
    obtain ⟨r, hr⟩ := hEv.exists
    exact EReal.coe_ne_bot _ (le_bot_iff.mp hr)
  have htop : γE ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top β) hγβ.le
  have hcoe : (γE.toReal : EReal) = γE := EReal.coe_toReal htop hbot
  have hγlt : γE.toReal < β := (EReal.coe_lt_coe_iff).mp (hcoe.trans_lt hγβ)
  have hγA : γE.toReal ≤ A' := (hγlt.trans hβA).le
  rw [eventually_atTop] at hEv
  obtain ⟨R0, hR0⟩ := hEv
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_cobounded_le_norm (E := ℂ) (max R0 2)] with z hz
  have hR : R0 ≤ ‖z‖ := (le_max_left _ _).trans hz
  have h2 : (2 : ℝ) ≤ ‖z‖ := (le_max_right _ _).trans hz
  have hrpos : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) h2
  have hlogpos : 0 < Real.log ‖z‖ := Real.log_pos (lt_of_lt_of_le (by norm_num) h2)
  let L : ℝ := max (Real.exp 1) (maximumModulus f ‖z‖)
  have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) (le_max_left _ _)
  have hlogL1 : 1 ≤ Real.log L := by
    dsimp [L]
    conv_lhs => rw [← Real.log_exp (1 : ℝ)]
    exact Real.log_le_log (Real.exp_pos 1)
      (le_max_left (Real.exp 1) (maximumModulus f ‖z‖))
  have hlogLpos : 0 < Real.log L := lt_of_lt_of_le (by norm_num) hlogL1
  have hratio : Real.log (Real.log L) / Real.log ‖z‖ ≤ γE.toReal := by
    dsimp [L]
    exact (EReal.coe_le_coe_iff).mp (le_of_le_of_eq (hR0 ‖z‖ hR) hcoe.symm)
  have hloglog : Real.log (Real.log L) ≤ γE.toReal * Real.log ‖z‖ :=
    (div_le_iff₀ hlogpos).mp hratio
  have hlogL : Real.log L ≤ ‖z‖ ^ γE.toReal := by
    rw [Real.rpow_def_of_pos hrpos, mul_comm]
    exact (Real.log_le_iff_le_exp hlogLpos).mp hloglog
  have hLle : L ≤ Real.exp (‖z‖ ^ γE.toReal) := (Real.log_le_iff_le_exp hLpos).mp hlogL
  have hMle : maximumModulus f ‖z‖ ≤ Real.exp (‖z‖ ^ γE.toReal) := by
    refine (le_max_right (Real.exp 1) (maximumModulus f ‖z‖)).trans ?_
    dsimp [L] at hLle
    exact hLle
  have hpow : ‖z‖ ^ γE.toReal ≤ ‖z‖ ^ A' :=
    Real.rpow_le_rpow_of_exponent_le ((by norm_num : (1 : ℝ) ≤ 2).trans h2) hγA
  calc
    ‖f z‖ ≤ maximumModulus f ‖z‖ := hfz z
    _ ≤ Real.exp (‖z‖ ^ γE.toReal) := hMle
    _ ≤ Real.exp (‖z‖ ^ A') := Real.exp_le_exp.mpr hpow
    _ = 1 * ‖Real.exp (‖z‖ ^ A')‖ := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]

/-- The growth-order quotient is nonnegative for large radius, so the limsup is nonnegative. -/
lemma zero_le_entireGrowthOrder (f : ℂ → ℂ) : 0 ≤ entireGrowthOrder f := by
  unfold entireGrowthOrder
  refine le_trans (le_liminf_of_le (by isBoundedDefault) ?_) liminf_le_limsup
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
  refine EReal.coe_nonneg.2 ?_
  have hlog : 0 < Real.log r := Real.log_pos hr
  refine div_nonneg ?_ hlog.le
  refine Real.log_nonneg ?_
  have hmax : Real.exp 1 ≤ max (Real.exp 1) (maximumModulus f r) := le_max_left _ _
  have hlogmax :
      Real.log (Real.exp 1) ≤ Real.log (max (Real.exp 1) (maximumModulus f r)) :=
    Real.log_le_log (Real.exp_pos 1) hmax
  simpa [Real.log_exp] using hlogmax

/-- **41.10**: finite-order Hadamard factorization, including a fixed genus and its convergence.
The order bound `ρ` need not be sharp; its nonnegativity follows from `entireGrowthOrder`. -/
theorem hadamard_factorization {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∃ z, f z ≠ 0) {ρ : ℝ} (horder : entireGrowthOrder f ≤ (ρ : EReal)) :
    ∃ (m p : ℕ) (Q : ℂ[X]) (a : ℕ → Option ℂ),
      (p : ℝ) ≤ ρ ∧ (Q.natDegree : ℝ) ≤ ρ ∧
      (∀ n w, a n = some w → w ≠ 0) ∧
      Summable (slopeWeight p a) ∧
      (∀ z, Multipliable (fun n ↦ genusFactor p a n z)) ∧
      (∀ K : Set ℂ, IsCompact K → TendstoUniformlyOn
        (fun N z ↦ ∏ n ∈ Finset.range N, genusFactor p a n z)
        (fixedGenusCanonicalProduct p a) atTop K) ∧
      ∀ z, f z = z ^ m * Complex.exp (Q.eval z) * fixedGenusCanonicalProduct p a z := by
  obtain ⟨g, hg, hg0, hfg⟩ := exists_removedZero hf hne
  have hρ : 0 ≤ ρ := EReal.coe_nonneg.1 ((zero_le_entireGrowthOrder f).trans horder)
  have hord : TauCeti.OrderLE g ρ :=
    orderLE_of_pow_mul (orderLE_of_entireGrowthOrder_le hf horder) hfg
  obtain ⟨p, Q, a, hp, hdeg, ha0, hsum, hmul, htend, heq⟩ :=
    exists_hadamard_of_orderLE hg hg0 hρ hord
  refine ⟨analyticOrderNatAt f 0, p, Q, a, ?_, hdeg, ha0, hsum, hmul, htend, fun z => ?_⟩
  · simpa [hp] using Nat.floor_le hρ
  · rw [hfg z, heq z, mul_assoc, fixedGenusCanonicalProduct]

/-- The extended logarithmic indicator; zeros use `log 0 = -∞`, rather than real-log totalization.
  -/
@[expose]
def entireIndicator (f : ℂ → ℂ) (ρ θ : ℝ) : EReal :=
  limsup (fun r : ℝ ↦ ((r ^ (-ρ) : ℝ) : EReal) *
    ENNReal.log (ENNReal.ofReal ‖f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖)) atTop

/-- Cartwright's class, with the real-axis logarithmic integrability written nonnegatively. -/
@[expose]
def IsCartwrightFunction (f : ℂ → ℂ) : Prop :=
  (∃ z, f z ≠ 0) ∧ (∃ σ : ℝ, 0 ≤ σ ∧ IsEntireExponentialType f σ) ∧
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.log (max 1 ‖f x‖) / (1 + x ^ 2))) < ∞

/-- Zero-counting measure of a nonzero entire function. At an infinite analytic order the
coefficient is totalized by `toNat`; the theorems exclude the identically zero function. -/
@[expose]
def entireZeroCountingMeasure (f : ℂ → ℂ) : Measure ℂ :=
  Measure.sum (fun z : ℂ ↦ (analyticOrderAt f z).toNat • Measure.dirac z)

/-- The indicator is the `limsup` of `r ^ (-ρ) log ‖f (r e^{iθ})‖` with extended logarithm. -/
theorem entireIndicator_def (f : ℂ → ℂ) (ρ θ : ℝ) :
    entireIndicator f ρ θ = limsup (fun r : ℝ ↦ ((r ^ (-ρ) : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal ‖f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖)) atTop :=
  rfl

/-- Membership in Cartwright's class unfolds to its three defining conditions. -/
theorem isCartwrightFunction_iff {f : ℂ → ℂ} :
    IsCartwrightFunction f ↔ (∃ z, f z ≠ 0) ∧ (∃ σ : ℝ, 0 ≤ σ ∧ IsEntireExponentialType f σ) ∧
      (∫⁻ x : ℝ, ENNReal.ofReal (Real.log (max 1 ‖f x‖) / (1 + x ^ 2))) < ∞ :=
  Iff.rfl

/-- The zero-counting measure gives each point the mass of its analytic order. -/
theorem entireZeroCountingMeasure_def (f : ℂ → ℂ) :
    entireZeroCountingMeasure f =
      Measure.sum (fun z : ℂ ↦ (analyticOrderAt f z).toNat • Measure.dirac z) :=
  rfl

/-- **41.26**: Cartwright's radial zero density and concentration near the two real directions. -/
theorem cartwright_zero_distribution {f : ℂ → ℂ} (hf : IsCartwrightFunction f) :
    Tendsto (fun r : ℝ ↦ (entireZeroCountingMeasure f (Metric.closedBall 0 r)).toReal / r)
      atTop (𝓝 (((entireIndicator f 1 (Real.pi / 2)).toReal +
        (entireIndicator f 1 (-Real.pi / 2)).toReal) / Real.pi)) ∧
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun r : ℝ ↦ (entireZeroCountingMeasure f
        {z | ‖z‖ ≤ r ∧ ε ≤ min |Complex.arg z| |Complex.arg (-z)|}).toReal / r)
        atTop (𝓝 0) := by
  sorry

/-- **41.38**, entire-function logarithmic derivative estimate with a finite-linear-measure
exceptional set. Stated for entire `f`; for a constant `f` the proximity function is `0`. -/
theorem logarithmic_derivative_estimate {f : ℂ → ℂ} (hf : Differentiable ℂ f) {k : ℕ} :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E < ∞ ∧ ∃ C R : ℝ, 0 < C ∧ 1 < R ∧
      ∀ r : ℝ, R ≤ r → r ∉ E →
        ValueDistribution.proximity (fun z ↦ iteratedDeriv k f z / f z) ⊤ r ≤
          C * (Real.log (max 1 (ValueDistribution.characteristic f ⊤ r)) + Real.log r) := by
  sorry

/-- **41.48**: four shared finite values determine a nonconstant entire function. Infinity is
their common omitted spherical value. Only `g` is assumed nonconstant: a constant `f` sharing
four values with `g` forces `g` to be constant, by Picard's little theorem. Stated for entire
functions; the meromorphic version with values at poles is not covered. -/
theorem four_value_entire {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hng : ∃ z w, g z ≠ g w)
    (a : Fin 4 → ℂ) (ha : Function.Injective a)
    (hshared : ∀ i z, f z = a i ↔ g z = a i) : f = g := by
  sorry

end CKMA
