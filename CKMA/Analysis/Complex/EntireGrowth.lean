/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import CKMA.Analysis.Complex.EntireGrowth.Elementary
public import CKMA.Analysis.Complex.EntireGrowth.Zeros
public import CKMA.Analysis.Complex.EntireGrowth.Removal
public import CKMA.Analysis.Complex.EntireGrowth.Product
public import CKMA.Analysis.Complex.EntireGrowth.Factor

import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

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
* `CKMA.weierstrassElementaryFactor`, `CKMA.canonicalProductFactor`,
  `CKMA.fixedGenusCanonicalProduct`: Weierstrass canonical products of fixed genus.
* `CKMA.entireIndicator`: Phragmén–Lindelöf indicator function.
* `CKMA.IsCartwrightFunction`, `CKMA.entireZeroCountingMeasure`: Cartwright class and zero-counting
  measure.

## Main results

* `CKMA.hadamard_factorization`: Hadamard's factorization theorem for finite-order entire functions.
* `CKMA.cartwright_zero_distribution`: Cartwright's theorem on zero distribution.
* `CKMA.logarithmic_derivative_estimate`: Nevanlinna's lemma on the logarithmic derivative.
* `CKMA.four_value_entire`: Nevanlinna's four-value theorem for entire functions.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology MeasureTheory Polynomial
open scoped BigOperators ENNReal

/-- Maximum modulus on a circle, totalized by the real supremum convention at empty spheres. -/
def maximumModulus (f : ℂ → ℂ) (r : ℝ) : ℝ := sSup ((fun z ↦ ‖f z‖) '' Metric.sphere 0 r)

/-- Entire-function order, retaining the possibility of infinite order.
The `max e` cutoff gives the usual order zero for constants and does not affect growth order. -/
def entireGrowthOrder (f : ℂ → ℂ) : EReal :=
  limsup (fun r : ℝ ↦ ((Real.log (Real.log (max (Real.exp 1) (maximumModulus f r))) /
    Real.log r : ℝ) : EReal)) atTop

/-- Exponential type at most `σ`, allowing an arbitrarily small increase in the exponent. -/
def IsEntireExponentialType (f : ℂ → ℂ) (σ : ℝ) : Prop :=
  Differentiable ℂ f ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp ((σ + ε) * ‖z‖)

/-- The genus-`p` Weierstrass elementary factor. -/
def weierstrassElementaryFactor (p : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * Complex.exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1 : ℂ))

/-- A zero list may be finite (entries `none`) or infinite and records multiplicity by repetition.
  -/
def canonicalProductFactor (p : ℕ) (a : ℕ → Option ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  match a n with
  | none => 1
  | some w => weierstrassElementaryFactor p (z / w)

/-- The canonical product of fixed genus, evaluated pointwise. Its convergence is asserted
explicitly in factorization targets, so the totalized infinite product is not mistaken for a proof.
  -/
def fixedGenusCanonicalProduct (p : ℕ) (a : ℕ → Option ℂ) (z : ℂ) : ℂ :=
  ∏' n : ℕ, canonicalProductFactor p a n z

/-- A finite value of `entireGrowthOrder` is an order bound at infinity. -/
theorem orderLE_of_entireGrowthOrder {f : ℂ → ℂ} (hf : Differentiable ℂ f) {ρ : ℝ}
    (horder : entireGrowthOrder f = (ρ : EReal)) : TauCeti.OrderLE f ρ := by
  refine TauCeti.orderLE_def.mpr ?_
  intro A' hA
  let β : ℝ := (ρ + A') / 2
  have hβ : ρ < β := by dsimp [β]; linarith
  have hβA : β < A' := by dsimp [β]; linarith
  have hfz (z : ℂ) : ‖f z‖ ≤ maximumModulus f ‖z‖ := by
    refine le_csSup ?_ ⟨z, ?_, rfl⟩
    · exact (isCompact_sphere (0 : ℂ) ‖z‖).bddAbove_image
        ((continuous_norm.comp hf.continuous).continuousOn)
    · simp
  rw [entireGrowthOrder, Filter.limsup_eq] at horder
  have hlt := horder.trans_lt ((EReal.coe_lt_coe_iff).mpr hβ)
  obtain ⟨γE, hγE, hγβ⟩ := sInf_lt_iff.mp hlt
  have hργ : (ρ : EReal) ≤ γE := (horder.symm).trans_le (sInf_le hγE)
  have hbot : γE ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot ρ) hργ
  have htop : γE ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top β) hγβ.le
  have hcoe : (γE.toReal : EReal) = γE := EReal.coe_toReal htop hbot
  have hγlt : γE.toReal < β := (EReal.coe_lt_coe_iff).mp (hcoe.trans_lt hγβ)
  have hγA : γE.toReal ≤ A' := (hγlt.trans hβA).le
  have hEv : ∀ᶠ n : ℝ in atTop,
      ((Real.log (Real.log (max (Real.exp 1) (maximumModulus f n))) /
        Real.log n : ℝ) : EReal) ≤ γE := by
    simpa using hγE
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

/-- **41.10**: finite-order Hadamard factorization, including a fixed genus and its convergence. -/
theorem hadamard_factorization {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∃ z, f z ≠ 0) {ρ : ℝ} (hρ : 0 ≤ ρ) (horder : entireGrowthOrder f = (ρ : EReal)) :
    ∃ (m p : ℕ) (Q : ℂ[X]) (a : ℕ → Option ℂ),
      (p : ℝ) ≤ ρ ∧ (Q.natDegree : ℝ) ≤ ρ ∧
      (∀ n w, a n = some w → w ≠ 0) ∧
      Summable (fun n ↦ match a n with
        | none => (0 : ℝ)
        | some w => ‖w‖ ^ (-((p : ℝ) + 1))) ∧
      (∀ z, Multipliable (fun n ↦ canonicalProductFactor p a n z)) ∧
      (∀ K : Set ℂ, IsCompact K → TendstoUniformlyOn
        (fun N z ↦ ∏ n ∈ Finset.range N, canonicalProductFactor p a n z)
        (fixedGenusCanonicalProduct p a) atTop K) ∧
      ∀ z, f z = z ^ m * Complex.exp (Q.eval z) * fixedGenusCanonicalProduct p a z := by
  obtain ⟨g, hg, hg0, hfg⟩ := exists_removedZero hf hne
  have hord : TauCeti.OrderLE g ρ :=
    orderLE_of_pow_mul (orderLE_of_entireGrowthOrder hf horder) hfg
  obtain ⟨p, Q, a, hp, hdeg, ha0, hsum, hmul, htend, heq⟩ :=
    exists_hadamard_of_orderLE hg hg0 hρ hord
  have hfac (n : ℕ) (z : ℂ) : canonicalProductFactor p a n z = genusFactor p a n z := by
    cases h : a n with
    | none => simp [canonicalProductFactor, genusFactor, h]
    | some w =>
      simp [canonicalProductFactor, genusFactor, h, weierstrassElementaryFactor,
        weierstrassFactor, weierstrassSum]
  refine ⟨analyticOrderNatAt f 0, p, Q, a, ?_, hdeg, ha0, ?_, ?_, ?_, ?_⟩
  · simpa [hp] using Nat.floor_le hρ
  · refine hsum.congr fun n => ?_
    cases h : a n with
    | none => simp [slopeWeight, h]
    | some w => simp [slopeWeight, h]
  · intro z
    exact (hmul z).congr fun n => hfac n z
  · intro K hKcomp
    refine ((htend K hKcomp).congr ?_).congr_right ?_
    · refine Eventually.of_forall fun _ => ?_
      intro z _
      exact Finset.prod_congr rfl fun n _ => (hfac n z).symm
    · intro z _
      unfold fixedGenusCanonicalProduct
      exact tprod_congr fun n => (hfac n z).symm
  · intro z
    rw [hfg z, heq z, mul_assoc]
    congr 1

/-- The extended logarithmic indicator; zeros use `log 0 = -∞`, rather than real-log totalization.
  -/
def entireIndicator (f : ℂ → ℂ) (ρ θ : ℝ) : EReal :=
  limsup (fun r : ℝ ↦ ((r ^ (-ρ) : ℝ) : EReal) *
    ENNReal.log (ENNReal.ofReal ‖f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖)) atTop

/-- Cartwright's class, with the real-axis logarithmic integrability written nonnegatively. -/
def IsCartwrightFunction (f : ℂ → ℂ) : Prop :=
  (∃ z, f z ≠ 0) ∧ (∃ σ : ℝ, 0 ≤ σ ∧ IsEntireExponentialType f σ) ∧
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.log (max 1 ‖f x‖) / (1 + x ^ 2))) < ∞

/-- Zero-counting measure of a nonzero entire function. At an infinite analytic order the
coefficient is totalized by `toNat`; the theorems exclude the identically zero function. -/
def entireZeroCountingMeasure (f : ℂ → ℂ) : Measure ℂ :=
  Measure.sum (fun z : ℂ ↦ (analyticOrderAt f z).toNat • Measure.dirac z)

set_option warn.sorry false in
/-- **41.26**: Cartwright's radial zero density and concentration near the two real directions. -/
theorem cartwright_zero_distribution {f : ℂ → ℂ} (hf : IsCartwrightFunction f) :
    Tendsto (fun r : ℝ ↦ (entireZeroCountingMeasure f (Metric.closedBall 0 r)).toReal / r)
      atTop (𝓝 (((entireIndicator f 1 (Real.pi / 2)).toReal +
        (entireIndicator f 1 (-Real.pi / 2)).toReal) / Real.pi)) ∧
    ∀ ε : ℝ, 0 < ε → ε < Real.pi / 2 →
      Tendsto (fun r : ℝ ↦ (entireZeroCountingMeasure f
        {z | ‖z‖ ≤ r ∧ ε ≤ min |Complex.arg z| |Complex.arg (-z)|}).toReal / r)
        atTop (𝓝 0) := by
  sorry

set_option warn.sorry false in
/-- **41.38**, entire-function logarithmic derivative estimate with a finite-linear-measure
exceptional set. The general meromorphic version and finite-order sharpening remain. -/
theorem logarithmic_derivative_estimate {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnonconstant : ∃ z w, f z ≠ f w) {k : ℕ} :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E < ∞ ∧ ∃ C R : ℝ, 0 < C ∧ 1 < R ∧
      ∀ r : ℝ, R ≤ r → r ∉ E →
        ValueDistribution.proximity (fun z ↦ iteratedDeriv k f z / f z) ⊤ r ≤
          C * (Real.log (max 1 (ValueDistribution.characteristic f ⊤ r)) + Real.log r) := by
  sorry

set_option warn.sorry false in
/-- **41.48**: four shared finite values determine nonconstant entire functions.
Infinity is their common omitted spherical value. The meromorphic spherical version
requires a separate interface for values at poles. -/
theorem four_value_entire {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hnf : ∃ z w, f z ≠ f w) (hng : ∃ z w, g z ≠ g w)
    (a : Fin 4 → ℂ) (ha : Function.Injective a)
    (hshared : ∀ i z, f z = a i ↔ g z = a i) : f = g := by
  sorry

end CKMA
