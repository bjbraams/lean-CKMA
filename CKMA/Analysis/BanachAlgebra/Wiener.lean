/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Complex.Circle

import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Algebra.Ring.MinimalAxioms

/-!
# Absolutely convergent bilateral Fourier series

Functions on the unit circle are represented by Fourier series indexed by the integers, with
summable coefficient norms. Circle elements are nonzero, so negative integer powers are
well-defined. Coefficient convolution records multiplication of these series; Wiener's lemma
asserts closure under pointwise inversion for functions with no zero on the circle.
Source: GAPS 20.40.

The proof realises the coefficient space as a commutative unital complex Banach algebra under
convolution, with norm transported from `lp (fun _ : ℤ => ℂ) 1`. Absolute convergence of the
Cauchy product uses `tsum_mul_tsum_of_summable_norm`. Characters are circle evaluations, by
density of finitely supported sequences (`lp.hasSum_single`) and the bound
`AlgHom.norm_apply_le_self`. A nowhere-vanishing series is therefore a unit, by
`WeakDual.CharacterSpace.exists_apply_eq_zero` and Gelfand–Mazur.

## Main definitions

* `CKMA.wienerSeries`: bilateral Fourier series evaluated on the unit circle.
* `CKMA.HasAbsolutelyConvergentFourierSeries`: representation by an `ℓ¹(ℤ)` Fourier series.
* `CKMA.wienerConvolution`: bilateral convolution of integer-indexed sequences.

## Main results

* `CKMA.hasAbsolutelyConvergentFourierSeries_iff`: defining lemma, with `CKMA.wienerSeries_def`
  and `CKMA.wienerConvolution_def`.
* `CKMA.HasAbsolutelyConvergentFourierSeries.inv`: Wiener's `1/f` lemma on the unit circle
  (**20.40**).
-/

public section

noncomputable section

namespace CKMA

open scoped BigOperators

open WeakDual

/-- A bilateral Fourier series evaluated on the unit circle. -/
@[expose]
def wienerSeries (a : ℤ → ℂ) (z : Circle) : ℂ := ∑' n, a n * (z : ℂ) ^ n

/-- Absolute Fourier convergence, with a specified circle-valued function. -/
@[expose]
def HasAbsolutelyConvergentFourierSeries (f : Circle → ℂ) : Prop :=
  ∃ a : ℤ → ℂ, Summable (fun n ↦ ‖a n‖) ∧ f = wienerSeries a

/-- Convolution of bilateral coefficient sequences. -/
@[expose]
def wienerConvolution (a b : ℤ → ℂ) (n : ℤ) : ℂ := ∑' k, a k * b (n - k)

/-- Defining equation of `wienerSeries`. -/
theorem wienerSeries_def (a : ℤ → ℂ) (z : Circle) :
    wienerSeries a z = ∑' n, a n * (z : ℂ) ^ n :=
  rfl

/-- Defining property of `HasAbsolutelyConvergentFourierSeries`. -/
theorem hasAbsolutelyConvergentFourierSeries_iff {f : Circle → ℂ} :
    HasAbsolutelyConvergentFourierSeries f ↔
      ∃ a : ℤ → ℂ, Summable (fun n ↦ ‖a n‖) ∧ f = wienerSeries a :=
  Iff.rfl

/-- A bilateral Fourier series with summable coefficient norms is absolutely convergent. -/
theorem hasAbsolutelyConvergentFourierSeries_wienerSeries {a : ℤ → ℂ}
    (ha : Summable fun n ↦ ‖a n‖) : HasAbsolutelyConvergentFourierSeries (wienerSeries a) :=
  ⟨a, ha, rfl⟩

/-- Defining equation of `wienerConvolution`. -/
theorem wienerConvolution_def (a b : ℤ → ℂ) (n : ℤ) :
    wienerConvolution a b n = ∑' k, a k * b (n - k) :=
  rfl

private lemma hp_one : 0 < (1 : ENNReal).toReal := by
  rw [ENNReal.toReal_one]
  exact zero_lt_one

private lemma ennreal_one_pos : (0 : ENNReal) < 1 := zero_lt_one

private lemma summable_of_memℓp {f : ℤ → ℂ} (hf : Memℓp f 1) : Summable fun n ↦ ‖f n‖ := by
  rw [memℓp_gen_iff hp_one] at hf
  refine hf.congr fun n ↦ ?_
  rw [ENNReal.toReal_one, Real.rpow_one]

private lemma memℓp_of_summable {f : ℤ → ℂ} (hf : Summable fun n ↦ ‖f n‖) : Memℓp f 1 := by
  rw [memℓp_gen_iff hp_one]
  refine hf.congr fun n ↦ ?_
  rw [ENNReal.toReal_one, Real.rpow_one]

private lemma norm_lp_eq_tsum (f : lp (fun _ : ℤ ↦ ℂ) 1) : ‖f‖ = ∑' n, ‖f n‖ := by
  rw [lp.norm_eq_tsum_rpow hp_one f]
  simp_rw [ENNReal.toReal_one, div_one, Real.rpow_one]

/-- Reindexing `(k, m) ↦ (k, k + m)`. -/
private def indexShift : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.1, p.1 + p.2)
  invFun p := (p.1, p.2 - p.1)
  left_inv p := by
    ext
    · rfl
    · ring
  right_inv p := by
    ext
    · rfl
    · ring

private lemma indexShift_symm_apply (p : ℤ × ℤ) : indexShift.symm p = (p.1, p.2 - p.1) := rfl

/-- Reindexing `k ↦ n - k`. -/
private def reflect (n : ℤ) : ℤ ≃ ℤ where
  toFun k := n - k
  invFun k := n - k
  left_inv k := by ring
  right_inv k := by ring

private lemma reflect_apply (n k : ℤ) : reflect n k = n - k := rfl

/-- Reindexing `(k, j) ↦ (k + j, k)`. -/
private def assocShift : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.1 + p.2, p.1)
  invFun p := (p.2, p.1 - p.2)
  left_inv p := by
    ext
    · ring
    · ring
  right_inv p := by
    ext
    · ring
    · ring

private lemma assocShift_symm_apply (p : ℤ × ℤ) :
    assocShift.symm p = (p.2, p.1 - p.2) := rfl

private abbrev shiftNorm (a b : ℤ → ℂ) (p : ℤ × ℤ) : ℝ := ‖a p.1‖ * ‖b (p.2 - p.1)‖

private lemma summable_shiftNorm {a b : ℤ → ℂ} (ha : Summable fun n ↦ ‖a n‖)
    (hb : Summable fun n ↦ ‖b n‖) : Summable (shiftNorm a b) := by
  have hprod : Summable fun p : ℤ × ℤ ↦ ‖a p.1‖ * ‖b p.2‖ :=
    ha.mul_of_nonneg hb (fun n ↦ norm_nonneg (a n)) fun n ↦ norm_nonneg (b n)
  refine ((indexShift.symm.summable_iff (f := fun p : ℤ × ℤ ↦ ‖a p.1‖ * ‖b p.2‖)).2
    hprod).congr fun p ↦ ?_
  rw [Function.comp_apply, indexShift_symm_apply]

private lemma summable_shiftNorm_fiber {a b : ℤ → ℂ} (ha : Summable fun n ↦ ‖a n‖)
    (hb : Summable fun n ↦ ‖b n‖) (n : ℤ) : Summable fun k ↦ ‖a k‖ * ‖b (n - k)‖ := by
  have hcomp : Summable fun p : ℤ × ℤ ↦ shiftNorm a b (Equiv.prodComm ℤ ℤ p) :=
    ((Equiv.prodComm ℤ ℤ).summable_iff (f := shiftNorm a b)).2 (summable_shiftNorm ha hb)
  refine (hcomp.prod_factor n).congr fun k ↦ ?_
  rw [Equiv.prodComm_apply]
  rfl

private lemma summable_term {a b : ℤ → ℂ} (ha : Summable fun n ↦ ‖a n‖)
    (hb : Summable fun n ↦ ‖b n‖) (n : ℤ) : Summable fun k ↦ a k * b (n - k) := by
  refine Summable.of_norm ?_
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun k ↦ norm_mul_le (a k) (b (n - k))) (summable_shiftNorm_fiber ha hb n)

private lemma norm_wienerConvolution_le {a b : ℤ → ℂ} (ha : Summable fun n ↦ ‖a n‖)
    (hb : Summable fun n ↦ ‖b n‖) (n : ℤ) :
    ‖wienerConvolution a b n‖ ≤ ∑' k, ‖a k‖ * ‖b (n - k)‖ := by
  rw [wienerConvolution]
  have hnorm : Summable fun k ↦ ‖a k * b (n - k)‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun k ↦ norm_mul_le (a k) (b (n - k))) (summable_shiftNorm_fiber ha hb n)
  exact le_trans (norm_tsum_le_tsum_norm hnorm)
    (hnorm.tsum_le_tsum (fun k ↦ norm_mul_le (a k) (b (n - k)))
      (summable_shiftNorm_fiber ha hb n))

private lemma summable_norm_convolution {a b : ℤ → ℂ} (ha : Summable fun n ↦ ‖a n‖)
    (hb : Summable fun n ↦ ‖b n‖) : Summable fun n ↦ ‖wienerConvolution a b n‖ := by
  have hcomp : Summable fun p : ℤ × ℤ ↦ shiftNorm a b (Equiv.prodComm ℤ ℤ p) :=
    ((Equiv.prodComm ℤ ℤ).summable_iff (f := shiftNorm a b)).2 (summable_shiftNorm ha hb)
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (norm_wienerConvolution_le ha hb)
    hcomp.prod

private lemma memℓp_convolution {a b : ℤ → ℂ} (ha : Summable fun n ↦ ‖a n‖)
    (hb : Summable fun n ↦ ‖b n‖) : Memℓp (wienerConvolution a b) 1 :=
  memℓp_of_summable (summable_norm_convolution ha hb)

private lemma tsum_shiftNorm {a b : ℤ → ℂ} (ha : Summable fun n ↦ ‖a n‖)
    (hb : Summable fun n ↦ ‖b n‖) :
    ∑' p, shiftNorm a b p = (∑' n, ‖a n‖) * ∑' n, ‖b n‖ := by
  have ha' : Summable fun n ↦ ‖(‖a n‖ : ℝ)‖ := by simpa [norm_norm] using ha
  have hb' : Summable fun n ↦ ‖(‖b n‖ : ℝ)‖ := by simpa [norm_norm] using hb
  have hprod :=
    tsum_mul_tsum_of_summable_norm (f := fun n ↦ (‖a n‖ : ℝ)) (g := fun n ↦ (‖b n‖ : ℝ)) ha' hb'
  have hre := indexShift.symm.tsum_eq (fun p : ℤ × ℤ ↦ ‖a p.1‖ * ‖b p.2‖)
  have hcongr : ∑' p, shiftNorm a b p =
      ∑' p, ‖a (indexShift.symm p).1‖ * ‖b (indexShift.symm p).2‖ := by
    refine tsum_congr fun p ↦ ?_
    rw [indexShift_symm_apply]
  exact (hcongr.trans hre).trans hprod.symm

private lemma tsum_fiber_eq_shift {a b : ℤ → ℂ} (ha : Summable fun n ↦ ‖a n‖)
    (hb : Summable fun n ↦ ‖b n‖) :
    ∑' n, ∑' k, ‖a k‖ * ‖b (n - k)‖ = ∑' p, shiftNorm a b p := by
  have hcomp : Summable fun p : ℤ × ℤ ↦ shiftNorm a b (Equiv.prodComm ℤ ℤ p) :=
    ((Equiv.prodComm ℤ ℤ).summable_iff (f := shiftNorm a b)).2 (summable_shiftNorm ha hb)
  have hswap := (Equiv.prodComm ℤ ℤ).tsum_eq (shiftNorm a b)
  refine Eq.trans ?_ hswap
  refine Eq.trans ?_ hcomp.tsum_prod.symm
  refine tsum_congr fun n ↦ tsum_congr fun k ↦ ?_
  rw [Equiv.prodComm_apply]
  rfl

private lemma tsum_norm_convolution_le {a b : ℤ → ℂ} (ha : Summable fun n ↦ ‖a n‖)
    (hb : Summable fun n ↦ ‖b n‖) :
    ∑' n, ‖wienerConvolution a b n‖ ≤ (∑' n, ‖a n‖) * ∑' n, ‖b n‖ := by
  have hcomp : Summable fun p : ℤ × ℤ ↦ shiftNorm a b (Equiv.prodComm ℤ ℤ p) :=
    ((Equiv.prodComm ℤ ℤ).summable_iff (f := shiftNorm a b)).2 (summable_shiftNorm ha hb)
  have hinner : Summable fun n ↦ ∑' k, ‖a k‖ * ‖b (n - k)‖ := hcomp.prod
  exact le_trans
    ((summable_norm_convolution ha hb).tsum_le_tsum (norm_wienerConvolution_le ha hb) hinner)
    (by rw [tsum_fiber_eq_shift ha hb, tsum_shiftNorm ha hb])

private lemma summable_slice {a b c : ℤ → ℂ} (ha : Summable fun n ↦ ‖a n‖)
    (hb : Summable fun n ↦ ‖b n‖) (hc : Summable fun n ↦ ‖c n‖) (n : ℤ) :
    Summable fun p : ℤ × ℤ ↦ ‖a p.1‖ * ‖b p.2‖ * ‖c (n - p.1 - p.2)‖ := by
  have hab : Summable fun p : ℤ × ℤ ↦ ‖a p.1‖ * ‖b p.2‖ :=
    ha.mul_of_nonneg hb (fun i ↦ norm_nonneg (a i)) fun i ↦ norm_nonneg (b i)
  have hcube : Summable fun q : (ℤ × ℤ) × ℤ ↦ ‖a q.1.1‖ * ‖b q.1.2‖ * ‖c q.2‖ :=
    hab.mul_of_nonneg hc (fun p ↦ mul_nonneg (norm_nonneg (a p.1)) (norm_nonneg (b p.2)))
      fun i ↦ norm_nonneg (c i)
  let ι : ℤ × ℤ → (ℤ × ℤ) × ℤ := fun p ↦ (p, n - p.1 - p.2)
  have hinj : Function.Injective ι := fun p q h ↦ congrArg Prod.fst h
  exact hcube.comp_injective hinj

private lemma summable_rightTerm {a b c : ℤ → ℂ} (ha : Summable fun n ↦ ‖a n‖)
    (hb : Summable fun n ↦ ‖b n‖) (hc : Summable fun n ↦ ‖c n‖) (n : ℤ) :
    Summable fun p : ℤ × ℤ ↦ a p.1 * b p.2 * c (n - p.1 - p.2) := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) ?_ (summable_slice ha hb hc n)
  intro p
  exact le_trans (norm_mul_le (a p.1 * b p.2) (c (n - p.1 - p.2)))
    (mul_le_mul_of_nonneg_right (norm_mul_le (a p.1) (b p.2)) (norm_nonneg _))

private lemma summable_leftTerm {a b c : ℤ → ℂ} (ha : Summable fun n ↦ ‖a n‖)
    (hb : Summable fun n ↦ ‖b n‖) (hc : Summable fun n ↦ ‖c n‖) (n : ℤ) :
    Summable fun p : ℤ × ℤ ↦ a p.2 * b (p.1 - p.2) * c (n - p.1) := by
  refine ((assocShift.symm.summable_iff
    (f := fun p : ℤ × ℤ ↦ a p.1 * b p.2 * c (n - p.1 - p.2))).2
    (summable_rightTerm ha hb hc n)).congr fun p ↦ ?_
  rw [Function.comp_apply, assocShift_symm_apply]
  have hidx : n - p.2 - (p.1 - p.2) = n - p.1 := by ring
  rw [hidx]

private lemma wienerConvolution_assoc {a b c : ℤ → ℂ} (ha : Summable fun n ↦ ‖a n‖)
    (hb : Summable fun n ↦ ‖b n‖) (hc : Summable fun n ↦ ‖c n‖) (n : ℤ) :
    wienerConvolution (wienerConvolution a b) c n =
      wienerConvolution a (wienerConvolution b c) n := by
  have hR := summable_rightTerm ha hb hc n
  have hL := summable_leftTerm ha hb hc n
  have hRight : wienerConvolution a (wienerConvolution b c) n =
      ∑' p : ℤ × ℤ, a p.1 * b p.2 * c (n - p.1 - p.2) := by
    unfold wienerConvolution
    refine Eq.trans
      (tsum_congr fun k ↦ ((summable_term hb hc (n - k)).tsum_mul_left (a k)).symm) ?_
    have hpt : ∀ k j, a k * (b j * c ((n - k) - j)) = a k * b j * c (n - k - j) := by
      intro k j
      ring
    refine Eq.trans (tsum_congr fun k ↦ tsum_congr (hpt k)) ?_
    exact hR.tsum_prod.symm
  have hLeft : wienerConvolution (wienerConvolution a b) c n =
      ∑' p : ℤ × ℤ, a p.2 * b (p.1 - p.2) * c (n - p.1) := by
    unfold wienerConvolution
    refine Eq.trans (tsum_congr fun m ↦
      ((summable_term ha hb m).tsum_mul_right (c (n - m))).symm) ?_
    exact hL.tsum_prod.symm
  have hLR : ∑' p : ℤ × ℤ, a p.2 * b (p.1 - p.2) * c (n - p.1) =
      ∑' p : ℤ × ℤ, a p.1 * b p.2 * c (n - p.1 - p.2) := by
    rw [← assocShift.symm.tsum_eq fun p ↦ a p.1 * b p.2 * c (n - p.1 - p.2)]
    refine tsum_congr fun p ↦ ?_
    rw [assocShift_symm_apply]
    have hidx : n - p.2 - (p.1 - p.2) = n - p.1 := by ring
    rw [hidx]
  rw [hLeft, hLR, hRight.symm]

/-- The Wiener algebra of absolutely summable bilateral coefficient sequences. -/
private structure WienerAlgebra where
  toLp : lp (fun _ : ℤ ↦ ℂ) 1

private instance : CoeFun WienerAlgebra fun _ ↦ ℤ → ℂ where
  coe a := a.toLp

private instance : Zero WienerAlgebra where
  zero := ⟨0⟩

private instance : Add WienerAlgebra where
  add a b := ⟨a.toLp + b.toLp⟩

private instance : Neg WienerAlgebra where
  neg a := ⟨-a.toLp⟩

private instance : One WienerAlgebra where
  one := ⟨lp.single (E := fun _ : ℤ ↦ ℂ) 1 0 1⟩

private instance : SMul ℂ WienerAlgebra where
  smul c a := ⟨c • a.toLp⟩

private lemma toLp_injective {a b : WienerAlgebra} (h : a.toLp = b.toLp) : a = b := by
  cases a
  cases b
  cases h
  rfl

private lemma summable_norm_toLp (a : WienerAlgebra) : Summable fun n ↦ ‖a n‖ :=
  summable_of_memℓp (lp.memℓp a.toLp)

private instance : Mul WienerAlgebra where
  mul a b := ⟨⟨wienerConvolution a b, memℓp_convolution (summable_norm_toLp a)
    (summable_norm_toLp b)⟩⟩

@[ext]
private lemma ext {a b : WienerAlgebra} (h : ∀ n : ℤ, a n = b n) : a = b := by
  apply toLp_injective
  apply lp.ext
  funext n
  exact h n

private lemma toLp_zero : (0 : WienerAlgebra).toLp = 0 := rfl

private lemma toLp_add (a b : WienerAlgebra) : (a + b).toLp = a.toLp + b.toLp := rfl

private lemma toLp_neg (a : WienerAlgebra) : (-a).toLp = -a.toLp := rfl

private lemma toLp_smul (c : ℂ) (a : WienerAlgebra) : (c • a).toLp = c • a.toLp := rfl

private lemma toLp_one : (1 : WienerAlgebra).toLp = lp.single (E := fun _ : ℤ ↦ ℂ) 1 0 1 := rfl

private lemma apply_zero (n : ℤ) : (0 : WienerAlgebra) n = 0 := by
  rw [toLp_zero, lp.coeFn_zero, Pi.zero_apply]

private lemma apply_add (a b : WienerAlgebra) (n : ℤ) : (a + b) n = a n + b n := by
  rw [toLp_add, lp.coeFn_add, Pi.add_apply]

private lemma apply_neg (a : WienerAlgebra) (n : ℤ) : (-a) n = -a n := by
  rw [toLp_neg, lp.coeFn_neg, Pi.neg_apply]

private lemma apply_smul (c : ℂ) (a : WienerAlgebra) (n : ℤ) : (c • a) n = c * a n := by
  rw [toLp_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]

private lemma apply_one (n : ℤ) : (1 : WienerAlgebra) n = if n = 0 then 1 else 0 := by
  rw [toLp_one, lp.coeFn_single, Pi.single_apply]

private lemma apply_mul (a b : WienerAlgebra) (n : ℤ) :
    (a * b) n = wienerConvolution a b n := rfl

private lemma add_assoc_alg (a b c : WienerAlgebra) : a + b + c = a + (b + c) := by
  ext n
  rw [apply_add, apply_add, apply_add, apply_add, add_assoc]

private lemma zero_add_alg (a : WienerAlgebra) : 0 + a = a := by
  ext n
  rw [apply_add, apply_zero, zero_add]

private lemma neg_add_cancel_alg (a : WienerAlgebra) : -a + a = 0 := by
  ext n
  rw [apply_add, apply_neg, apply_zero, neg_add_cancel]

private lemma mul_comm_alg (a b : WienerAlgebra) : a * b = b * a := by
  ext n
  rw [apply_mul, apply_mul, wienerConvolution, wienerConvolution]
  rw [← (reflect n).tsum_eq fun k ↦ a k * b (n - k)]
  refine tsum_congr fun j ↦ ?_
  rw [reflect_apply]
  have hsub : n - (n - j) = j := by ring
  rw [hsub, mul_comm]

private lemma one_mul_alg (a : WienerAlgebra) : 1 * a = a := by
  ext n
  rw [apply_mul, wienerConvolution]
  have hzero : ∀ k, k ≠ 0 → (1 : WienerAlgebra) k * a (n - k) = 0 := by
    intro k hk
    rw [apply_one, ite_eq_right hk, zero_mul]
  rw [tsum_eq_single 0 hzero, apply_one, ite_eq_left rfl, one_mul, sub_zero]

private lemma left_distrib_alg (a b c : WienerAlgebra) : a * (b + c) = a * b + a * c := by
  ext n
  rw [apply_mul, apply_add, apply_mul, apply_mul]
  unfold wienerConvolution
  have hb := summable_term (summable_norm_toLp a) (summable_norm_toLp b) n
  have hc := summable_term (summable_norm_toLp a) (summable_norm_toLp c) n
  rw [← hb.tsum_add hc]
  refine tsum_congr fun k ↦ ?_
  rw [apply_add, mul_add]

private lemma mul_assoc_alg (a b c : WienerAlgebra) : a * b * c = a * (b * c) := by
  ext n
  rw [apply_mul, apply_mul]
  exact wienerConvolution_assoc (summable_norm_toLp a) (summable_norm_toLp b)
    (summable_norm_toLp c) n

private lemma norm_mul_le_of_coe (a b : WienerAlgebra) :
    ‖(a * b).toLp‖ ≤ ‖a.toLp‖ * ‖b.toLp‖ := by
  rw [norm_lp_eq_tsum, norm_lp_eq_tsum, norm_lp_eq_tsum]
  exact tsum_norm_convolution_le (summable_norm_toLp a) (summable_norm_toLp b)

private instance : NormedCommRing WienerAlgebra := by
  letI : CommRing WienerAlgebra :=
    CommRing.ofMinimalAxioms add_assoc_alg zero_add_alg neg_add_cancel_alg mul_assoc_alg
      mul_comm_alg one_mul_alg left_distrib_alg
  let hom : WienerAlgebra →+ lp (fun _ : ℤ ↦ ℂ) 1 :=
    { toFun := WienerAlgebra.toLp
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  exact
    ({ NormedAddCommGroup.induced WienerAlgebra (lp (fun _ : ℤ ↦ ℂ) 1) hom
        (fun a b h ↦ toLp_injective h),
      (inferInstance : CommRing WienerAlgebra) with
      norm_mul_le := norm_mul_le_of_coe } : NormedCommRing WienerAlgebra)

private lemma norm_eq_toLp (a : WienerAlgebra) : ‖a‖ = ‖a.toLp‖ := rfl

private def toLpAddHom : WienerAlgebra →+ lp (fun _ : ℤ ↦ ℂ) 1 where
  toFun := WienerAlgebra.toLp
  map_zero' := rfl
  map_add' := fun _ _ ↦ rfl

private def toLpEquiv : WienerAlgebra ≃ lp (fun _ : ℤ ↦ ℂ) 1 where
  toFun := WienerAlgebra.toLp
  invFun f := ⟨f⟩
  left_inv a := by
    cases a
    rfl
  right_inv _ := rfl

private lemma isometry_toLp : Isometry (fun a : WienerAlgebra ↦ a.toLp) :=
  Isometry.of_dist_eq fun _ _ ↦ rfl

private instance : CompleteSpace WienerAlgebra :=
  (completeSpace_congr (e := toLpEquiv) isometry_toLp.isUniformEmbedding).2
    (inferInstance : CompleteSpace (lp (fun _ : ℤ ↦ ℂ) 1))

private instance : NormOneClass WienerAlgebra where
  norm_one := by
    rw [norm_eq_toLp, toLp_one, lp.norm_single ennreal_one_pos, norm_one]

private lemma convolution_smul_left (r : ℂ) {a b : ℤ → ℂ} (ha : Summable fun n ↦ ‖a n‖)
    (hb : Summable fun n ↦ ‖b n‖) (n : ℤ) :
    wienerConvolution (fun k ↦ r * a k) b n = r * wienerConvolution a b n := by
  unfold wienerConvolution
  rw [← (summable_term ha hb n).tsum_mul_left r]
  refine tsum_congr fun k ↦ ?_
  ring

private lemma convolution_smul_right (r : ℂ) {a b : ℤ → ℂ} (ha : Summable fun n ↦ ‖a n‖)
    (hb : Summable fun n ↦ ‖b n‖) (n : ℤ) :
    wienerConvolution a (fun k ↦ r * b k) n = r * wienerConvolution a b n := by
  unfold wienerConvolution
  rw [← (summable_term ha hb n).tsum_mul_left r]
  refine tsum_congr fun k ↦ ?_
  ring

private lemma smul_mul_alg (r : ℂ) (x y : WienerAlgebra) : r • x * y = r • (x * y) := by
  ext n
  rw [apply_mul, apply_smul, apply_mul]
  have hfun : wienerConvolution (⇑(r • x)) (⇑y) n =
      wienerConvolution (fun k ↦ r * x k) (⇑y) n := by
    unfold wienerConvolution
    refine tsum_congr fun k ↦ ?_
    rw [apply_smul]
  rw [hfun]
  exact convolution_smul_left r (summable_norm_toLp x) (summable_norm_toLp y) n

private lemma mul_smul_alg (r : ℂ) (x y : WienerAlgebra) : x * r • y = r • (x * y) := by
  ext n
  rw [apply_mul, apply_smul, apply_mul]
  have hfun : wienerConvolution (⇑x) (⇑(r • y)) n =
      wienerConvolution (⇑x) (fun k ↦ r * y k) n := by
    unfold wienerConvolution
    refine tsum_congr fun k ↦ ?_
    rw [apply_smul]
  rw [hfun]
  exact convolution_smul_right r (summable_norm_toLp x) (summable_norm_toLp y) n

private instance : NormedAlgebra ℂ WienerAlgebra := by
  letI : Module ℂ WienerAlgebra :=
    Function.Injective.module ℂ toLpAddHom (fun a b h ↦ toLp_injective h) fun _ _ ↦ rfl
  exact
    { Algebra.ofModule smul_mul_alg mul_smul_alg with
      norm_smul_le := fun r x ↦ by
        rw [norm_eq_toLp, norm_eq_toLp, toLp_smul]
        exact lp.norm_const_smul_le one_ne_zero r x.toLp }

/-- The standard basis sequence, equal to `1` at one integer index. -/
private def delta (n : ℤ) : WienerAlgebra := ⟨lp.single (E := fun _ : ℤ ↦ ℂ) 1 n 1⟩

private lemma delta_zero : delta 0 = 1 := rfl

private lemma coe_delta (n k : ℤ) : delta n k = if k = n then (1 : ℂ) else 0 := by
  unfold delta
  rw [lp.coeFn_single, Pi.single_apply]

private lemma norm_delta (n : ℤ) : ‖delta n‖ = 1 := by
  rw [norm_eq_toLp, delta, lp.norm_single ennreal_one_pos, norm_one]

private lemma delta_mul (m n : ℤ) : delta m * delta n = delta (m + n) := by
  ext k
  rw [apply_mul, wienerConvolution]
  have hzero : ∀ j, j ≠ m → delta m j * delta n (k - j) = 0 := by
    intro j hj
    rw [coe_delta, ite_eq_right hj, zero_mul]
  rw [tsum_eq_single m hzero, coe_delta, ite_eq_left rfl, one_mul, coe_delta, coe_delta]
  have hiff : k - m = n ↔ k = m + n := by
    constructor
    · intro h
      rw [← h]
      ring
    · intro h
      rw [h]
      ring
  by_cases hk : k = m + n
  · rw [ite_eq_left (hiff.2 hk), ite_eq_left hk]
  · rw [ite_eq_right (mt hiff.1 hk), ite_eq_right hk]

private lemma phi_delta (φ : characterSpace ℂ WienerAlgebra) (n : ℤ) :
    φ (delta n) = φ (delta 1) ^ n := by
  have hne : φ (delta 1) ≠ 0 := by
    intro h
    have hmul : φ (delta 1) * φ (delta (-1)) = 1 := by
      rw [← map_mul, delta_mul, show (1 : ℤ) + -1 = 0 by ring, delta_zero, map_one]
    rw [h, zero_mul] at hmul
    exact zero_ne_one hmul
  induction n using Int.induction_on with
  | zero =>
      rw [delta_zero, map_one, zpow_zero]
  | succ i ih =>
      rw [← delta_mul, map_mul, ih]
      exact (zpow_add_one₀ hne (i : ℤ)).symm
  | pred i ih =>
      have hmul : delta (-(i : ℤ) - 1) * delta 1 = delta (-(i : ℤ)) := by
        rw [delta_mul]
        congr 1
        ring
      have hmul' : φ (delta (-(i : ℤ) - 1)) * φ (delta 1) = φ (delta 1) ^ (-(i : ℤ)) := by
        rw [← map_mul, hmul, ih]
      apply mul_right_cancel₀ hne
      rw [hmul']
      rw [← zpow_add_one₀ hne (-(i : ℤ) - 1)]
      congr 1
      ring

private lemma norm_phi_delta_one (φ : characterSpace ℂ WienerAlgebra) : ‖φ (delta 1)‖ = 1 := by
  have hmul : ‖φ (delta 1)‖ * ‖φ (delta (-1))‖ = 1 := by
    rw [← norm_mul, ← map_mul, delta_mul, show (1 : ℤ) + -1 = 0 by ring, delta_zero, map_one,
      norm_one]
  have h1 : ‖φ (delta 1)‖ ≤ 1 := by
    simpa [norm_delta] using AlgHom.norm_apply_le_self φ (delta 1)
  have h2 : ‖φ (delta (-1))‖ ≤ 1 := by
    simpa [norm_delta] using AlgHom.norm_apply_le_self φ (delta (-1))
  have hle : 1 ≤ ‖φ (delta 1)‖ := by
    have hmul_le := mul_le_mul_of_nonneg_left h2 (norm_nonneg (φ (delta 1)))
    rwa [hmul, mul_one] at hmul_le
  exact le_antisymm h1 hle

private def characterPoint (φ : characterSpace ℂ WienerAlgebra) : Circle :=
  ⟨φ (delta 1), mem_sphere_zero_iff_norm.2 (norm_phi_delta_one φ)⟩

private lemma coe_characterPoint (φ : characterSpace ℂ WienerAlgebra) :
    (characterPoint φ : ℂ) = φ (delta 1) := rfl

private lemma toLp_smul_delta (c : ℂ) (n : ℤ) :
    (c • delta n).toLp = lp.single (E := fun _ : ℤ ↦ ℂ) 1 n c := by
  rw [toLp_smul, delta, ← lp.single_smul]
  simp [smul_eq_mul, mul_one]

private lemma hasSum_smul_delta (a : WienerAlgebra) : HasSum (fun n : ℤ ↦ a n • delta n) a := by
  have hp : (1 : ENNReal) ≠ ⊤ := ENNReal.one_ne_top
  have hsum := lp.hasSum_single (E := fun _ : ℤ ↦ ℂ) hp a.toLp
  have hfun : ∀ s : Finset ℤ, toLpAddHom (∑ n ∈ s, a n • delta n) =
      ∑ n ∈ s, lp.single (E := fun _ : ℤ ↦ ℂ) 1 n (a n) := by
    intro s
    rw [map_sum]
    exact Finset.sum_congr rfl fun n _ ↦ toLp_smul_delta (a n) n
  unfold HasSum at hsum
  refine isometry_toLp.tendsto_nhds_iff.2 ?_
  refine Filter.Tendsto.congr
    (f₁ := fun s : Finset ℤ ↦ ∑ n ∈ s, lp.single (E := fun _ : ℤ ↦ ℂ) 1 n (a n))
    (f₂ := fun s : Finset ℤ ↦ (∑ n ∈ s, a n • delta n).toLp)
    ?_ hsum
  intro s
  exact (hfun s).symm.trans rfl

private lemma phi_coeff (φ : characterSpace ℂ WienerAlgebra) (c : ℂ) (n : ℤ) :
    φ (c • delta n) = c * (characterPoint φ : ℂ) ^ n := by
  rw [map_smul, phi_delta, smul_eq_mul, coe_characterPoint]

private lemma character_apply (φ : characterSpace ℂ WienerAlgebra) (a : WienerAlgebra) :
    φ a = wienerSeries a (characterPoint φ) := by
  have hsum := (CharacterSpace.toCLM φ).hasSum (hasSum_smul_delta a)
  have hpoint : φ a = ∑' n, a n * (characterPoint φ : ℂ) ^ n := by
    rw [← congrFun (CharacterSpace.coe_toCLM φ) a, ← hsum.tsum_eq]
    refine tsum_congr fun n ↦ ?_
    exact (congrFun (CharacterSpace.coe_toCLM φ) (a n • delta n)).trans (phi_coeff φ (a n) n)
  rw [wienerSeries]
  exact hpoint

private lemma seriesProduct {a b : ℤ → ℂ} (ha : Summable fun n ↦ ‖a n‖)
    (hb : Summable fun n ↦ ‖b n‖) {ζ : ℂ} (hζ : ζ ≠ 0) (hnζ : ‖ζ‖ = 1) :
    (∑' n, a n * ζ ^ n) * (∑' n, b n * ζ ^ n) =
      ∑' n, wienerConvolution a b n * ζ ^ n := by
  have hna : Summable fun n ↦ ‖a n * ζ ^ n‖ := by
    refine ha.congr fun n ↦ ?_
    rw [norm_mul, norm_zpow, hnζ, one_zpow, mul_one]
  have hnb : Summable fun n ↦ ‖b n * ζ ^ n‖ := by
    refine hb.congr fun n ↦ ?_
    rw [norm_mul, norm_zpow, hnζ, one_zpow, mul_one]
  rw [tsum_mul_tsum_of_summable_norm hna hnb]
  have hpoint : ∀ p : ℤ × ℤ,
      (a p.1 * ζ ^ p.1) * (b p.2 * ζ ^ p.2) = a p.1 * b p.2 * ζ ^ (p.1 + p.2) := by
    intro p
    rw [zpow_add₀ hζ p.1 p.2]
    ring
  rw [tsum_congr hpoint]
  rw [← indexShift.symm.tsum_eq fun p : ℤ × ℤ ↦ a p.1 * b p.2 * ζ ^ (p.1 + p.2)]
  have hshift_pt : ∀ p : ℤ × ℤ,
      a (indexShift.symm p).1 * b (indexShift.symm p).2 *
          ζ ^ ((indexShift.symm p).1 + (indexShift.symm p).2) =
        a p.1 * b (p.2 - p.1) * ζ ^ p.2 := by
    intro p
    rw [indexShift_symm_apply]
    have hadd : p.1 + (p.2 - p.1) = p.2 := by ring
    rw [hadd]
  rw [tsum_congr hshift_pt]
  let S : ℤ × ℤ → ℂ := fun p ↦ a p.1 * b (p.2 - p.1) * ζ ^ p.2
  have hS : Summable S := by
    refine Summable.of_norm ?_
    refine (summable_shiftNorm ha hb).congr fun p ↦ ?_
    rw [norm_mul, norm_mul, norm_zpow, hnζ, one_zpow, mul_one]
  rw [← (Equiv.prodComm ℤ ℤ).tsum_eq S]
  have hcomp : Summable fun p ↦ S (Equiv.prodComm ℤ ℤ p) :=
    ((Equiv.prodComm ℤ ℤ).summable_iff (f := S)).2 hS
  rw [hcomp.tsum_prod]
  refine tsum_congr fun n ↦ ?_
  unfold wienerConvolution
  have hfiber : ∀ c, S (Equiv.prodComm ℤ ℤ (n, c)) = (a c * b (n - c)) * ζ ^ n := by
    intro c
    rfl
  rw [tsum_congr hfiber, (summable_term ha hb n).tsum_mul_right (ζ ^ n)]

private lemma wienerSeries_mul {a b : ℤ → ℂ} (ha : Summable fun n ↦ ‖a n‖)
    (hb : Summable fun n ↦ ‖b n‖) (z : Circle) :
    wienerSeries a z * wienerSeries b z = wienerSeries (wienerConvolution a b) z := by
  rw [wienerSeries, wienerSeries, wienerSeries]
  exact seriesProduct ha hb (Circle.coe_ne_zero z) (Circle.norm_coe z)

private lemma wienerSeries_one (z : Circle) : wienerSeries (⇑(1 : WienerAlgebra)) z = 1 := by
  rw [wienerSeries]
  have hzero : ∀ n, n ≠ 0 → (1 : WienerAlgebra) n * (z : ℂ) ^ n = 0 := by
    intro n hn
    rw [apply_one, ite_eq_right hn, zero_mul]
  rw [tsum_eq_single 0 hzero, apply_one, ite_eq_left rfl, one_mul, zpow_zero]

/-- **20.40**, Wiener's `1/f` lemma: if `f` has an absolutely convergent bilateral Fourier series
on the unit circle and vanishes nowhere there, then `1/f` also has one. The coefficients of `1/f`
are those of the inverse of `f` in the Wiener algebra, which is a unit because every character of
that algebra is evaluation at a point of the circle. -/
theorem HasAbsolutelyConvergentFourierSeries.inv {f : Circle → ℂ}
    (hf : HasAbsolutelyConvergentFourierSeries f) (hzero : ∀ z, f z ≠ 0) :
    HasAbsolutelyConvergentFourierSeries (fun z ↦ (f z)⁻¹) := by
  obtain ⟨a, ha, rfl⟩ := hf
  let A : WienerAlgebra := ⟨⟨a, memℓp_of_summable ha⟩⟩
  have hA : ⇑A = a := rfl
  have hφ : ∀ φ : characterSpace ℂ WienerAlgebra, φ A ≠ 0 := by
    intro φ
    rw [character_apply, hA]
    exact hzero (characterPoint φ)
  have hunit : IsUnit A := by
    by_contra hnu
    obtain ⟨φ, hφ0⟩ := WeakDual.CharacterSpace.exists_apply_eq_zero hnu
    exact hφ φ hφ0
  let B : WienerAlgebra := ↑hunit.unit⁻¹
  have hAB : A * B = 1 := hunit.mul_val_inv
  refine ⟨⇑B, summable_norm_toLp B, ?_⟩
  ext z
  have hmul := wienerSeries_mul (summable_norm_toLp A) (summable_norm_toLp B) z
  have hcoe : wienerConvolution (⇑A) (⇑B) = ⇑(A * B) := rfl
  rw [hA, hcoe, hAB, wienerSeries_one] at hmul
  calc
    (wienerSeries a z)⁻¹ =
        (wienerSeries a z)⁻¹ * (wienerSeries a z * wienerSeries (⇑B) z) := by
      rw [hmul, mul_one]
    _ = wienerSeries (⇑B) z := by
      rw [← mul_assoc, inv_mul_cancel₀ (hzero z), one_mul]

end CKMA
