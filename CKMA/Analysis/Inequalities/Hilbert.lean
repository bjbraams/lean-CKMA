/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module


public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

import CKMA.Analysis.Inequalities.Hilbert.Kernel
import Mathlib.Analysis.PSeries

/-!
# Hilbert integral and sequence inequalities

Hilbert's bilinear inequality on the positive half-line and its sequence analogue,
with conjugate exponents and constant `pi / sin (pi / p)`. The discrete denominator
`m+n+2` corresponds to positive integers `m+1,n+1`. Nonnegative integrals and sums
preserve infinite values; the input norms use Mathlib's `MemLp` and `eLpNorm`.

The constant is the Beta integral `Beta(b, 1 - b)`, computed with the kernel estimates in
`CKMA.Analysis.Inequalities.Hilbert.Kernel`. The bilinear bound is Hölder's inequality in
`ENNReal`, and the sequence bound compares the decreasing kernel with that integral.

The constant is optimal in both forms. The test functions `x ^ (-1 / p)` and `y ^ (-1 / q)`
truncated to `(1, N)` (respectively the sequences `(m + 1) ^ (-1 / p)` and `(n + 1) ^ (-1 / q)`
for `m, n < N`) have norm product `log N` (respectively the harmonic sum `H_N`), while the
bilinear form is at least `π / sin (π / p)` times that quantity minus a bounded error.
Source: GAPS 11.37.

## Main definitions

* `CKMA.hilbertConstant`: Hilbert's sharp constant `π / sin (π / p)`. At `p = 1` the value is `0`;
  the inequalities assume `1 < p`.

## Main results

* `CKMA.hilbert_integral` (**11.37**): Hilbert's integral inequality on `(0, ∞)` for nonnegative
  functions, with nonnegative extended integrals.
* `CKMA.hilbert_tsum` (**11.37**): the discrete Hilbert inequality for sequences in `ℓ^p` and
  `ℓ^q`.
* `CKMA.hilbertConstant_le_of_hilbert_integral_le`,
  `CKMA.hilbertConstant_le_of_hilbert_tsum_le` (**11.37**): any admissible constant is at least
  `π / sin (π / p)`.
* `CKMA.isLeast_hilbertConstant_integral`, `CKMA.isLeast_hilbertConstant_tsum` (**11.37**):
  `π / sin (π / p)` is the least admissible constant in each form.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Set intervalIntegral Hilbert
open scoped ENNReal

/-- Hilbert's sharp constant `π / sin (π / p)`. At `p = 1` the sine in the denominator is `0`,
so the value is `0`; the inequalities assume `1 < p`. -/
@[expose]
def hilbertConstant (p : ℝ) : ℝ := Real.pi / Real.sin (Real.pi / p)

/-- Left Schur factor `f(x) (x / y) ^ (1 / (p q)) / (x + y) ^ (1 / p)`. -/
private def hilbertLeft (p q : ℝ) (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  if 0 < x ∧ 0 < y then
    f x * rpowPos (1 / (p * q)) (x / y) / rpowPos (1 / p) (x + y)
  else 0

/-- Right Schur factor `g(y) (y / x) ^ (1 / (p q)) / (x + y) ^ (1 / q)`. -/
private def hilbertRight (p q : ℝ) (g : ℝ → ℝ) (x y : ℝ) : ℝ :=
  if 0 < x ∧ 0 < y then
    g y * rpowPos (1 / (p * q)) (y / x) / rpowPos (1 / q) (x + y)
  else 0

/-- The left factor is nonnegative when `f` is. -/
private lemma hilbertLeft_nonneg {p q : ℝ} {f : ℝ → ℝ} {x y : ℝ} (hf : 0 ≤ f x) :
    0 ≤ hilbertLeft p q f x y := by
  unfold hilbertLeft
  split_ifs with h
  · exact div_nonneg (mul_nonneg hf (rpowPos_nonneg _ _)) (rpowPos_pos (by linarith [h.1, h.2])).le
  · exact le_rfl

/-- The right factor is nonnegative when `g` is. -/
private lemma hilbertRight_nonneg {p q : ℝ} {g : ℝ → ℝ} {x y : ℝ} (hg : 0 ≤ g y) :
    0 ≤ hilbertRight p q g x y := by
  unfold hilbertRight
  split_ifs with h
  · exact div_nonneg (mul_nonneg hg (rpowPos_nonneg _ _)) (rpowPos_pos (by linarith [h.1, h.2])).le
  · exact le_rfl

/-- Real form of the left factor on the positive quadrant. -/
private lemma hilbertLeft_eq {p q x y fx : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hilbertLeft p q (fun _ => fx) x y =
      fx * (x / y) ^ (1 / (p * q)) / (x + y) ^ (1 / p) := by
  have hxy : 0 < x / y := div_pos hx hy
  have hs : 0 < x + y := add_pos hx hy
  rw [hilbertLeft, ite_eq_left ⟨hx, hy⟩, rpowPos_eq hxy, rpowPos_eq hs]

/-- Real form of the right factor on the positive quadrant. -/
private lemma hilbertRight_eq {p q x y gy : ℝ} (hx : 0 < x) (hy : 0 < y) :
    hilbertRight p q (fun _ => gy) x y =
      gy * (y / x) ^ (1 / (p * q)) / (x + y) ^ (1 / q) := by
  have hyx : 0 < y / x := div_pos hy hx
  have hs : 0 < x + y := add_pos hx hy
  rw [hilbertRight, ite_eq_left ⟨hx, hy⟩, rpowPos_eq hyx, rpowPos_eq hs]

/-- The two Schur factors multiply back to the Hilbert kernel. -/
private lemma hilbertFactor_mul {p q : ℝ} (hpq : p.HolderConjugate q) {x y fx gy : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    hilbertLeft p q (fun _ => fx) x y * hilbertRight p q (fun _ => gy) x y =
      fx * gy / (x + y) := by
  have hs : 0 < x + y := add_pos hx hy
  have hxy : 0 < x / y := div_pos hx hy
  have hyx : 0 < y / x := div_pos hy hx
  rw [hilbertLeft_eq hx hy, hilbertRight_eq hx hy]
  have hprod : (x / y) ^ (1 / (p * q)) * (y / x) ^ (1 / (p * q)) = 1 := by
    rw [← Real.mul_rpow hxy.le hyx.le]
    have : (x / y) * (y / x) = 1 := by field_simp
    rw [this, Real.one_rpow]
  have hden : (x + y) ^ (1 / p) * (x + y) ^ (1 / q) = x + y := by
    rw [← Real.rpow_add hs]
    have hadd : (1 / p + 1 / q : ℝ) = 1 := by simpa [one_div] using hpq.inv_add_inv_eq_one
    rw [hadd, Real.rpow_one]
  calc
    (fx * (x / y) ^ (1 / (p * q)) / (x + y) ^ (1 / p)) *
        (gy * (y / x) ^ (1 / (p * q)) / (x + y) ^ (1 / q))
        = (fx * (x / y) ^ (1 / (p * q)) * (gy * (y / x) ^ (1 / (p * q)))) /
          ((x + y) ^ (1 / p) * (x + y) ^ (1 / q)) := by
            rw [div_mul_div_comm]
    _ = (fx * gy * ((x / y) ^ (1 / (p * q)) * (y / x) ^ (1 / (p * q)))) /
          ((x + y) ^ (1 / p) * (x + y) ^ (1 / q)) := by
            rw [mul_mul_mul_comm]
    _ = (fx * gy * 1) / (x + y) := by rw [hprod, hden]
    _ = fx * gy / (x + y) := by rw [mul_one]

/-- Raising the left factor to `p` recovers `f(x) ^ p` times the kernel of exponent `1 / q`. -/
private lemma hilbertLeft_pow {p q : ℝ} (hpq : p.HolderConjugate q) {x y fx : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hfx : 0 ≤ fx) :
    hilbertLeft p q (fun _ => fx) x y ^ p =
      fx ^ p * hilbertKernel x q⁻¹ y := by
  have hs : 0 < x + y := add_pos hx hy
  have hxy : 0 ≤ x / y := (div_pos hx hy).le
  rw [hilbertLeft_eq hx hy, hilbertKernel_eq hx hy]
  have hbase : 0 ≤ fx * (x / y) ^ (1 / (p * q)) :=
    mul_nonneg hfx (Real.rpow_nonneg hxy _)
  have hc : 0 ≤ (x + y) ^ (1 / p) := Real.rpow_nonneg hs.le _
  rw [Real.div_rpow hbase hc, Real.mul_rpow hfx (Real.rpow_nonneg hxy _)]
  rw [← Real.rpow_mul hxy, ← Real.rpow_mul hs.le]
  have hθ : 1 / (p * q) * p = q⁻¹ := by
    rw [one_div, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hpq.pos.ne', mul_one]
  have hp : (1 / p) * p = 1 := by field_simp [hpq.pos.ne']
  rw [hθ, hp, Real.rpow_one, mul_div_assoc]

/-- Raising the right factor to `q` recovers `g(y) ^ q` times the kernel of exponent `1 / p`. -/
private lemma hilbertRight_pow {p q : ℝ} (hpq : p.HolderConjugate q) {x y gy : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hgy : 0 ≤ gy) :
    hilbertRight p q (fun _ => gy) x y ^ q =
      gy ^ q * hilbertKernel y p⁻¹ x := by
  have hs : 0 < x + y := add_pos hx hy
  have hyx : 0 ≤ y / x := (div_pos hy hx).le
  rw [hilbertRight_eq hx hy, hilbertKernel_eq hy hx]
  have hbase : 0 ≤ gy * (y / x) ^ (1 / (p * q)) :=
    mul_nonneg hgy (Real.rpow_nonneg hyx _)
  have hc : 0 ≤ (x + y) ^ (1 / q) := Real.rpow_nonneg hs.le _
  rw [Real.div_rpow hbase hc, Real.mul_rpow hgy (Real.rpow_nonneg hyx _)]
  rw [← Real.rpow_mul hyx, ← Real.rpow_mul hs.le]
  have hθ : 1 / (p * q) * q = p⁻¹ := by
    rw [one_div, mul_inv_rev, mul_assoc, mul_left_comm q⁻¹ p⁻¹ q,
      inv_mul_cancel₀ hpq.symm.pos.ne', mul_one]
  have hq : (1 / q) * q = 1 := by field_simp [hpq.symm.pos.ne']
  rw [hθ, hq, Real.rpow_one, add_comm x y, mul_div_assoc]

/-- `ENNReal` form of the product of the two factors. -/
private lemma ofReal_hilbertFactor_mul {p q : ℝ} (hpq : p.HolderConjugate q) {x y fx gy : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hfx : 0 ≤ fx) :
    ENNReal.ofReal (hilbertLeft p q (fun _ => fx) x y) *
        ENNReal.ofReal (hilbertRight p q (fun _ => gy) x y) =
      ENNReal.ofReal (fx * gy / (x + y)) := by
  rw [← ENNReal.ofReal_mul (hilbertLeft_nonneg hfx), hilbertFactor_mul hpq hx hy]

/-- `ENNReal` form of the left factor raised to `p`. -/
private lemma ofReal_hilbertLeft_pow {p q : ℝ} (hpq : p.HolderConjugate q) {x y fx : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hfx : 0 ≤ fx) :
    ENNReal.ofReal (hilbertLeft p q (fun _ => fx) x y) ^ p =
      ENNReal.ofReal fx ^ p * ENNReal.ofReal (hilbertKernel x q⁻¹ y) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (hilbertLeft_nonneg hfx) hpq.pos.le,
    hilbertLeft_pow hpq hx hy hfx, ENNReal.ofReal_mul (Real.rpow_nonneg hfx _),
    ← ENNReal.ofReal_rpow_of_nonneg hfx hpq.pos.le]

/-- `ENNReal` form of the right factor raised to `q`. -/
private lemma ofReal_hilbertRight_pow {p q : ℝ} (hpq : p.HolderConjugate q) {x y gy : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hgy : 0 ≤ gy) :
    ENNReal.ofReal (hilbertRight p q (fun _ => gy) x y) ^ q =
      ENNReal.ofReal gy ^ q * ENNReal.ofReal (hilbertKernel y p⁻¹ x) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (hilbertRight_nonneg hgy) hpq.symm.pos.le,
    hilbertRight_pow hpq hx hy hgy, ENNReal.ofReal_mul (Real.rpow_nonneg hgy _),
    ← ENNReal.ofReal_rpow_of_nonneg hgy hpq.symm.pos.le]

/-- The left factor is jointly measurable when `f` is measurable. -/
private lemma measurable_hilbertLeft {p q : ℝ} {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (Function.uncurry (hilbertLeft p q f)) := by
  unfold hilbertLeft
  refine Measurable.ite ?_ ?_ measurable_const
  · have hs : {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2} = Ioi 0 ×ˢ Ioi 0 := by
      ext z
      simp
    rw [hs]
    exact measurableSet_Ioi.prod measurableSet_Ioi
  · exact (((hf.comp measurable_fst).mul ((measurable_rpowPos _).comp
      (measurable_fst.div measurable_snd))).div
      ((measurable_rpowPos _).comp (measurable_fst.add measurable_snd)))

/-- The right factor is jointly measurable when `g` is measurable. -/
private lemma measurable_hilbertRight {p q : ℝ} {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable (Function.uncurry (hilbertRight p q g)) := by
  unfold hilbertRight
  refine Measurable.ite ?_ ?_ measurable_const
  · have hs : {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2} = Ioi 0 ×ˢ Ioi 0 := by
      ext z
      simp
    rw [hs]
    exact measurableSet_Ioi.prod measurableSet_Ioi
  · exact (((hg.comp measurable_snd).mul ((measurable_rpowPos _).comp
      (measurable_snd.div measurable_fst))).div
      ((measurable_rpowPos _).comp (measurable_fst.add measurable_snd)))

/-- The nonnegative integrand `f(x) g(y) / (x + y)` is jointly measurable. -/
private lemma measurable_hilbert_integrand {f g : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun z : ℝ × ℝ => ENNReal.ofReal (f z.1 * g z.2 / (z.1 + z.2)) :=
  ENNReal.measurable_ofReal.comp <|
    ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).div
      (measurable_fst.add measurable_snd)

/-- Hilbert's constant is positive for `p > 1`. -/
private lemma hilbertConstant_pos {p : ℝ} (hp : 1 < p) : 0 < hilbertConstant p := by
  unfold hilbertConstant
  refine div_pos Real.pi_pos (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
  · exact div_pos Real.pi_pos (by linarith)
  · rw [div_lt_iff₀ (by linarith : (0 : ℝ) < p)]
    nlinarith [Real.pi_pos]

/-- `sin (π / q) = sin (π / p)` for the conjugate exponent. -/
private lemma sin_pi_conjExponent {p : ℝ} (hp : 1 < p) :
    Real.sin (Real.pi * (Real.conjExponent p)⁻¹) = Real.sin (Real.pi / p) := by
  have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp
  calc
    Real.sin (Real.pi * (Real.conjExponent p)⁻¹)
        = Real.sin (Real.pi * (1 - p⁻¹)) := by rw [← hpq.one_sub_inv]
    _ = Real.sin (Real.pi - Real.pi / p) := by
        rw [mul_sub, mul_one, ← div_eq_mul_inv]
    _ = Real.sin (Real.pi / p) := Real.sin_pi_sub _

/-- Inner integral of the left factor to the power `p`. -/
private lemma lintegral_hilbertLeft_pow {p q : ℝ} (hpq : p.HolderConjugate q) {x fx : ℝ}
    (hx : 0 < x) (hfx : 0 ≤ fx) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (hilbertLeft p q (fun _ => fx) x y) ^ p =
      ENNReal.ofReal fx ^ p * ENNReal.ofReal (hilbertConstant p) := by
  have hpoint : EqOn
      (fun y => ENNReal.ofReal (hilbertLeft p q (fun _ => fx) x y) ^ p)
      (fun y => ENNReal.ofReal fx ^ p * ENNReal.ofReal (hilbertKernel x q⁻¹ y))
      (Ioi (0 : ℝ)) := fun y hy => ofReal_hilbertLeft_pow hpq hx hy hfx
  rw [setLIntegral_congr_fun measurableSet_Ioi hpoint,
    lintegral_const_mul' _ _
      (ENNReal.rpow_ne_top_of_nonneg hpq.pos.le ENNReal.ofReal_ne_top),
    lintegral_hilbertKernel hx (inv_pos.mpr hpq.symm.pos)
      (inv_lt_one_of_one_lt₀ hpq.symm.lt)]
  congr 1
  unfold hilbertConstant
  rw [← hpq.conjExponent_eq, sin_pi_conjExponent hpq.lt]

/-- Inner integral of the right factor to the power `q`. -/
private lemma lintegral_hilbertRight_pow {p q : ℝ} (hpq : p.HolderConjugate q) {y gy : ℝ}
    (hy : 0 < y) (hgy : 0 ≤ gy) :
    ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (hilbertRight p q (fun _ => gy) x y) ^ q =
      ENNReal.ofReal gy ^ q * ENNReal.ofReal (hilbertConstant p) := by
  have hpoint : EqOn
      (fun x => ENNReal.ofReal (hilbertRight p q (fun _ => gy) x y) ^ q)
      (fun x => ENNReal.ofReal gy ^ q * ENNReal.ofReal (hilbertKernel y p⁻¹ x))
      (Ioi (0 : ℝ)) := fun x hx => ofReal_hilbertRight_pow hpq hx hy hgy
  rw [setLIntegral_congr_fun measurableSet_Ioi hpoint,
    lintegral_const_mul' _ _
      (ENNReal.rpow_ne_top_of_nonneg hpq.symm.pos.le ENNReal.ofReal_ne_top),
    lintegral_hilbertKernel hy (inv_pos.mpr hpq.pos) (inv_lt_one_of_one_lt₀ hpq.lt)]
  congr 1

/-- `(eLpNorm f p) ^ p` is the integral of `‖f‖ₑ ^ p` for a nonnegative measurable function. -/
private lemma lintegral_ofReal_rpow_eq_eLpNorm_rpow {α : Type*} [MeasurableSpace α]
    {p : ℝ} (hp : 1 < p) {f : α → ℝ} {μ : Measure α}
    (hf0 : ∀ x, 0 ≤ f x) (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ENNReal.ofReal (f x) ^ p ∂μ = eLpNorm f (ENNReal.ofReal p) μ ^ p := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp.le
  have hppos : 0 < p := lt_trans zero_lt_one hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hppos).ne'
      ENNReal.ofReal_ne_top hf, ENNReal.toReal_ofReal hp0]
  rw [show (1 / p : ℝ) = p⁻¹ from (inv_eq_one_div p).symm, ENNReal.rpow_inv_rpow hppos.ne']
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal (hf0 x)]

/-- Product of the normalized Schur integrals. -/
private lemma holder_schur_mul {c n m : ℝ≥0∞} {p q : ℝ}
    (hc0 : c ≠ 0) (hct : c ≠ ∞) (hp : 0 < p) (hq : 0 < q) (hpq : p⁻¹ + q⁻¹ = 1) :
    (c * n ^ p) ^ p⁻¹ * (c * m ^ q) ^ q⁻¹ = c * n * m := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp.le),
    ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hq.le),
    ENNReal.rpow_rpow_inv hp.ne', ENNReal.rpow_rpow_inv hq.ne']
  have hre : c ^ p⁻¹ * n * (c ^ q⁻¹ * m) = c ^ p⁻¹ * c ^ q⁻¹ * n * m := by
    calc
      c ^ p⁻¹ * n * (c ^ q⁻¹ * m)
          = c ^ p⁻¹ * (n * (c ^ q⁻¹ * m)) := mul_assoc _ _ _
      _ = c ^ p⁻¹ * (c ^ q⁻¹ * (n * m)) := congrArg (c ^ p⁻¹ * ·) (mul_left_comm _ _ _)
      _ = (c ^ p⁻¹ * c ^ q⁻¹) * (n * m) := (mul_assoc _ _ _).symm
      _ = (c ^ p⁻¹ * c ^ q⁻¹) * n * m := (mul_assoc _ _ _).symm
  rw [hre, ← ENNReal.rpow_add _ _ hc0 hct, hpq, ENNReal.rpow_one]

/-- Slice bounds `I x = ‖φ x‖ ^ r * c` integrate to `c * (eLpNorm φ r) ^ r`. -/
private lemma lintegral_schur_pow {ν : Measure ℝ} {φ : ℝ → ℝ} {r : ℝ} {c : ℝ≥0∞}
    {I : ℝ → ℝ≥0∞} (hr : 1 < r) (hφ0 : ∀ x, 0 ≤ φ x)
    (hφ : AEStronglyMeasurable φ ν) (hct : c ≠ ∞)
    (hinner : ∀ᵐ x ∂ν, I x = ENNReal.ofReal (φ x) ^ r * c) :
    ∫⁻ x, I x ∂ν = c * eLpNorm φ (ENNReal.ofReal r) ν ^ r := by
  rw [lintegral_congr_ae hinner, lintegral_mul_const' _ _ hct,
    lintegral_ofReal_rpow_eq_eLpNorm_rpow hr hφ0 hφ, mul_comm]

/-- **11.37**: Hilbert's integral inequality for nonnegative functions on the positive half-line.
The nonnegative integral avoids the totalized Bochner integral for infinite bilinear forms. -/
theorem hilbert_integral {p : ℝ} (hp : 1 < p) {f g : ℝ → ℝ}
    (hf0 : ∀ᵐ x ∂volume.restrict (Set.Ioi 0), 0 ≤ f x)
    (hg0 : ∀ᵐ x ∂volume.restrict (Set.Ioi 0), 0 ≤ g x)
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Set.Ioi 0)))
    (hg : MemLp g (ENNReal.ofReal (p / (p - 1))) (volume.restrict (Set.Ioi 0))) :
    (∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ y in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (f x * g y / (x + y))) ≤
      ENNReal.ofReal (hilbertConstant p) *
        eLpNorm f (ENNReal.ofReal p) (volume.restrict (Set.Ioi 0)) *
        eLpNorm g (ENNReal.ofReal (p / (p - 1))) (volume.restrict (Set.Ioi 0)) := by
  let ν : Measure ℝ := volume.restrict (Set.Ioi 0)
  have hf_ae : AEMeasurable f ν := hf.aemeasurable
  have hg_ae : AEMeasurable g ν := hg.aemeasurable
  let f2 : ℝ → ℝ := fun x => max (hf_ae.mk f x) 0
  let g2 : ℝ → ℝ := fun x => max (hg_ae.mk g x) 0
  have hf2m : Measurable f2 := (hf_ae.measurable_mk).max measurable_const
  have hg2m : Measurable g2 := (hg_ae.measurable_mk).max measurable_const
  have hf2nn : ∀ x, 0 ≤ f2 x := fun x => le_max_right _ _
  have hg2nn : ∀ x, 0 ≤ g2 x := fun x => le_max_right _ _
  have hf2ae : f2 =ᵐ[ν] f := by
    filter_upwards [hf_ae.ae_eq_mk, hf0] with x hx hx0
    simp only [f2]
    rw [← hx, max_eq_left hx0]
  have hg2ae : g2 =ᵐ[ν] g := by
    filter_upwards [hg_ae.ae_eq_mk, hg0] with x hx hx0
    simp only [g2]
    rw [← hx, max_eq_left hx0]
  have hint : ∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ y in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (f x * g y / (x + y)) =
      ∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ y in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (f2 x * g2 y / (x + y)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hf2ae] with x hx
    refine lintegral_congr_ae ?_
    filter_upwards [hg2ae] with y hy
    rw [hx, hy]
  rw [hint, eLpNorm_congr_ae hf2ae.symm, eLpNorm_congr_ae hg2ae.symm]
  let q : ℝ := Real.conjExponent p
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  let F : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (hilbertLeft p q f2 z.1 z.2)
  let G : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (hilbertRight p q g2 z.1 z.2)
  have hF : Measurable F := ENNReal.measurable_ofReal.comp (measurable_hilbertLeft hf2m)
  have hG : Measurable G := ENNReal.measurable_ofReal.comp (measurable_hilbertRight hg2m)
  have hprod : ∫⁻ z, (F * G) z ∂(ν.prod ν) =
      ∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ y in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (f2 x * g2 y / (x + y)) := by
    rw [lintegral_prod _ (hF.mul hG).aemeasurable]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hL : hilbertLeft p q f2 x y = hilbertLeft p q (fun _ => f2 x) x y := by
      unfold hilbertLeft
      rfl
    have hR : hilbertRight p q g2 x y = hilbertRight p q (fun _ => g2 y) x y := by
      unfold hilbertRight
      rfl
    rw [Pi.mul_apply]
    dsimp only [F, G]
    rw [hL, hR]
    exact ofReal_hilbertFactor_mul hpq hx hy (hf2nn x)
  have hc0 : ENNReal.ofReal (hilbertConstant p) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (hilbertConstant_pos hp)).ne'
  have hct : ENNReal.ofReal (hilbertConstant p) ≠ ∞ := ENNReal.ofReal_ne_top
  have hFp : ∫⁻ z, F z ^ p ∂(ν.prod ν) =
      ENNReal.ofReal (hilbertConstant p) *
        eLpNorm f2 (ENNReal.ofReal p) ν ^ p := by
    rw [lintegral_prod _ (hF.pow_const p).aemeasurable]
    refine lintegral_schur_pow hp hf2nn
      (hf2m.aestronglyMeasurable.mono_measure Measure.restrict_le_self) hct ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hpoint : ∫⁻ y, F (x, y) ^ p ∂ν =
        ∫⁻ y, ENNReal.ofReal (hilbertLeft p q (fun _ => f2 x) x y) ^ p ∂ν := by
      refine lintegral_congr fun y => ?_
      simp only [F]
      unfold hilbertLeft
      rfl
    rw [hpoint]
    exact lintegral_hilbertLeft_pow hpq hx (hf2nn x)
  have hGq : ∫⁻ z, G z ^ q ∂(ν.prod ν) =
      ENNReal.ofReal (hilbertConstant p) *
        eLpNorm g2 (ENNReal.ofReal q) ν ^ q := by
    rw [lintegral_prod_symm (fun z => G z ^ q) (hG.pow_const q).aemeasurable]
    refine lintegral_schur_pow hpq.symm.lt hg2nn
      (hg2m.aestronglyMeasurable.mono_measure Measure.restrict_le_self) hct ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hpoint : ∫⁻ x, G (x, y) ^ q ∂ν =
        ∫⁻ x, ENNReal.ofReal (hilbertRight p q (fun _ => g2 y) x y) ^ q ∂ν := by
      refine lintegral_congr fun x => ?_
      simp only [G]
      unfold hilbertRight
      rfl
    rw [hpoint]
    exact lintegral_hilbertRight_pow hpq hy (hg2nn y)
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq (ν.prod ν) hpq
    hF.aemeasurable hG.aemeasurable
  rw [hprod] at hHolder
  refine hHolder.trans ?_
  rw [hFp, hGq]
  rw [show (1 / p : ℝ) = p⁻¹ from (inv_eq_one_div p).symm,
    show (1 / q : ℝ) = q⁻¹ from (inv_eq_one_div q).symm,
    holder_schur_mul hc0 hct hpq.pos hpq.symm.pos hpq.inv_add_inv_eq_one]
  have hqexp : q = p / (p - 1) := by
    unfold q
    rfl
  rw [hqexp]

/-- Positive-integer samples of the kernel are at most Hilbert's constant. -/
private lemma tsum_hilbertKernel_le_hilbertConstant {p : ℝ} {k α : ℝ}
    (hk : 0 < k) (hα0 : 0 < α) (hα1 : α < 1)
    (hsin : Real.sin (Real.pi * α) = Real.sin (Real.pi / p)) :
    ∑' n : ℕ, ENNReal.ofReal (hilbertKernel k α (n + 1)) ≤
      ENNReal.ofReal (hilbertConstant p) := by
  refine (tsum_hilbertKernel_le hk hα0 hα1).trans_eq ?_
  unfold hilbertConstant
  rw [hsin]

/-- The discrete Hilbert inequality; indices `m,n : ℕ` represent the positive integers `m+1,n+1`. -/
theorem hilbert_tsum {p : ℝ} (hp : 1 < p) {a b : ℕ → ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n)
    (ha : MemLp a (ENNReal.ofReal p) Measure.count)
    (hb : MemLp b (ENNReal.ofReal (p / (p - 1))) Measure.count) :
    (∑' m, ∑' n, ENNReal.ofReal (a m * b n / (m + n + 2 : ℝ))) ≤
      ENNReal.ofReal (hilbertConstant p) * eLpNorm a (ENNReal.ofReal p) Measure.count *
        eLpNorm b (ENNReal.ofReal (p / (p - 1))) Measure.count := by
  let q : ℝ := Real.conjExponent p
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  let ι : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hpos : ∀ n : ℕ, 0 < ι n := fun n =>
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
  have hcast : ∀ m n : ℕ, ι m + ι n = (m + n + 2 : ℝ) := fun m n => by
    simp only [ι]
    calc
      (m : ℝ) + 1 + ((n : ℝ) + 1) = (m : ℝ) + (n : ℝ) + (1 + 1) := add_add_add_comm _ _ _ _
      _ = ((m + n : ℕ) : ℝ) + 2 := by rw [← Nat.cast_add, one_add_one_eq_two]
      _ = (m + n + 2 : ℝ) := by rw [← Nat.cast_add]
  let μ : Measure (ℕ × ℕ) := Measure.count.prod Measure.count
  let F : ℕ × ℕ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (hilbertLeft p q (fun _ => a z.1) (ι z.1) (ι z.2))
  let G : ℕ × ℕ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (hilbertRight p q (fun _ => b z.2) (ι z.1) (ι z.2))
  have hF : Measurable F := Measurable.of_discrete
  have hG : Measurable G := Measurable.of_discrete
  have hc0 : ENNReal.ofReal (hilbertConstant p) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (hilbertConstant_pos hp)).ne'
  have hct : ENNReal.ofReal (hilbertConstant p) ≠ ∞ := ENNReal.ofReal_ne_top
  have hprod : ∫⁻ z, (F * G) z ∂μ =
      ∑' m, ∑' n, ENNReal.ofReal (a m * b n / (m + n + 2 : ℝ)) := by
    rw [lintegral_prod _ (hF.mul hG).aemeasurable]
    simp_rw [lintegral_count]
    refine tsum_congr fun m => tsum_congr fun n => ?_
    rw [Pi.mul_apply, ofReal_hilbertFactor_mul hpq (hpos m) (hpos n) (ha0 m), hcast m n]
  have hLeft : ∀ m, ∑' n, ENNReal.ofReal (hilbertKernel (ι m) q⁻¹ (ι n)) ≤
      ENNReal.ofReal (hilbertConstant p) := fun m => by
    simpa [ι] using tsum_hilbertKernel_le_hilbertConstant (hpos m)
      (inv_pos.mpr hpq.symm.pos) (inv_lt_one_of_one_lt₀ hpq.symm.lt)
      (sin_pi_conjExponent hp)
  have hRight : ∀ n, ∑' m, ENNReal.ofReal (hilbertKernel (ι n) p⁻¹ (ι m)) ≤
      ENNReal.ofReal (hilbertConstant p) := fun n => by
    simpa [ι] using tsum_hilbertKernel_le_hilbertConstant (hpos n)
      (inv_pos.mpr hpq.pos) (inv_lt_one_of_one_lt₀ hpq.lt) (by rw [← div_eq_mul_inv])
  have hFp : ∫⁻ z, F z ^ p ∂μ ≤
      ENNReal.ofReal (hilbertConstant p) *
        eLpNorm a (ENNReal.ofReal p) Measure.count ^ p := by
    rw [lintegral_prod _ (hF.pow_const p).aemeasurable]
    simp_rw [lintegral_count]
    have hinner : ∀ m, ∑' n, F (m, n) ^ p ≤
        ENNReal.ofReal (a m) ^ p * ENNReal.ofReal (hilbertConstant p) := by
      intro m
      have hpoint : ∀ n, F (m, n) ^ p =
          ENNReal.ofReal (a m) ^ p *
            ENNReal.ofReal (hilbertKernel (ι m) q⁻¹ (ι n)) := fun n => by
        simpa [F] using ofReal_hilbertLeft_pow hpq (hpos m) (hpos n) (ha0 m)
      simp_rw [hpoint, ENNReal.tsum_mul_left]
      exact mul_le_mul_right (hLeft m) _
    refine (ENNReal.tsum_le_tsum hinner).trans_eq ?_
    rw [ENNReal.tsum_mul_right, ← lintegral_count,
      lintegral_ofReal_rpow_eq_eLpNorm_rpow hp ha0 ha.aestronglyMeasurable, mul_comm]
  have hGq : ∫⁻ z, G z ^ q ∂μ ≤
      ENNReal.ofReal (hilbertConstant p) *
        eLpNorm b (ENNReal.ofReal q) Measure.count ^ q := by
    rw [lintegral_prod_symm (fun z => G z ^ q) (hG.pow_const q).aemeasurable]
    simp_rw [lintegral_count]
    have hinner : ∀ n, ∑' m, G (m, n) ^ q ≤
        ENNReal.ofReal (b n) ^ q * ENNReal.ofReal (hilbertConstant p) := by
      intro n
      have hpoint : ∀ m, G (m, n) ^ q =
          ENNReal.ofReal (b n) ^ q *
            ENNReal.ofReal (hilbertKernel (ι n) p⁻¹ (ι m)) := fun m => by
        simpa [G] using ofReal_hilbertRight_pow hpq (hpos m) (hpos n) (hb0 n)
      simp_rw [hpoint, ENNReal.tsum_mul_left]
      exact mul_le_mul_right (hRight n) _
    refine (ENNReal.tsum_le_tsum hinner).trans_eq ?_
    rw [ENNReal.tsum_mul_right, ← lintegral_count,
      lintegral_ofReal_rpow_eq_eLpNorm_rpow hpq.symm.lt hb0 hb.aestronglyMeasurable, mul_comm]
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hF.aemeasurable hG.aemeasurable
  rw [hprod] at hHolder
  refine hHolder.trans ?_
  refine (mul_le_mul' (ENNReal.rpow_le_rpow hFp hpq.one_div_nonneg)
      (ENNReal.rpow_le_rpow hGq hpq.symm.one_div_nonneg)).trans_eq ?_
  rw [show (1 / p : ℝ) = p⁻¹ from (inv_eq_one_div p).symm,
    show (1 / q : ℝ) = q⁻¹ from (inv_eq_one_div q).symm]
  rw [holder_schur_mul hc0 hct hpq.pos hpq.symm.pos hpq.inv_add_inv_eq_one]
  have hqexp : q = p / (p - 1) := by
    unfold q
    rfl
  rw [hqexp]

/-! ### Optimality of the constant -/

/-- `L^r` norm of a nonnegative function as the `r`-th root of the integral of its power. -/
private lemma eLpNorm_eq_lintegral_rpow_inv {α : Type*} [MeasurableSpace α] {r : ℝ}
    (hr : 1 < r) {f : α → ℝ} {μ : Measure α} (hf0 : ∀ x, 0 ≤ f x)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (ENNReal.ofReal r) μ = (∫⁻ x, ENNReal.ofReal (f x) ^ r ∂μ) ^ r⁻¹ := by
  rw [lintegral_ofReal_rpow_eq_eLpNorm_rpow hr hf0 hf,
    ENNReal.rpow_rpow_inv (zero_lt_one.trans hr).ne']

/-- `L ^ (1 / p) * L ^ (1 / q) = L` for conjugate exponents and finite nonzero `L`. -/
private lemma rpow_inv_mul_rpow_inv {L : ℝ≥0∞} {p q : ℝ} (hpq : p⁻¹ + q⁻¹ = 1)
    (h0 : L ≠ 0) (ht : L ≠ ⊤) : L ^ p⁻¹ * L ^ q⁻¹ = L := by
  rw [← ENNReal.rpow_add _ _ h0 ht, hpq, ENNReal.rpow_one]

/-- A power `x ^ e` raised to `r` with `e r = -1` is `x⁻¹`. -/
private lemma ofReal_rpow_rpow_eq_inv {x e r : ℝ} (hx : 0 < x) (hr : 0 ≤ r)
    (her : e * r = -1) : ENNReal.ofReal (x ^ e) ^ r = ENNReal.ofReal x⁻¹ := by
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hx.le _) hr, ← Real.rpow_mul hx.le, her,
    Real.rpow_neg_one]

/-- Sine form of Hilbert's constant at the conjugate weight `a = 1 - 1 / p`. -/
private lemma hilbertConstant_eq_conj (p : ℝ) :
    hilbertConstant p = Real.pi / Real.sin (Real.pi * (1 - p⁻¹)) := by
  rw [hilbertConstant, mul_sub, mul_one, ← div_eq_mul_inv, Real.sin_pi_sub]

/-! #### The integral inequality -/

/-- The open interval `(1, N)` lies in the positive half-line. -/
private lemma Ioo_one_subset_Ioi_zero {N : ℝ} : Ioo (1 : ℝ) N ⊆ Ioi 0 :=
  fun _ hx => zero_lt_one.trans hx.1

/-- Truncated power `x ^ e` on `(1, N)`, the test function for the integral optimality. -/
private def hilbertTest (N e : ℝ) : ℝ → ℝ := (Ioo 1 N).indicator fun x => x ^ e

/-- The truncated power test function is nonnegative. -/
private lemma hilbertTest_nonneg (N e x : ℝ) : 0 ≤ hilbertTest N e x :=
  Set.indicator_nonneg (fun _ hy => Real.rpow_nonneg (Ioo_one_subset_Ioi_zero hy).le _) x

/-- The truncated power test function is measurable. -/
private lemma measurable_hilbertTest (N e : ℝ) : Measurable (hilbertTest N e) :=
  (measurable_id.pow_const e).indicator measurableSet_Ioo

/-- The `L^r` norm of the test function with `e r = -1`. -/
private lemma eLpNorm_hilbertTest {N e r : ℝ} (hr : 1 < r) (her : e * r = -1) :
    eLpNorm (hilbertTest N e) (ENNReal.ofReal r) (volume.restrict (Ioi 0)) =
      (∫⁻ x in Ioo 1 N, ENNReal.ofReal x⁻¹) ^ r⁻¹ := by
  rw [eLpNorm_eq_lintegral_rpow_inv hr (hilbertTest_nonneg N e)
    (measurable_hilbertTest N e).aestronglyMeasurable]
  congr 1
  have hpt : EqOn (fun x => ENNReal.ofReal (hilbertTest N e x) ^ r)
      ((Ioo 1 N).indicator fun x => ENNReal.ofReal x⁻¹) (Ioi 0) := by
    intro x hx
    by_cases hxS : x ∈ Ioo (1 : ℝ) N
    · simp only [hilbertTest, indicator_of_mem hxS]
      exact ofReal_rpow_rpow_eq_inv hx (by linarith) her
    · simp only [hilbertTest, indicator_of_notMem hxS, ENNReal.ofReal_zero]
      exact ENNReal.zero_rpow_of_pos (by linarith)
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, setLIntegral_indicator measurableSet_Ioo,
    inter_eq_left.mpr Ioo_one_subset_Ioi_zero]

/-- The inner integral of the test integrand. -/
private lemma lintegral_hilbertTest_inner {a N x : ℝ} (hx : 0 < x) :
    ∫⁻ y in Ioi (0 : ℝ),
        ENNReal.ofReal (hilbertTest N (a - 1) x * hilbertTest N (-a) y / (x + y)) =
      (Ioo 1 N).indicator (fun x => ENNReal.ofReal x⁻¹ *
        ∫⁻ y in Ioo 1 N, ENNReal.ofReal (hilbertKernel x a y)) x := by
  by_cases hxS : x ∈ Ioo (1 : ℝ) N
  · rw [indicator_of_mem hxS]
    have hpt : EqOn
        (fun y => ENNReal.ofReal (hilbertTest N (a - 1) x * hilbertTest N (-a) y / (x + y)))
        ((Ioo 1 N).indicator fun y =>
          ENNReal.ofReal x⁻¹ * ENNReal.ofReal (hilbertKernel x a y)) (Ioi 0) := by
      intro y hy
      by_cases hyS : y ∈ Ioo (1 : ℝ) N
      · simp only [hilbertTest, indicator_of_mem hxS, indicator_of_mem hyS]
        rw [rpow_mul_rpow_div_eq hx hy, ENNReal.ofReal_mul (inv_nonneg.mpr hx.le)]
      · simp [hilbertTest, indicator_of_notMem hyS]
    rw [setLIntegral_congr_fun measurableSet_Ioi hpt, setLIntegral_indicator measurableSet_Ioo,
      inter_eq_left.mpr Ioo_one_subset_Ioi_zero,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  · simp [hilbertTest, indicator_of_notMem hxS]

/-- Lower bound for the bilinear form of the truncated power test functions. -/
private lemma hilbert_integral_lower {a N : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hN : 1 < N) :
    ENNReal.ofReal (Real.pi / Real.sin (Real.pi * a)) *
        ∫⁻ x in Ioo 1 N, ENNReal.ofReal x⁻¹ ≤
      (∫⁻ x in Ioi (0 : ℝ), ∫⁻ y in Ioi (0 : ℝ),
          ENNReal.ofReal (hilbertTest N (a - 1) x * hilbertTest N (-a) y / (x + y))) +
        (ENNReal.ofReal (-1 / (a - 1)) * ENNReal.ofReal (1 - a)⁻¹ +
          ENNReal.ofReal (1 / (a * a))) := by
  have hN0 : 0 < N := zero_lt_one.trans hN
  set c : ℝ := N ^ (-a) / a with hc
  have hI : (∫⁻ x in Ioi (0 : ℝ), ∫⁻ y in Ioi (0 : ℝ),
        ENNReal.ofReal (hilbertTest N (a - 1) x * hilbertTest N (-a) y / (x + y))) =
      ∫⁻ x in Ioo 1 N, ENNReal.ofReal x⁻¹ *
        ∫⁻ y in Ioo 1 N, ENNReal.ofReal (hilbertKernel x a y) := by
    rw [setLIntegral_congr_fun measurableSet_Ioi fun x hx => lintegral_hilbertTest_inner hx,
      setLIntegral_indicator measurableSet_Ioo,
      inter_eq_left.mpr Ioo_one_subset_Ioi_zero]
  have htail_meas : Measurable fun x : ℝ => ENNReal.ofReal (x ^ (a - 2)) *
      ENNReal.ofReal (1 - a)⁻¹ + ENNReal.ofReal (x ^ (a - 1)) * ENNReal.ofReal c := by
    fun_prop
  have hE1 : ∫⁻ x in Ioo 1 N, ENNReal.ofReal (x ^ (a - 2)) * ENNReal.ofReal (1 - a)⁻¹ ≤
      ENNReal.ofReal (-1 / (a - 1)) * ENNReal.ofReal (1 - a)⁻¹ := by
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    refine mul_le_mul_left ((lintegral_mono_set Ioo_subset_Ioi_self).trans_eq ?_) _
    rw [lintegral_Ioi_rpow (by linarith) one_pos, Real.one_rpow, show a - 2 + 1 = a - 1 by ring]
  have hE2 : ∫⁻ x in Ioo 1 N, ENNReal.ofReal (x ^ (a - 1)) * ENNReal.ofReal c ≤
      ENNReal.ofReal (1 / (a * a)) := by
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    calc (∫⁻ x in Ioo 1 N, ENNReal.ofReal (x ^ (a - 1))) * ENNReal.ofReal c
        ≤ (∫⁻ x in Ioc 0 N, ENNReal.ofReal (x ^ (a - 1))) * ENNReal.ofReal c :=
          mul_le_mul_left (lintegral_mono_set (show Ioo (1 : ℝ) N ⊆ Ioc 0 N from
            fun x hx => ⟨zero_lt_one.trans hx.1, hx.2.le⟩)) _
      _ = ENNReal.ofReal (1 / (a * a)) := by
          rw [lintegral_Ioc_rpow (by linarith) hN0, show a - 1 + 1 = a by ring,
            ← ENNReal.ofReal_mul (by positivity), hc, Real.rpow_neg hN0.le]
          congr 1
          field_simp
  calc ENNReal.ofReal (Real.pi / Real.sin (Real.pi * a)) *
        ∫⁻ x in Ioo 1 N, ENNReal.ofReal x⁻¹
      = ∫⁻ x in Ioo 1 N, ENNReal.ofReal x⁻¹ * ENNReal.ofReal
          (Real.pi / Real.sin (Real.pi * a)) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]
    _ ≤ ∫⁻ x in Ioo 1 N, (ENNReal.ofReal x⁻¹ *
          ∫⁻ y in Ioo 1 N, ENNReal.ofReal (hilbertKernel x a y)) +
          (ENNReal.ofReal (x ^ (a - 2)) * ENNReal.ofReal (1 - a)⁻¹ +
            ENNReal.ofReal (x ^ (a - 1)) * ENNReal.ofReal c) := by
        refine setLIntegral_mono' measurableSet_Ioo fun x hx => ?_
        have hx0 : 0 < x := zero_lt_one.trans hx.1
        rw [← ofReal_inv_mul_tail hx0, ← mul_add]
        exact mul_le_mul_right (ofReal_pi_div_sin_le_lintegral_Ioo ha0 ha1 hx0 hN0) _
    _ = _ := lintegral_add_right _ htail_meas
    _ ≤ _ := by
        rw [hI]
        refine add_le_add le_rfl ?_
        rw [lintegral_add_left (by fun_prop)]
        exact add_le_add hE1 hE2

/-- For `1 < p`, the weight `a = 1 - p⁻¹` and the conjugate `q = p / (p - 1)` satisfy
`0 < a < 1`, `1 < q`, `p⁻¹ + q⁻¹ = 1`, `(a - 1) * p = -1` and `(-a) * q = -1`. -/
private lemma hilbertConjFacts {p : ℝ} (hp : 1 < p) :
    0 < 1 - p⁻¹ ∧ 1 - p⁻¹ < 1 ∧ 1 < p / (p - 1) ∧
      p⁻¹ + (p / (p - 1))⁻¹ = 1 ∧
      ((1 - p⁻¹) - 1) * p = -1 ∧
      (-(1 - p⁻¹)) * (p / (p - 1)) = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith [inv_lt_one_of_one_lt₀ hp]
  · linarith [inv_pos.mpr (zero_lt_one.trans hp)]
  · rw [lt_div_iff₀ (by linarith : (0 : ℝ) < p - 1)]
    linarith
  · rw [inv_div]
    field_simp
    ring
  · field_simp
    ring
  · rw [neg_mul]
    field_simp

/-- **11.37** (optimality, integral form): no constant smaller than `π / sin (π / p)` bounds
Hilbert's bilinear form on `(0, ∞)`. -/
theorem hilbertConstant_le_of_hilbert_integral_le {p : ℝ} (hp : 1 < p) {C : ℝ≥0∞}
    (hC : ∀ f g : ℝ → ℝ, (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ g x) →
      MemLp f (ENNReal.ofReal p) (volume.restrict (Ioi 0)) →
      MemLp g (ENNReal.ofReal (p / (p - 1))) (volume.restrict (Ioi 0)) →
      (∫⁻ x in Ioi (0 : ℝ), ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (f x * g y / (x + y))) ≤
        C * eLpNorm f (ENNReal.ofReal p) (volume.restrict (Ioi 0)) *
          eLpNorm g (ENNReal.ofReal (p / (p - 1))) (volume.restrict (Ioi 0))) :
    ENNReal.ofReal (hilbertConstant p) ≤ C := by
  obtain ⟨ha0, ha1, hq1, hpq, hep, heq⟩ := hilbertConjFacts hp
  set a : ℝ := 1 - p⁻¹
  set q : ℝ := p / (p - 1)
  rw [hilbertConstant_eq_conj]
  refine le_of_forall_nat_le_mul_le (d := ENNReal.ofReal (-1 / (a - 1)) *
      ENNReal.ofReal (1 - a)⁻¹ + ENNReal.ofReal (1 / (a * a)))
    (by finiteness) fun n => ?_
  set N : ℝ := Real.exp (n + 1) with hN
  have hN1 : 1 < N := Real.one_lt_exp_iff.mpr (by positivity)
  have hL : ∫⁻ x in Ioo 1 N, ENNReal.ofReal x⁻¹ = ENNReal.ofReal (n + 1) := by
    rw [lintegral_Ioo_inv hN1, hN, Real.log_exp]
  set L := ∫⁻ x in Ioo 1 N, ENNReal.ofReal x⁻¹ with hLdef
  have hL0 : L ≠ 0 := by rw [hL]; exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hLt : L ≠ ⊤ := by rw [hL]; exact ENNReal.ofReal_ne_top
  refine ⟨L, ?_, hLt, ?_⟩
  · rw [hL, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hnF := eLpNorm_hilbertTest (N := N) hp hep
  have hnG := eLpNorm_hilbertTest (N := N) hq1 heq
  have hmF : MemLp (hilbertTest N (a - 1)) (ENNReal.ofReal p) (volume.restrict (Ioi 0)) :=
    by rw [memLp_iff, hnF]; exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hLt
  have hmG : MemLp (hilbertTest N (-a)) (ENNReal.ofReal q) (volume.restrict (Ioi 0)) :=
    by rw [memLp_iff, hnG]; exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hLt
  have hbound := hC _ _ (hilbertTest_nonneg N _) (hilbertTest_nonneg N _) hmF hmG
  rw [hnF, hnG, mul_assoc, rpow_inv_mul_rpow_inv hpq hL0 hLt] at hbound
  exact (hilbert_integral_lower ha0 ha1 hN1).trans (add_le_add hbound le_rfl)

/-! #### The sequence inequality -/

/-- Truncated power sequence `(m + 1) ^ e` for `m < N`, the test sequence for the discrete
optimality. -/
private def hilbertSeq (N : ℕ) (e : ℝ) (m : ℕ) : ℝ := if m < N then ((m : ℝ) + 1) ^ e else 0

/-- The truncated power test sequence is nonnegative. -/
private lemma hilbertSeq_nonneg (N : ℕ) (e : ℝ) (m : ℕ) : 0 ≤ hilbertSeq N e m := by
  unfold hilbertSeq
  split_ifs
  · positivity
  · exact le_rfl

/-- The `ℓ^r` norm of the test sequence with `e r = -1`. -/
private lemma eLpNorm_hilbertSeq {N : ℕ} {e r : ℝ} (hr : 1 < r) (her : e * r = -1) :
    eLpNorm (hilbertSeq N e) (ENNReal.ofReal r) Measure.count =
      (∑ m ∈ Finset.range N, ENNReal.ofReal ((m : ℝ) + 1)⁻¹) ^ r⁻¹ := by
  rw [eLpNorm_eq_lintegral_rpow_inv hr (hilbertSeq_nonneg N e)
    Measurable.of_discrete.aestronglyMeasurable, lintegral_count]
  congr 1
  rw [tsum_eq_sum (s := Finset.range N) fun m hm => by
    simp only [hilbertSeq, show ¬m < N by simpa using hm, ↓reduceIte, ENNReal.ofReal_zero]
    exact ENNReal.zero_rpow_of_pos (by linarith)]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [hilbertSeq, Finset.mem_range.mp hm, ↓reduceIte]
  exact ofReal_rpow_rpow_eq_inv (by positivity) (by linarith) her

/-- The bilinear form of the test sequences, as a finite double sum. -/
private lemma tsum_hilbertSeq {N : ℕ} {a : ℝ} :
    ∑' m, ∑' n, ENNReal.ofReal
        (hilbertSeq N (a - 1) m * hilbertSeq N (-a) n / (m + n + 2 : ℝ)) =
      ∑ m ∈ Finset.range N, ENNReal.ofReal ((m : ℝ) + 1)⁻¹ *
        ∑ n ∈ Finset.range N, ENNReal.ofReal (hilbertKernel ((m : ℝ) + 1) a ((n : ℝ) + 1)) := by
  calc ∑' m, ∑' n, ENNReal.ofReal
        (hilbertSeq N (a - 1) m * hilbertSeq N (-a) n / (m + n + 2 : ℝ))
      = ∑ m ∈ Finset.range N, ∑' n, ENNReal.ofReal
          (hilbertSeq N (a - 1) m * hilbertSeq N (-a) n / (m + n + 2 : ℝ)) :=
        tsum_eq_sum fun m hm => tsum_eq_zero_iff.mpr fun n => by
          simp [hilbertSeq, Finset.mem_range.not.mp hm]
    _ = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, ENNReal.ofReal
          (hilbertSeq N (a - 1) m * hilbertSeq N (-a) n / (m + n + 2 : ℝ)) :=
        Finset.sum_congr rfl fun m _ => tsum_eq_sum fun n hn => by
          simp [hilbertSeq, Finset.mem_range.not.mp hn]
    _ = _ := Finset.sum_congr rfl fun m hm => by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n hn => ?_
        simp only [hilbertSeq, Finset.mem_range.mp hm, Finset.mem_range.mp hn, ↓reduceIte]
        rw [show (m + n + 2 : ℝ) = ((m : ℝ) + 1) + ((n : ℝ) + 1) by ring,
          rpow_mul_rpow_div_eq (by positivity) (by positivity),
          ENNReal.ofReal_mul (by positivity)]

/-- Lower bound for the bilinear form of the truncated power test sequences. -/
private lemma hilbert_tsum_lower {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (N : ℕ) :
    ENNReal.ofReal (Real.pi / Real.sin (Real.pi * a)) *
        ∑ m ∈ Finset.range N, ENNReal.ofReal ((m : ℝ) + 1)⁻¹ ≤
      (∑' m, ∑' n, ENNReal.ofReal
          (hilbertSeq N (a - 1) m * hilbertSeq N (-a) n / (m + n + 2 : ℝ))) +
        ((∑' m : ℕ, ENNReal.ofReal (((m : ℝ) + 1) ^ (a - 2))) * ENNReal.ofReal (1 - a)⁻¹ +
          ENNReal.ofReal (1 / (a * a))) := by
  set M : ℝ := (N : ℝ) + 1 with hM
  have hM0 : 0 < M := by positivity
  set c : ℝ := M ^ (-a) / a with hc
  rw [tsum_hilbertSeq]
  have hanti : AntitoneOn (fun x : ℝ => ENNReal.ofReal (x ^ (a - 1))) (Ioi 0) :=
    fun x hx y _ hxy => ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hx hxy (by linarith))
  have hE1 : ∑ m ∈ Finset.range N,
      ENNReal.ofReal (((m : ℝ) + 1) ^ (a - 2)) * ENNReal.ofReal (1 - a)⁻¹ ≤
      (∑' m : ℕ, ENNReal.ofReal (((m : ℝ) + 1) ^ (a - 2))) * ENNReal.ofReal (1 - a)⁻¹ := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_left (sum_le_tsum _) _
  have hE2 : ∑ m ∈ Finset.range N,
      ENNReal.ofReal (((m : ℝ) + 1) ^ (a - 1)) * ENNReal.ofReal c ≤
      ENNReal.ofReal (1 / (a * a)) := by
    rw [← Finset.sum_mul]
    calc (∑ m ∈ Finset.range N, ENNReal.ofReal (((m : ℝ) + 1) ^ (a - 1))) * ENNReal.ofReal c
        ≤ (∫⁻ x in Ioc 0 M, ENNReal.ofReal (x ^ (a - 1))) * ENNReal.ofReal c :=
          mul_le_mul_left ((sum_le_lintegral_Ioc_of_antitoneOn hanti N).trans
            (lintegral_mono_set (Ioc_subset_Ioc_right (by linarith)))) _
      _ = ENNReal.ofReal (1 / (a * a)) := by
          rw [lintegral_Ioc_rpow (by linarith) hM0, show a - 1 + 1 = a by ring,
            ← ENNReal.ofReal_mul (by positivity), hc, Real.rpow_neg hM0.le]
          congr 1
          field_simp
  calc ENNReal.ofReal (Real.pi / Real.sin (Real.pi * a)) *
        ∑ m ∈ Finset.range N, ENNReal.ofReal ((m : ℝ) + 1)⁻¹
      = ∑ m ∈ Finset.range N, ENNReal.ofReal ((m : ℝ) + 1)⁻¹ *
          ENNReal.ofReal (Real.pi / Real.sin (Real.pi * a)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    _ ≤ ∑ m ∈ Finset.range N, (ENNReal.ofReal ((m : ℝ) + 1)⁻¹ *
          ∑ n ∈ Finset.range N, ENNReal.ofReal (hilbertKernel ((m : ℝ) + 1) a ((n : ℝ) + 1)) +
          (ENNReal.ofReal (((m : ℝ) + 1) ^ (a - 2)) * ENNReal.ofReal (1 - a)⁻¹ +
            ENNReal.ofReal (((m : ℝ) + 1) ^ (a - 1)) * ENNReal.ofReal c)) := by
        refine Finset.sum_le_sum fun m _ => ?_
        have hx0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
        have hrow := lintegral_Ioo_le_sum_of_antitoneOn (fun s hs t ht hst =>
          ENNReal.ofReal_le_ofReal (hilbertKernel_antitone hx0 ha0 hs ht hst)) N
        rw [← ofReal_inv_mul_tail hx0, ← mul_add]
        exact mul_le_mul_right ((ofReal_pi_div_sin_le_lintegral_Ioo ha0 ha1 hx0 hM0).trans
          (add_le_add hrow le_rfl)) _
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ _ := add_le_add le_rfl (add_le_add hE1 hE2)

/-- **11.37** (optimality, discrete form): no constant smaller than `π / sin (π / p)` bounds
the discrete Hilbert form with denominator `m + n + 2`. -/
theorem hilbertConstant_le_of_hilbert_tsum_le {p : ℝ} (hp : 1 < p) {C : ℝ≥0∞}
    (hC : ∀ u v : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, 0 ≤ v n) →
      MemLp u (ENNReal.ofReal p) Measure.count →
      MemLp v (ENNReal.ofReal (p / (p - 1))) Measure.count →
      (∑' m, ∑' n, ENNReal.ofReal (u m * v n / (m + n + 2 : ℝ))) ≤
        C * eLpNorm u (ENNReal.ofReal p) Measure.count *
          eLpNorm v (ENNReal.ofReal (p / (p - 1))) Measure.count) :
    ENNReal.ofReal (hilbertConstant p) ≤ C := by
  obtain ⟨ha0, ha1, hq1, hpq, hep, heq⟩ := hilbertConjFacts hp
  set a : ℝ := 1 - p⁻¹
  set q : ℝ := p / (p - 1)
  have hsum : Summable fun m : ℕ => ((m : ℝ) + 1) ^ (a - 2) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow.mpr (show a - 2 < -1 by linarith))
    exact_mod_cast h
  rw [hilbertConstant_eq_conj]
  refine le_of_forall_nat_le_mul_le (d := (∑' m : ℕ, ENNReal.ofReal (((m : ℝ) + 1) ^ (a - 2))) *
      ENNReal.ofReal (1 - a)⁻¹ + ENNReal.ofReal (1 / (a * a))) ?_ fun n => ?_
  · rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum]
    finiteness
  obtain ⟨N, hN⟩ := (Filter.tendsto_atTop.mp Real.tendsto_sum_range_one_div_nat_succ_atTop
    ((n : ℝ) + 1)).exists
  set H := ∑ m ∈ Finset.range N, ENNReal.ofReal ((m : ℝ) + 1)⁻¹ with hHdef
  have hH : H = ENNReal.ofReal (∑ m ∈ Finset.range N, 1 / ((m : ℝ) + 1)) := by
    rw [hHdef, ENNReal.ofReal_sum_of_nonneg fun m _ => by positivity]
    simp only [one_div]
  have hnH : ENNReal.ofReal ((n : ℝ) + 1) ≤ H := hH ▸ ENNReal.ofReal_le_ofReal hN
  have hH0 : H ≠ 0 := (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hnH).ne'
  have hHt : H ≠ ⊤ := by rw [hH]; exact ENNReal.ofReal_ne_top
  refine ⟨H, le_trans ?_ hnH, hHt, ?_⟩
  · rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hnu := eLpNorm_hilbertSeq (N := N) hp hep
  have hnv := eLpNorm_hilbertSeq (N := N) hq1 heq
  have hmu : MemLp (hilbertSeq N (a - 1)) (ENNReal.ofReal p) Measure.count := by
    rw [memLp_iff, hnu]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hHt
  have hmv : MemLp (hilbertSeq N (-a)) (ENNReal.ofReal q) Measure.count := by
    rw [memLp_iff, hnv]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hHt
  have hbound := hC _ _ (hilbertSeq_nonneg N _) (hilbertSeq_nonneg N _) hmu hmv
  rw [hnu, hnv, mul_assoc, rpow_inv_mul_rpow_inv hpq hH0 hHt] at hbound
  exact (hilbert_tsum_lower ha0 ha1 N).trans (add_le_add hbound le_rfl)

/-- **11.37**: `π / sin (π / p)` is the least constant in Hilbert's integral inequality. -/
theorem isLeast_hilbertConstant_integral {p : ℝ} (hp : 1 < p) :
    IsLeast {C : ℝ≥0∞ | ∀ f g : ℝ → ℝ,
      (∀ᵐ x ∂volume.restrict (Ioi 0), 0 ≤ f x) → (∀ᵐ x ∂volume.restrict (Ioi 0), 0 ≤ g x) →
      MemLp f (ENNReal.ofReal p) (volume.restrict (Ioi 0)) →
      MemLp g (ENNReal.ofReal (p / (p - 1))) (volume.restrict (Ioi 0)) →
      (∫⁻ x in Ioi (0 : ℝ), ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (f x * g y / (x + y))) ≤
        C * eLpNorm f (ENNReal.ofReal p) (volume.restrict (Ioi 0)) *
          eLpNorm g (ENNReal.ofReal (p / (p - 1))) (volume.restrict (Ioi 0))}
      (ENNReal.ofReal (hilbertConstant p)) :=
  ⟨fun _ _ hf0 hg0 hf hg => hilbert_integral hp hf0 hg0 hf hg,
    fun _ hC => hilbertConstant_le_of_hilbert_integral_le hp fun f g hf0 hg0 hf hg =>
      hC f g (ae_of_all _ hf0) (ae_of_all _ hg0) hf hg⟩

/-- **11.37**: `π / sin (π / p)` is the least constant in the discrete Hilbert inequality. -/
theorem isLeast_hilbertConstant_tsum {p : ℝ} (hp : 1 < p) :
    IsLeast {C : ℝ≥0∞ | ∀ u v : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, 0 ≤ v n) →
      MemLp u (ENNReal.ofReal p) Measure.count →
      MemLp v (ENNReal.ofReal (p / (p - 1))) Measure.count →
      (∑' m, ∑' n, ENNReal.ofReal (u m * v n / (m + n + 2 : ℝ))) ≤
        C * eLpNorm u (ENNReal.ofReal p) Measure.count *
          eLpNorm v (ENNReal.ofReal (p / (p - 1))) Measure.count}
      (ENNReal.ofReal (hilbertConstant p)) :=
  ⟨fun _ _ hu0 hv0 hu hv => hilbert_tsum hp hu0 hv0 hu hv,
    fun _ hC => hilbertConstant_le_of_hilbert_tsum_le hp hC⟩

end CKMA
