/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.ENNReal.Real

/-!
# Comparison of `‖ξ‖^{2s}` with the Bessel weight

Elementary bounds, for `0 ≤ s` and `r ≥ 0`, between `(1 + r ^ 2) ^ s` and `1 + r ^ (2 * s)`.
They turn the Fourier form of the Gagliardo energy into a two-sided comparison with the
Bessel potential. No minimization of a continuous function is required: the inequalities are
read off by splitting `r ≤ 1` and `r ≥ 1`, or by adding the two trivial lower bounds `1` and
`r ^ (2 * s)`.
-/

@[expose] public section

noncomputable section

namespace CKMA

/-- `(r ^ 2) ^ s = r ^ (2 * s)` for a nonnegative base. -/
private lemma sq_rpow {r s : ℝ} (hr : 0 ≤ r) : (r ^ 2) ^ s = r ^ (2 * s) := by
  rw [← Real.rpow_two, ← Real.rpow_mul hr]

/-- `(1 + r ^ 2) ^ s ≤ 2 ^ s * (1 + r ^ (2 * s))` for `0 ≤ s` and `0 ≤ r`. -/
theorem one_add_sq_rpow_le_two_rpow_mul {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) :
    (1 + r ^ 2) ^ s ≤ 2 ^ s * (1 + r ^ (2 * s)) := by
  have hrpow : 0 ≤ r ^ (2 * s) := Real.rpow_nonneg hr _
  have htwo : 0 ≤ (2 : ℝ) ^ s := Real.rpow_nonneg (by positivity) _
  by_cases hr1 : r ≤ 1
  · have hsum : 1 + r ^ 2 ≤ 2 := by
      have : r ^ 2 ≤ 1 := pow_le_one₀ hr hr1
      linarith
    have hsbase : (1 + r ^ 2) ^ s ≤ 2 ^ s :=
      Real.rpow_le_rpow (by positivity) hsum hs
    calc
      (1 + r ^ 2) ^ s ≤ 2 ^ s := hsbase
      _ = 2 ^ s * 1 := (mul_one _).symm
      _ ≤ 2 ^ s * (1 + r ^ (2 * s)) :=
        mul_le_mul_of_nonneg_left (by linarith) htwo
  · have hr1' : 1 ≤ r := le_of_not_ge hr1
    have hr2 : 1 ≤ r ^ 2 := one_le_pow₀ hr1'
    have hsum : 1 + r ^ 2 ≤ 2 * r ^ 2 := by linarith
    have hsbase : (1 + r ^ 2) ^ s ≤ (2 * r ^ 2) ^ s :=
      Real.rpow_le_rpow (by positivity) hsum hs
    have hsplit : (2 * r ^ 2) ^ s = 2 ^ s * (r ^ 2) ^ s :=
      Real.mul_rpow (by positivity) (sq_nonneg r)
    calc
      (1 + r ^ 2) ^ s ≤ (2 * r ^ 2) ^ s := hsbase
      _ = 2 ^ s * (r ^ 2) ^ s := hsplit
      _ = 2 ^ s * r ^ (2 * s) := by rw [sq_rpow hr]
      _ ≤ 2 ^ s * (1 + r ^ (2 * s)) :=
        mul_le_mul_of_nonneg_left (by linarith) htwo

/-- `(1 / 2) * (1 + r ^ (2 * s)) ≤ (1 + r ^ 2) ^ s` for `0 ≤ s` and `0 ≤ r`. -/
theorem half_mul_one_add_rpow_le {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) :
    (1 / 2) * (1 + r ^ (2 * s)) ≤ (1 + r ^ 2) ^ s := by
  have hge1 : (1 : ℝ) ≤ (1 + r ^ 2) ^ s :=
    Real.one_le_rpow (by linarith [sq_nonneg r]) hs
  have hge : r ^ (2 * s) ≤ (1 + r ^ 2) ^ s := by
    rw [← sq_rpow hr]
    exact Real.rpow_le_rpow (sq_nonneg r) (by linarith) hs
  linarith

/-- Extended-real form of the scalar comparison, after multiplication by a nonnegative density. -/
theorem ofReal_bessel_weight_bounds {s r n : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r) (hn : 0 ≤ n) :
    ENNReal.ofReal (1 / 2) * (ENNReal.ofReal n + ENNReal.ofReal (r ^ (2 * s) * n)) ≤
        ENNReal.ofReal ((1 + r ^ 2) ^ s * n) ∧
      ENNReal.ofReal ((1 + r ^ 2) ^ s * n) ≤
        ENNReal.ofReal (2 ^ s) *
          (ENNReal.ofReal n + ENNReal.ofReal (r ^ (2 * s) * n)) := by
  have hrpow : 0 ≤ r ^ (2 * s) := Real.rpow_nonneg hr _
  have hprod : 0 ≤ r ^ (2 * s) * n := mul_nonneg hrpow hn
  have hsum : 0 ≤ n + r ^ (2 * s) * n := add_nonneg hn hprod
  have hhalf : (1 / 2) * (n + r ^ (2 * s) * n) ≤ (1 + r ^ 2) ^ s * n := by
    have hcoeff : (1 / 2) * (1 + r ^ (2 * s)) * n ≤ (1 + r ^ 2) ^ s * n :=
      mul_le_mul_of_nonneg_right (half_mul_one_add_rpow_le hs hr) hn
    have hrew : (1 / 2) * (n + r ^ (2 * s) * n) =
        (1 / 2) * (1 + r ^ (2 * s)) * n := by ring
    rw [hrew]
    exact hcoeff
  have hup : (1 + r ^ 2) ^ s * n ≤ 2 ^ s * (n + r ^ (2 * s) * n) := by
    have hcoeff : (1 + r ^ 2) ^ s * n ≤ 2 ^ s * (1 + r ^ (2 * s)) * n :=
      mul_le_mul_of_nonneg_right (one_add_sq_rpow_le_two_rpow_mul hs hr) hn
    have hrew : 2 ^ s * (1 + r ^ (2 * s)) * n = 2 ^ s * (n + r ^ (2 * s) * n) := by ring
    rw [← hrew]
    exact hcoeff
  constructor
  · calc
      ENNReal.ofReal (1 / 2) * (ENNReal.ofReal n + ENNReal.ofReal (r ^ (2 * s) * n))
          = ENNReal.ofReal (1 / 2) * ENNReal.ofReal (n + r ^ (2 * s) * n) := by
            rw [ENNReal.ofReal_add hn hprod]
      _ = ENNReal.ofReal ((1 / 2) * (n + r ^ (2 * s) * n)) := by
            rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (1 : ℝ) / 2)]
      _ ≤ ENNReal.ofReal ((1 + r ^ 2) ^ s * n) := ENNReal.ofReal_le_ofReal hhalf
  · calc
      ENNReal.ofReal ((1 + r ^ 2) ^ s * n)
          ≤ ENNReal.ofReal (2 ^ s * (n + r ^ (2 * s) * n)) := ENNReal.ofReal_le_ofReal hup
      _ = ENNReal.ofReal (2 ^ s) * ENNReal.ofReal (n + r ^ (2 * s) * n) := by
            rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
      _ = ENNReal.ofReal (2 ^ s) *
            (ENNReal.ofReal n + ENNReal.ofReal (r ^ (2 * s) * n)) := by
          rw [ENNReal.ofReal_add hn hprod]

/-- Pass from a squeeze of `N + A` to a squeeze of `N + K • A`, with positive finite constants. -/
theorem ennreal_weighted_comparable {K s : ℝ} (hK : 0 < K) {N A B : ENNReal}
    (hlo : ENNReal.ofReal (1 / 2) * (N + A) ≤ B)
    (hhi : B ≤ ENNReal.ofReal (2 ^ s) * (N + A)) :
    ENNReal.ofReal (1 / (2 * max K 1)) * (N + ENNReal.ofReal K * A) ≤ B ∧
      B ≤ ENNReal.ofReal (2 ^ s * max K⁻¹ 1) * (N + ENNReal.ofReal K * A) := by
  have hs2 : 0 ≤ (2 : ℝ) ^ s := Real.rpow_nonneg (by positivity) _
  set M : ℝ := max K 1
  have hMge1 : (1 : ℝ) ≤ M := le_max_right _ _
  have hMgeK : K ≤ M := le_max_left _ _
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hMge1
  have hone : (1 : ENNReal) ≤ ENNReal.ofReal M := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hMge1
  have hKN : ENNReal.ofReal K * A ≤ ENNReal.ofReal M * A :=
    mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hMgeK) zero_le
  have hN : N ≤ ENNReal.ofReal M * N :=
    calc
      N = 1 * N := (one_mul N).symm
      _ ≤ ENNReal.ofReal M * N := mul_le_mul_of_nonneg_right hone zero_le
  have hsum : N + ENNReal.ofReal K * A ≤ ENNReal.ofReal M * (N + A) := by
    calc
      N + ENNReal.ofReal K * A ≤ ENNReal.ofReal M * N + ENNReal.ofReal M * A :=
        add_le_add hN hKN
      _ = ENNReal.ofReal M * (N + A) := by rw [← mul_add]
  have hcancel : (1 / (2 * M)) * M = 1 / 2 := by
    field_simp [hMpos.ne']
  have hcM : ENNReal.ofReal (1 / (2 * M)) * ENNReal.ofReal M = ENNReal.ofReal (1 / 2) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (2 * M))]
    rw [hcancel]
  set Minv : ℝ := max K⁻¹ 1
  have hInv1 : (1 : ℝ) ≤ Minv := le_max_right _ _
  have hInvK : K⁻¹ ≤ Minv := le_max_left _ _
  have hInv0 : 0 ≤ Minv := le_trans zero_le_one hInv1
  have hprod : (1 : ℝ) ≤ Minv * K := by
    calc
      (1 : ℝ) = K⁻¹ * K := by rw [inv_mul_cancel₀ hK.ne']
      _ ≤ Minv * K := mul_le_mul_of_nonneg_right hInvK hK.le
  have hInv1' : (1 : ENNReal) ≤ ENNReal.ofReal Minv := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hInv1
  have hprod' : (1 : ENNReal) ≤ ENNReal.ofReal (Minv * K) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hprod
  have hN' : N ≤ ENNReal.ofReal Minv * N :=
    calc
      N = 1 * N := (one_mul N).symm
      _ ≤ ENNReal.ofReal Minv * N := mul_le_mul_of_nonneg_right hInv1' zero_le
  have hA : A ≤ ENNReal.ofReal Minv * (ENNReal.ofReal K * A) := by
    calc
      A = 1 * A := (one_mul A).symm
      _ ≤ ENNReal.ofReal (Minv * K) * A := mul_le_mul_of_nonneg_right hprod' zero_le
      _ = ENNReal.ofReal Minv * ENNReal.ofReal K * A := by
        rw [ENNReal.ofReal_mul hInv0]
      _ = ENNReal.ofReal Minv * (ENNReal.ofReal K * A) := by rw [mul_assoc]
  have hsum' : N + A ≤ ENNReal.ofReal Minv * (N + ENNReal.ofReal K * A) := by
    calc
      N + A ≤ ENNReal.ofReal Minv * N + ENNReal.ofReal Minv * (ENNReal.ofReal K * A) :=
        add_le_add hN' hA
      _ = ENNReal.ofReal Minv * (N + ENNReal.ofReal K * A) := by rw [← mul_add]
  constructor
  · calc
      ENNReal.ofReal (1 / (2 * M)) * (N + ENNReal.ofReal K * A)
          ≤ ENNReal.ofReal (1 / (2 * M)) * (ENNReal.ofReal M * (N + A)) :=
            mul_le_mul_of_nonneg_left hsum zero_le
      _ = (ENNReal.ofReal (1 / (2 * M)) * ENNReal.ofReal M) * (N + A) := by rw [← mul_assoc]
      _ = ENNReal.ofReal (1 / 2) * (N + A) := by rw [hcM]
      _ ≤ B := hlo
  · calc
      B ≤ ENNReal.ofReal (2 ^ s) * (N + A) := hhi
      _ ≤ ENNReal.ofReal (2 ^ s) *
            (ENNReal.ofReal Minv * (N + ENNReal.ofReal K * A)) :=
          mul_le_mul_of_nonneg_left hsum' zero_le
      _ = (ENNReal.ofReal (2 ^ s) * ENNReal.ofReal Minv) *
            (N + ENNReal.ofReal K * A) := by rw [← mul_assoc]
      _ = ENNReal.ofReal (2 ^ s * Minv) * (N + ENNReal.ofReal K * A) := by
          rw [← ENNReal.ofReal_mul hs2]

end CKMA
