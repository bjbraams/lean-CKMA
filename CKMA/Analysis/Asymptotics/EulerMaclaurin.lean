/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.NumberTheory.ZetaValues
import TauCeti.Analysis.Asymptotics.Sum.EulerMaclaurin

/-!
# Euler–Maclaurin summation with periodic remainder

For integers `m ≤ n`, an order `p ≥ 1` and `f : ℝ → E` of class `C^{2p}` on `[m, n]`, with
values in a real Banach space `E`,
`∑_{k=m}^n f(k) = ∫_m^n f + (f(m) + f(n))/2
  + ∑_{r=1}^p B_{2r}/(2r)! (f^{(2r-1)}(n) - f^{(2r-1)}(m)) + R_p`,
where `R_p = -(2p)!⁻¹ ∫_m^n B_{2p}({x}) f^{(2p)}(x) dx`, `{x}` is the fractional part and
`B_{2p}({x})` is the periodic Bernoulli function `bernoulliFun (2 * p) (Int.fract x)`. The
derivatives are taken within `[m, n]`; for `f` of class `C^{2p}` on a neighbourhood of `[m, n]`
they agree with `iteratedDeriv` on `[m, n]` (`iteratedDerivWithin_eq_iteratedDeriv`).

Source: GAPS 50.23. The formula is derived from TauCeti's even-order
`TauCeti.sum_Icc_eq_eulerMaclaurin`, whose remainder
`∫_m^n (B_{2p} - B_{2p}({x}))/(2p)! f^{(2p)}(x) dx` contains the `r = p` boundary term.

## Main definitions

* `CKMA.eulerMaclaurinRemainder`: the remainder `R_p` above.

## Main results

* `CKMA.euler_maclaurin`: Euler–Maclaurin summation formula with exact periodic remainder.
-/

public section

noncomputable section

namespace CKMA

open Finset intervalIntegral MeasureTheory
open scoped Nat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Euler–Maclaurin remainder of order `p` on `[a, b]`,
`-(2p)!⁻¹ ∫_a^b B_{2p}({x}) f^{(2p)}(x) dx`, with the derivative taken within `[a, b]`. -/
@[expose]
def eulerMaclaurinRemainder (p : ℕ) (f : ℝ → E) (a b : ℝ) : E :=
  -((2 * p)! : ℝ)⁻¹ • ∫ x in a..b,
    bernoulliFun (2 * p) (Int.fract x) • iteratedDerivWithin (2 * p) f (Set.Icc a b) x

/-- The defining formula of `CKMA.eulerMaclaurinRemainder`. -/
theorem eulerMaclaurinRemainder_def (p : ℕ) (f : ℝ → E) (a b : ℝ) :
    eulerMaclaurinRemainder p f a b = -((2 * p)! : ℝ)⁻¹ • ∫ x in a..b,
      bernoulliFun (2 * p) (Int.fract x) • iteratedDerivWithin (2 * p) f (Set.Icc a b) x :=
  rfl

variable [CompleteSpace E]

/-- **50.23**: inclusive integer-endpoint Euler–Maclaurin with its exact periodic remainder,
for `p ≥ 1` and `f` of class `C^{2p}` on `[m, n]`. Equal endpoints are included: both sides
reduce to `f m`. -/
theorem euler_maclaurin {m n : ℤ} (hmn : m ≤ n) {p : ℕ} (hp : 0 < p) {f : ℝ → E}
    (hf : ContDiffOn ℝ (2 * p : ℕ) f (Set.Icc (m : ℝ) n)) :
    ∑ k ∈ Icc m n, f k = (∫ x in (m : ℝ)..n, f x) + (2 : ℝ)⁻¹ • (f m + f n) +
      ∑ r ∈ Icc 1 p, (bernoulli (2 * r) / (2 * r)! : ℝ) •
        (iteratedDerivWithin (2 * r - 1) f (Set.Icc m n) n -
          iteratedDerivWithin (2 * r - 1) f (Set.Icc m n) m) +
      eulerMaclaurinRemainder p f m n := by
  rcases hmn.lt_or_eq with hlt | rfl
  swap
  · simp only [Icc_self, sum_singleton, integral_same, sub_self, smul_zero, sum_const_zero,
      eulerMaclaurinRemainder, zero_add, add_zero, smul_add, ← add_smul]
    norm_num
  set g : ℕ → ℝ → E := fun i ↦ iteratedDerivWithin i f (Set.Icc (m : ℝ) n) with hg
  have hle : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hU : UniqueDiffOn ℝ (Set.Icc (m : ℝ) n) := uniqueDiffOn_Icc (by exact_mod_cast hlt)
  have hcont (i : ℕ) (hi : i ≤ 2 * p) : ContinuousOn (g i) (Set.Icc (m : ℝ) n) :=
    hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hi) hU
  have hint : IntervalIntegrable (g (2 * p)) volume m n :=
    (hcont _ le_rfl).intervalIntegrable_of_Icc hle
  -- The `r = p` boundary term is `∫_m^n f^{(2p)} = f^{(2p-1)}(n) - f^{(2p-1)}(m)`.
  have hderiv (x : ℝ) (hx : x ∈ Set.Ioo (m : ℝ) n) :
      HasDerivAt (g (2 * p - 1)) (g (2 * p) x) x := by
    have hx' : Set.Icc (m : ℝ) n ∈ nhds x := Icc_mem_nhds hx.1 hx.2
    have hd := hf.differentiableOn_iteratedDerivWithin (m := 2 * p - 1)
      (by exact_mod_cast (by omega : 2 * p - 1 < 2 * p)) hU x (Set.Ioo_subset_Icc_self hx)
    have h2 : 2 * p = 2 * p - 1 + 1 := by omega
    rw [h2]
    simp only [hg, iteratedDerivWithin_succ, derivWithin_of_mem_nhds hx']
    exact (hd.differentiableAt hx').hasDerivAt
  have hFTC : ∫ x in (m : ℝ)..n, g (2 * p) x = g (2 * p - 1) n - g (2 * p - 1) m :=
    integral_eq_sub_of_hasDerivAt_of_le hle (hcont _ (by omega)) hderiv hint
  have hR : ∫ x in (m : ℝ)..n,
        ((bernoulli (2 * p) - bernoulliFun (2 * p) (Int.fract x)) / (2 * p)!) • g (2 * p) x =
      (bernoulli (2 * p) / (2 * p)! : ℝ) • (∫ x in (m : ℝ)..n, g (2 * p) x) +
        eulerMaclaurinRemainder p f m n := by
    have h₁ : IntervalIntegrable (fun x ↦ (bernoulli (2 * p) / (2 * p)! : ℝ) • g (2 * p) x)
        volume m n := hint.smul _
    have h₂ : IntervalIntegrable (fun x ↦ -((2 * p)! : ℝ)⁻¹ •
        bernoulliFun (2 * p) (Int.fract x) • g (2 * p) x) volume m n :=
      (hint.bernoulliFun_fract_smul _).smul _
    rw [eulerMaclaurinRemainder, ← intervalIntegral.integral_smul,
      ← intervalIntegral.integral_smul, ← intervalIntegral.integral_add h₁ h₂]
    exact integral_congr fun x _ ↦ by module
  rw [TauCeti.sum_Icc_eq_eulerMaclaurin hmn hp hf, ← Finset.Ico_add_one_right_eq_Icc,
    sum_Ico_succ_top hp, hR, hFTC, smul_add]
  abel

end CKMA
