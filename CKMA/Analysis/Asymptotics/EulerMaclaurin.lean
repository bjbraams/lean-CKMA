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

The inclusive sum over integer endpoints is expressed as an interval integral,
half-endpoint values, Bernoulli derivative corrections and an exact signed periodic
Bernoulli remainder. The order is positive, and the remainder involves the derivative
of order twice that order.

Source: GAPS 50.23. Bernoulli functions and numbers reuse Mathlib's zeta-value API.
`CKMA.euler_maclaurin` is the scalar even-order case of
`TauCeti.sum_Icc_eq_eulerMaclaurin_of_hasDerivAt`, rewritten with Mathlib's
`periodizedBernoulli` on the circle and with global `iteratedDeriv`.

## Main definitions

* `CKMA.eulerMaclaurinRemainder`: signed periodic Bernoulli remainder in Euler–Maclaurin summation.

## Main results

* `CKMA.euler_maclaurin`: Euler–Maclaurin summation formula with exact periodic remainder.
-/

public section

noncomputable section

namespace CKMA

open Finset intervalIntegral MeasureTheory
open scoped BigOperators Nat

/-- The circle-valued periodic Bernoulli function agrees with `bernoulliFun` of the fractional
part. -/
private lemma periodizedBernoulli_eq_bernoulliFun_fract (k : ℕ) (x : ℝ) :
    periodizedBernoulli k (x : AddCircle (1 : ℝ)) = bernoulliFun k (Int.fract x) := by
  rw [← AddCircle.coe_fract x, periodizedBernoulli]
  exact AddCircle.liftIco_coe_apply
    ⟨Int.fract_nonneg x, by simpa [zero_add] using Int.fract_lt_one x⟩

/-- The signed Euler–Maclaurin remainder for the convention used in `GAPS_EASY.md`. -/
@[expose]
def eulerMaclaurinRemainder (p : ℕ) (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  -((2 * p).factorial : ℝ)⁻¹ * ∫ x in a..b,
    periodizedBernoulli (2 * p) (x : AddCircle (1 : ℝ)) * iteratedDeriv (2 * p) f x

/-- **50.23**: inclusive integer-endpoint Euler–Maclaurin with its exact periodic remainder.
Equal endpoints are included: both sides reduce to `f m`. The displayed remainder convention
requires `p ≥ 1`; the `p=0` formula is different. -/
theorem euler_maclaurin {m n : ℤ} (hmn : m ≤ n) {p : ℕ} (hp : 0 < p)
    (f : ℝ → ℝ) (hf : ContDiff ℝ (2 * p) f) :
    (∑ k ∈ Finset.Icc m n, f k) = (∫ x in (m : ℝ)..n, f x) + (f m + f n) / 2 +
      (∑ r ∈ Finset.range p, ((bernoulli (2 * (r + 1)) : ℚ) : ℝ) /
        (2 * (r + 1)).factorial *
        (iteratedDeriv (2 * r + 1) f n - iteratedDeriv (2 * r + 1) f m)) +
      eulerMaclaurinRemainder p f m n := by
  set g : ℕ → ℝ → ℝ := fun i ↦ iteratedDeriv i f
  have hcont : ∀ i < 2 * p, ContinuousOn (g i) (Set.Icc (m : ℝ) n) := by
    intro i hi
    exact (hf.continuous_iteratedDeriv i (by exact_mod_cast hi.le)).continuousOn
  have hderiv : ∀ i < 2 * p, ∀ x ∈ Set.Ioo (m : ℝ) n,
      HasDerivAt (g i) (g (i + 1) x) x := by
    intro i hi x _
    have hd := ((hf.differentiable_iteratedDeriv i (by exact_mod_cast hi)) x).hasDerivAt
    simpa [g, iteratedDeriv_succ] using hd
  have hint : IntervalIntegrable (g (2 * p)) volume (m : ℝ) n :=
    (hf.continuous_iteratedDeriv (2 * p) le_rfl).intervalIntegrable _ _
  have hEM := TauCeti.sum_Icc_eq_eulerMaclaurin_of_hasDerivAt (g := g) hmn (k := 2 * p)
    (by omega) hcont hderiv hint
  -- Odd Bernoulli numbers from `B₃` onward vanish, so only the even corrections remain.
  have hsum :
      (∑ s ∈ Icc 2 (2 * p), (bernoulli s / s ! : ℝ) * (g (s - 1) n - g (s - 1) m)) =
        ∑ r ∈ range p, ((bernoulli (2 * (r + 1)) : ℚ) : ℝ) / (2 * (r + 1)).factorial *
          (iteratedDeriv (2 * r + 1) f n - iteratedDeriv (2 * r + 1) f m) := by
    let F : ℕ → ℝ := fun s ↦
      (bernoulli s / s ! : ℝ) * (g (s - 1) n - g (s - 1) m)
    have hF : ∀ s ∈ Icc 2 (2 * p), Odd s → F s = 0 := by
      intro s hs ho
      have hlt : 1 < s := by
        have h2 : 2 ≤ s := (mem_Icc.mp hs).1
        omega
      simp [F, bernoulli_eq_zero_of_odd ho hlt]
    have hfilter : ∑ s ∈ Icc 2 (2 * p), F s = ∑ s ∈ (Icc 2 (2 * p)).filter Even, F s := by
      symm
      refine sum_filter_of_ne ?_
      intro s hs hne
      by_contra hod
      exact hne (hF s hs (Nat.not_even_iff_odd.mp hod))
    rw [hfilter]
    have himage : (range p).image (fun r ↦ 2 * (r + 1)) = (Icc 2 (2 * p)).filter Even := by
      ext s
      simp only [mem_image, mem_range, mem_filter, mem_Icc]
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact ⟨⟨by omega, by omega⟩, even_two_mul (r + 1)⟩
      · rintro ⟨⟨h2, hp⟩, he⟩
        obtain ⟨t, ht⟩ := even_iff_exists_two_mul.mp he
        refine ⟨t - 1, ?_, ?_⟩
        · omega
        · omega
    have hinj : Set.InjOn (fun r ↦ 2 * (r + 1)) (range p) := by
      intro r _ q _ h
      exact Nat.add_right_cancel (mul_right_injective₀ two_ne_zero h)
    rw [← himage, sum_image hinj]
    refine sum_congr rfl fun r _ ↦ ?_
    have hidx : 2 * (r + 1) - 1 = 2 * r + 1 := by omega
    simp only [F, g, hidx]
  have hintg : ∫ x in (m : ℝ)..n, bernoulliFun (2 * p) (Int.fract x) * g (2 * p) x =
      ∫ x in (m : ℝ)..n,
        periodizedBernoulli (2 * p) (x : AddCircle (1 : ℝ)) * iteratedDeriv (2 * p) f x := by
    refine integral_congr fun x _ ↦ ?_
    rw [periodizedBernoulli_eq_bernoulliFun_fract]
  simp only [smul_eq_mul] at hEM
  rw [hsum, hintg] at hEM
  simp only [g, iteratedDeriv_zero] at hEM
  rw [hEM]
  simp only [pow_mul, neg_one_sq, one_pow, div_eq_mul_inv, one_mul]
  rw [eulerMaclaurinRemainder]
  ring

end CKMA
