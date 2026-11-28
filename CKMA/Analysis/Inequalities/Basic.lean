/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Sum–integral comparisons and limiting bounds for the classical inequalities

Elementary tools used in the optimality proofs of the classical inequalities: comparisons
between the values of an antitone `ℝ≥0∞`-valued function at `1, …, N` and its Lebesgue integral,
the integral `∫_1^N dx / x = log N`, and the limiting argument that an affine bound
`k L ≤ c L + d` along unbounded finite `L` forces `k ≤ c`.

## Main results

* `CKMA.le_of_forall_nat_le_mul_le_mul_add`: an affine bound `k L ≤ c L + d` with `d ≠ ∞`, for
  arbitrarily large finite `L`, forces `k ≤ c`.
* `CKMA.lintegral_ofReal_inv_Ioo_one`: `∫⁻_{(1, N)} 1 / x = log N` for `1 < N`.
* `CKMA.lintegral_Ioo_le_sum_of_antitoneOn`: `∫⁻_{(1, N + 1)} φ ≤ φ 1 + ⋯ + φ N` for antitone `φ`.
* `CKMA.sum_le_lintegral_Ioc_of_antitoneOn`: `ψ 1 + ⋯ + ψ N ≤ ∫⁻_{(0, N]} ψ` for antitone `ψ`.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Set
open scoped ENNReal

/-- An affine bound `k L ≤ c L + d` with `d ≠ ∞`, holding for finite `L` beyond every natural
number, forces `k ≤ c`. -/
theorem le_of_forall_nat_le_mul_le_mul_add {k c d : ℝ≥0∞} (hd : d ≠ ⊤)
    (h : ∀ n : ℕ, ∃ L : ℝ≥0∞, (n : ℝ≥0∞) ≤ L ∧ L ≠ ⊤ ∧ k * L ≤ c * L + d) : k ≤ c := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt (tsub_pos_of_lt hlt).ne' hd
  obtain ⟨L, hnL, hLt, hkL⟩ := h n
  have hsub : (k - c) * L ≤ d := by
    rw [ENNReal.sub_mul fun _ _ => hLt]
    exact tsub_le_iff_right.mpr (by rwa [add_comm])
  exact (hn.trans_le ((mul_le_mul_left hnL _).trans_eq (mul_comm _ _))).not_ge hsub

/-- `∫⁻_{(1, N)} 1 / x = log N` for `1 < N`. -/
theorem lintegral_ofReal_inv_Ioo_one {N : ℝ} (hN : 1 < N) :
    ∫⁻ x in Ioo 1 N, ENNReal.ofReal x⁻¹ = ENNReal.ofReal (Real.log N) := by
  have hsub : Icc (1 : ℝ) N ⊆ {0}ᶜ := fun x hx => (zero_lt_one.trans_le hx.1).ne'
  have hint : IntegrableOn (fun x : ℝ => x⁻¹) (Ioc 1 N) :=
    ((continuousOn_inv₀.mono hsub).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [setLIntegral_congr Ioo_ae_eq_Ioc, ← ofReal_integral_eq_lintegral_ofReal hint
      (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx =>
        (inv_pos.mpr (zero_lt_one.trans hx.1)).le),
    ← intervalIntegral.integral_of_le hN.le, integral_inv_of_pos one_pos (one_pos.trans hN),
    div_one]

/-- An antitone function on `(0, ∞)` has integral over `(1, N + 1)` at most the sum of its
values at `1, …, N`. -/
theorem lintegral_Ioo_le_sum_of_antitoneOn {φ : ℝ → ℝ≥0∞} (hφ : AntitoneOn φ (Ioi 0))
    (N : ℕ) : ∫⁻ y in Ioo 1 ((N : ℝ) + 1), φ y ≤ ∑ n ∈ Finset.range N, φ ((n : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hcover : Ioo 1 (((N + 1 : ℕ) : ℝ) + 1) ⊆
        Ioo 1 ((N : ℝ) + 1) ∪ Ico ((N : ℝ) + 1) ((N : ℝ) + 1 + 1) := by
      intro y hy
      push_cast at hy
      by_cases h : y < (N : ℝ) + 1
      · exact Or.inl ⟨hy.1, h⟩
      · exact Or.inr ⟨le_of_not_gt h, hy.2⟩
    have hlast : ∫⁻ y in Ico ((N : ℝ) + 1) ((N : ℝ) + 1 + 1), φ y ≤ φ ((N : ℝ) + 1) := by
      calc ∫⁻ y in Ico ((N : ℝ) + 1) ((N : ℝ) + 1 + 1), φ y
          ≤ ∫⁻ _ in Ico ((N : ℝ) + 1) ((N : ℝ) + 1 + 1), φ ((N : ℝ) + 1) :=
            setLIntegral_mono' measurableSet_Ico fun y hy =>
              hφ (show (0 : ℝ) < N + 1 by positivity)
                (show (0 : ℝ) < y by linarith [hy.1, N.cast_nonneg (α := ℝ)]) hy.1
        _ = φ ((N : ℝ) + 1) := by simp [Real.volume_Ico]
    rw [Finset.sum_range_succ]
    exact (lintegral_mono_set hcover).trans
      ((lintegral_union_le _ _ _).trans (add_le_add ih hlast))

/-- The values of an antitone function on `(0, ∞)` at `1, …, N` sum to at most its integral
over `(0, N]`. -/
theorem sum_le_lintegral_Ioc_of_antitoneOn {ψ : ℝ → ℝ≥0∞} (hψ : AntitoneOn ψ (Ioi 0))
    (N : ℕ) : ∑ m ∈ Finset.range N, ψ ((m : ℝ) + 1) ≤ ∫⁻ x in Ioc 0 (N : ℝ), ψ x := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN : (0 : ℝ) ≤ N := N.cast_nonneg
    have hlast : ψ ((N : ℝ) + 1) ≤ ∫⁻ x in Ioc (N : ℝ) ((N : ℝ) + 1), ψ x := by
      calc ψ ((N : ℝ) + 1) = ∫⁻ _ in Ioc (N : ℝ) ((N : ℝ) + 1), ψ ((N : ℝ) + 1) := by
            simp [Real.volume_Ioc]
        _ ≤ _ := setLIntegral_mono' measurableSet_Ioc fun x hx =>
            hψ (show (0 : ℝ) < x from lt_of_le_of_lt hN hx.1)
              (show (0 : ℝ) < N + 1 by positivity) hx.2
    rw [Finset.sum_range_succ, Nat.cast_succ,
      ← Ioc_union_Ioc_eq_Ioc hN (by linarith : (N : ℝ) ≤ N + 1),
      lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl)]
    exact add_le_add ih hlast

end CKMA
