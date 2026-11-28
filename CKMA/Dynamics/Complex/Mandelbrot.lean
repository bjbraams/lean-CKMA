/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.Complex.PolynomialJulia

import Mathlib.Algebra.Order.Ring.Star

/-!
# The Mandelbrot set (46.40)

The Mandelbrot set is the set of parameters `c` for which the critical orbit of `z ↦ z ^ 2 + c`
from `0` is bounded. The radius-two escape criterion gives compactness; connectedness
(Douady–Hubbard) is admitted, and membership is equivalent to connectedness of the Julia set of
`z ^ 2 + c` by the critical-orbit criterion `CKMA.isConnected_polynomialFilledJuliaSet_iff`.

## Main definitions

* `CKMA.quadraticFamily`: the quadratic polynomial `X ^ 2 + C c`.
* `CKMA.mandelbrotSet`: parameters with bounded critical orbit.

## Main results

* `CKMA.mem_mandelbrotSet_iff`, `CKMA.mandelbrotSet_subset_closedBall`,
  `CKMA.isCompact_mandelbrotSet`: the radius-two critical-orbit criterion and compactness.
* `CKMA.isConnected_mandelbrotSet`: connectedness of the Mandelbrot set.
* `CKMA.mem_mandelbrotSet_iff_isConnected_polynomialJuliaSet`: the Julia-set criterion.
* `CKMA.mandelbrot_properties`: the four properties together (**46.40**).
-/

public section

noncomputable section

namespace CKMA

open Bornology Filter Function Metric Polynomial Set Topology

/-- The standard quadratic family. -/
@[expose]
def quadraticFamily (c : ℂ) : ℂ[X] := X ^ 2 + C c

/-- Defining equation of `quadraticFamily`. -/
theorem quadraticFamily_def (c : ℂ) : quadraticFamily c = X ^ 2 + C c := rfl

/-- Evaluation of `quadraticFamily`. -/
@[simp]
theorem eval_quadraticFamily (c z : ℂ) : (quadraticFamily c).eval z = z ^ 2 + c := by
  simp [quadraticFamily]

/-- The Mandelbrot set is the set of bounded quadratic critical orbits. -/
@[expose]
def mandelbrotSet : Set ℂ := {c | HasBoundedOrbit (fun z ↦ z ^ 2 + c) 0}

/-- Membership in `mandelbrotSet` as a bounded critical orbit. -/
theorem mem_mandelbrotSet_iff_hasBoundedOrbit {c : ℂ} :
    c ∈ mandelbrotSet ↔ HasBoundedOrbit (fun z ↦ z ^ 2 + c) 0 := Iff.rfl

/-- A bounded quadratic orbit cannot visit a point of norm greater than both `2` and `‖c‖`. -/
private theorem not_hasBoundedOrbit_quadratic_of_lt {c z : ℂ}
    (h₂ : 2 < ‖z‖) (hc : ‖c‖ ≤ ‖z‖) :
    ¬ HasBoundedOrbit (fun w : ℂ ↦ w ^ 2 + c) z := by
  set f : ℂ → ℂ := fun w ↦ w ^ 2 + c
  set q := ‖z‖ - 1
  have hq : 1 < q := by dsimp [q]; linarith
  have hstep {w : ℂ} (hw : ‖z‖ ≤ ‖w‖) : q * ‖w‖ ≤ ‖f w‖ := by
    have htri : ‖w‖ ^ 2 ≤ ‖f w‖ + ‖c‖ := by
      rw [← norm_pow, ← norm_neg c]
      convert norm_add_le (f w) (-c) using 1
      simp [f]
    have hprod := mul_le_mul_of_nonneg_right hw (norm_nonneg w)
    dsimp only [q]
    nlinarith [hc.trans hw]
  have hiter (n : ℕ) : q ^ n * ‖z‖ ≤ ‖(f^[n]) z‖ := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hzpow : ‖z‖ ≤ q ^ n * ‖z‖ :=
        le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hq.le)
      rw [iterate_succ_apply', pow_succ', mul_assoc]
      exact (mul_le_mul_of_nonneg_left ih (zero_le_one.trans hq.le)).trans
        (hstep (hzpow.trans ih))
  intro hbounded
  obtain ⟨B, hB⟩ := (hasBoundedOrbit_iff_exists_norm_le f z).mp hbounded
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hq).atTop_mul_const'
    (zero_lt_two.trans h₂) |>.eventually_gt_atTop B).exists
  exact (hn.trans_le (hiter n)).not_ge (hB n)

/-- The critical orbit is bounded exactly when every iterate has norm at most `2`. -/
theorem mem_mandelbrotSet_iff {c : ℂ} : c ∈ mandelbrotSet ↔
    ∀ n : ℕ, ‖((fun z : ℂ ↦ z ^ 2 + c)^[n]) 0‖ ≤ 2 := by
  set f : ℂ → ℂ := fun w ↦ w ^ 2 + c
  have hf : f 0 = c := by simp [f]
  constructor
  · intro h n
    have hbounded : HasBoundedOrbit f 0 := h
    have hc : ‖c‖ ≤ 2 := by
      by_contra! hc
      have hmap : HasBoundedOrbit f c := by simpa only [← hf] using hbounded.map
      exact not_hasBoundedOrbit_quadratic_of_lt hc le_rfl hmap
    by_contra! hn
    obtain ⟨B, hB⟩ := (hasBoundedOrbit_iff_exists_norm_le f 0).mp hbounded
    have htail : HasBoundedOrbit f ((f^[n]) 0) :=
      (hasBoundedOrbit_iff_exists_norm_le _ _).mpr ⟨B, fun k ↦ by
        rw [← iterate_add_apply]
        exact hB (k + n)⟩
    exact not_hasBoundedOrbit_quadratic_of_lt hn (hc.trans hn.le) htail
  · intro h
    exact (hasBoundedOrbit_iff_exists_norm_le f 0).mpr ⟨2, h⟩

/-- The Mandelbrot set lies in the closed disc of radius `2`. -/
theorem mandelbrotSet_subset_closedBall : mandelbrotSet ⊆ Metric.closedBall 0 2 := by
  intro c hc
  simpa [mem_closedBall, dist_zero_right, iterate_one] using mem_mandelbrotSet_iff.mp hc 1

/-- The Mandelbrot set is compact. -/
theorem isCompact_mandelbrotSet : IsCompact mandelbrotSet := by
  refine (isCompact_closedBall 0 2).of_isClosed_subset ?_ mandelbrotSet_subset_closedBall
  have hcont (n : ℕ) : Continuous (fun c : ℂ ↦ ((fun z : ℂ ↦ z ^ 2 + c)^[n]) 0) := by
    induction n with
    | zero => exact continuous_const
    | succ n ih =>
      simp only [iterate_succ_apply']
      exact (ih.pow 2).add continuous_id
  have heq : mandelbrotSet = ⋂ n : ℕ,
      {c : ℂ | ‖((fun z : ℂ ↦ z ^ 2 + c)^[n]) 0‖ ≤ 2} := by
    ext c
    simpa only [mem_iInter, mem_ofPred_eq] using (mem_mandelbrotSet_iff (c := c))
  rw [heq]
  exact isClosed_iInter fun n ↦ isClosed_le (hcont n).norm continuous_const

/-- **46.40**, connectedness: the Mandelbrot set is connected (Douady–Hubbard). -/
theorem isConnected_mandelbrotSet : IsConnected mandelbrotSet := by
  sorry

/-- **46.40**, Julia criterion: `c` lies in the Mandelbrot set exactly when the Julia set of
`z ↦ z ^ 2 + c` is connected. -/
theorem mem_mandelbrotSet_iff_isConnected_polynomialJuliaSet (c : ℂ) :
    c ∈ mandelbrotSet ↔ IsConnected (polynomialJuliaSet (quadraticFamily c)) := by
  have hdegree : 2 ≤ (quadraticFamily c).natDegree := by
    simp only [quadraticFamily, Polynomial.natDegree_X_pow_add_C, le_rfl]
  have hcrit : ∀ z : ℂ, (quadraticFamily c).derivative.eval z = 0 ↔ z = 0 := by
    intro z
    rw [quadraticFamily, Polynomial.derivative_add, Polynomial.derivative_C, add_zero,
      Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_C]
    simp
  have heval (z : ℂ) : (quadraticFamily c).eval z = z ^ 2 + c := by
    simp [quadraticFamily]
  rw [(isConnected_polynomialFilledJuliaSet_iff hdegree).2,
    (isConnected_polynomialFilledJuliaSet_iff hdegree).1]
  constructor
  · intro hc z hz
    rw [(hcrit z).mp hz]
    simpa only [mandelbrotSet, polynomialFilledJuliaSet, mem_ofPred_eq, heval] using hc
  · intro hc
    simpa only [mandelbrotSet, polynomialFilledJuliaSet, mem_ofPred_eq, heval]
      using hc 0 ((hcrit 0).mpr rfl)

/-- **46.40**: Mandelbrot compactness, connectedness, escape bound and the Julia criterion. -/
theorem mandelbrot_properties : IsCompact mandelbrotSet ∧ IsConnected mandelbrotSet ∧
    mandelbrotSet ⊆ Metric.closedBall 0 2 ∧
    ∀ c : ℂ, c ∈ mandelbrotSet ↔ IsConnected (polynomialJuliaSet (quadraticFamily c)) :=
  ⟨isCompact_mandelbrotSet, isConnected_mandelbrotSet, mandelbrotSet_subset_closedBall,
    mem_mandelbrotSet_iff_isConnected_polynomialJuliaSet⟩

end CKMA
