/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic

/-!
# Newton–Maclaurin and discrete Hardy inequalities

Normalized elementary symmetric means of finite tuples, Newton log-concavity and
Maclaurin's chain for nonnegative entries. Cesàro averages use the first `n+1` terms;
Hardy's inequality and its optimal constant are expressed by extended nonnegative sums.
Elementary symmetric polynomials, real powers and infinite sums reuse Mathlib.
Sources: GAPS 11.9 and 11.32.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped BigOperators ENNReal

/-- The elementary symmetric mean `e_k / choose(n,k)` of a finite real tuple. -/
def normalizedElementaryMean {n : ℕ} (x : Fin n → ℝ) (k : ℕ) : ℝ :=
  (Finset.univ.val.map x).esymm k / (n.choose k : ℝ)

/-- The zeroth symmetric mean is one, including the empty tuple. -/
@[simp]
theorem normalizedElementaryMean_zero {n : ℕ} (x : Fin n → ℝ) :
    normalizedElementaryMean x 0 = 1 := by
  simp [normalizedElementaryMean]

/-- **11.9**: Newton log-concavity of normalized elementary symmetric means. -/
theorem newton_normalizedElementaryMean {n k : ℕ} (x : Fin n → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hk : 1 ≤ k) (hkn : k < n) :
    normalizedElementaryMean x (k - 1) * normalizedElementaryMean x (k + 1) ≤
      normalizedElementaryMean x k ^ 2 := by
  sorry

/-- Maclaurin's monotone chain of positive-root normalized means, allowing zero entries. -/
theorem maclaurin_normalizedElementaryMean {n j k : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hj : 1 ≤ j) (hjk : j ≤ k) (hkn : k ≤ n) :
    normalizedElementaryMean x k ^ (1 / (k : ℝ)) ≤
      normalizedElementaryMean x j ^ (1 / (j : ℝ)) := by
  sorry

/-- Cesaro average of the first `n+1` entries, indexed from zero. -/
def hardyAverage (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (n + 1), a j) / (n + 1 : ℝ)

/-- **11.32**: Hardy's discrete inequality, stated as an extended nonnegative sum. -/
theorem discrete_hardy {p : ℝ} (hp : 1 < p) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) :
    (∑' n, ENNReal.ofReal (hardyAverage a n ^ p)) ≤
      ENNReal.ofReal ((p / (p - 1)) ^ p) * ∑' n, ENNReal.ofReal (a n ^ p) := by
  sorry

/-- The constant in Hardy's inequality is optimal already on finitely supported inputs. -/
theorem discrete_hardy_constant_le {p C : ℝ} (hp : 1 < p) (hC : 0 ≤ C)
    (hbound : ∀ a : ℕ → ℝ, (∀ n, 0 ≤ a n) → (Function.support a).Finite →
      (∑' n, ENNReal.ofReal (hardyAverage a n ^ p)) ≤
        ENNReal.ofReal C * ∑' n, ENNReal.ofReal (a n ^ p)) :
    (p / (p - 1)) ^ p ≤ C := by
  sorry

end CKMA
