/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.BrownianTheory.DyadicPath

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Hölder limits of dyadic floors

A function whose dyadic increments are Hölder is Cauchy along dyadic floors. The limit is
Hölder on each compact interval, with constant equal to the summed dyadic factor.

## Main results

* `CKMA.Brownian.tendsto_dyadicFloor_limUnder`: values of a dyadically Hölder function at
  the dyadic floors of `t` converge to their `limUnder`.
* `CKMA.Brownian.abs_sub_dyadicFloor_lim`: limits of dyadic floors are Hölder with the summed
  dyadic constant.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Finset Filter
open scoped Topology

namespace Brownian

/-- Two consecutive meshes add to one and a half times the coarser mesh. -/
private lemma two_mesh_sum (n : ℕ) :
    (1 : ℝ) / 2 ^ n + 1 / 2 ^ (n + 1) = (3 / 2) * (2 : ℝ) ^ (-(n : ℝ)) := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  rw [one_div_two_pow_eq_rpow, one_div_two_pow_eq_rpow]
  have hsucc : (-((n + 1 : ℕ) : ℝ)) = -(n : ℝ) + -1 := by push_cast; ring
  rw [hsucc, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_neg_one]
  field_simp
  ring

/-- The summed mesh, raised to `α`, is a geometric term of ratio `2 ^ (-α)`. -/
private lemma two_mesh_sum_rpow {α : ℝ} (n : ℕ) :
    (1 / 2 ^ n + 1 / 2 ^ (n + 1)) ^ α =
      ((3 : ℝ) / 2) ^ α * ((2 : ℝ) ^ (-α)) ^ n := by
  have hbase : (0 : ℝ) ≤ (3 : ℝ) / 2 := by positivity
  have htwo : (0 : ℝ) ≤ 2 := by positivity
  rw [two_mesh_sum]
  calc
    ((3 : ℝ) / 2 * (2 : ℝ) ^ (-(n : ℝ))) ^ α =
        ((3 : ℝ) / 2) ^ α * ((2 : ℝ) ^ (-(n : ℝ))) ^ α :=
      Real.mul_rpow hbase (Real.rpow_nonneg htwo _)
    _ = ((3 : ℝ) / 2) ^ α * (2 : ℝ) ^ ((-(n : ℝ)) * α) := by
      rw [← Real.rpow_mul htwo]
    _ = ((3 : ℝ) / 2) ^ α * (2 : ℝ) ^ (-α * (n : ℝ)) := by ring_nf
    _ = ((3 : ℝ) / 2) ^ α * ((2 : ℝ) ^ (-α)) ^ (n : ℝ) := by
      rw [← Real.rpow_mul htwo]
    _ = ((3 : ℝ) / 2) ^ α * ((2 : ℝ) ^ (-α)) ^ n := by
      rw [Real.rpow_natCast]

/-- Dyadic floors of a dyadically Hölder function form a Cauchy sequence. -/
private lemma cauchySeq_dyadicFloor {f : ℝ → ℝ} {α : ℝ} {K : ℕ → ℝ} {N : ℕ}
    (hα : 0 < α) (hK : ∀ j, j < N → 0 ≤ K j)
    (hinc : ∀ j, j < N → HasDyadicIncrements f α (K j) j)
    {t : ℝ} (ht0 : 0 ≤ t) (htN : t ≤ ↑N) :
    CauchySeq (fun n => f (dyadicFloorReal n t)) := by
  let C : ℝ := dyadicHolderFactor α * (∑ j ∈ range N, K j) * ((3 : ℝ) / 2) ^ α
  refine cauchySeq_of_le_geometric (r := (2 : ℝ) ^ (-α)) (C := C)
    (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 hα)) ?_
  intro n
  have hstep := abs_sub_dyadicFloor_levels hα hK hinc (Nat.le_succ n) ht0 htN
  have hpow := two_mesh_sum_rpow (α := α) n
  dsimp [C]
  calc
    dist (f (dyadicFloorReal n t)) (f (dyadicFloorReal (n + 1) t)) =
        |f (dyadicFloorReal (n + 1) t) - f (dyadicFloorReal n t)| := by
      rw [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm]
    _ ≤ dyadicHolderFactor α * (∑ j ∈ range N, K j) *
          (1 / 2 ^ n + 1 / 2 ^ (n + 1)) ^ α := hstep
    _ = C * ((2 : ℝ) ^ (-α)) ^ n := by rw [hpow]; ring

/-- The dyadic floors converge, and the limit is their `limUnder`. -/
lemma tendsto_dyadicFloor_limUnder {f : ℝ → ℝ} {α : ℝ} {K : ℕ → ℝ} {N : ℕ}
    (hα : 0 < α) (hK : ∀ j, j < N → 0 ≤ K j)
    (hinc : ∀ j, j < N → HasDyadicIncrements f α (K j) j)
    {t : ℝ} (ht0 : 0 ≤ t) (htN : t ≤ ↑N) :
    Tendsto (fun n => f (dyadicFloorReal n t)) atTop
      (𝓝 (limUnder atTop (fun n => f (dyadicFloorReal n t)))) :=
  (cauchySeq_dyadicFloor hα hK hinc ht0 htN).tendsto_limUnder

/-- Limits of dyadic floors are Hölder, with the summed dyadic constant. -/
lemma abs_sub_dyadicFloor_lim {f : ℝ → ℝ} {α : ℝ} {K : ℕ → ℝ} {N : ℕ}
    (hα : 0 < α) (hK : ∀ j, j < N → 0 ≤ K j)
    (hinc : ∀ j, j < N → HasDyadicIncrements f α (K j) j)
    {s t : ℝ} (hs0 : 0 ≤ s) (hsN : s ≤ ↑N) (ht0 : 0 ≤ t) (htN : t ≤ ↑N) :
    |limUnder atTop (fun n => f (dyadicFloorReal n t)) -
        limUnder atTop (fun n => f (dyadicFloorReal n s))| ≤
      dyadicHolderFactor α * (∑ j ∈ range N, K j) * |s - t| ^ α := by
  by_cases hst : s = t
  · subst hst
    simp [sub_self, abs_zero, Real.zero_rpow hα.ne']
  · have hcs := tendsto_dyadicFloor_limUnder hα hK hinc hs0 hsN
    have hct := tendsto_dyadicFloor_limUnder hα hK hinc ht0 htN
    have habs : Tendsto (fun n => |f (dyadicFloorReal n t) - f (dyadicFloorReal n s)|) atTop
        (𝓝 |limUnder atTop (fun n => f (dyadicFloorReal n t)) -
            limUnder atTop (fun n => f (dyadicFloorReal n s))|) :=
      (hct.sub hcs).abs
    have hmesh : Tendsto (fun n : ℕ => |s - t| + 1 / 2 ^ n) atTop (𝓝 |s - t|) := by
      have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)
      have hdiv : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
        simpa [div_pow, one_pow] using hpow
      simpa using tendsto_const_nhds.add hdiv
    have hrhs := (hmesh.rpow_const (p := α)
        (Or.inl (abs_ne_zero.2 (sub_ne_zero.2 hst)))).const_mul
      (dyadicHolderFactor α * ∑ j ∈ range N, K j)
    refine le_of_tendsto_of_tendsto' habs hrhs fun n => ?_
    exact abs_sub_dyadicFloor_le hα hK hinc hs0 hsN ht0 htN

end Brownian

end CKMA
