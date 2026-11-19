/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Analysis.Complex.GrowthOrder

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Removing the zero at the origin

An entire function that is not identically zero has finite vanishing order at `0`. Dividing out
`z ^ m` leaves an entire function of no greater order, normalized to be nonzero at the origin.
-/

public section

noncomputable section

namespace CKMA

open Complex Filter Function
open scoped Topology

/-- Iterated divided differences at the origin preserve entirety. -/
theorem differentiable_iterate_dslope {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} (hf : Differentiable ℂ f) (n : ℕ) :
    Differentiable ℂ ((swap dslope (0 : ℂ))^[n] f) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    rw [iterate_succ_apply']
    have hdiff : DifferentiableOn ℂ (dslope ((swap dslope (0 : ℂ))^[n] f) 0) Set.univ :=
      (differentiableOn_dslope Filter.univ_mem).2 ih.differentiableOn
    intro z
    exact (hdiff z (Set.mem_univ z)).differentiableAt (isOpen_univ.mem_nhds (Set.mem_univ z))

/-- The entire function obtained by dividing out the zero of finite order at the origin. -/
theorem exists_removedZero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : ∃ z, f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g 0 ≠ 0 ∧
      ∀ z, f z = z ^ analyticOrderNatAt f 0 * g z := by
  have hnot : ¬∀ᶠ z in 𝓝 (0 : ℂ), f z = 0 := by
    intro hz
    have htop : analyticOrderAt f 0 = ⊤ := analyticOrderAt_eq_top.mpr hz
    have hf0 : f = 0 :=
      (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (0 : ℂ)
        (fun z => hf.analyticAt z)).mp htop
    obtain ⟨z, hz⟩ := hne
    exact hz (congrFun hf0 z)
  rcases hf.analyticAt 0 with ⟨p, hp⟩
  have hp0 : p ≠ 0 := by
    intro h
    exact hnot (hp.locally_zero_iff.mpr h)
  set m : ℕ := p.order
  set g : ℂ → ℂ := (swap dslope (0 : ℂ))^[m] f
  have hfg (z : ℂ) : f z = z ^ m * g z := by
    simpa [g, m, sub_zero, smul_eq_mul] using hp.eq_pow_order_mul_iterate_dslope z
  have hg0 : g 0 ≠ 0 := hp.iterate_dslope_fslope_ne_zero hp0
  have hg : Differentiable ℂ g := differentiable_iterate_dslope hf m
  have hgA : AnalyticAt ℂ g 0 :=
    ⟨_, hp.has_fpower_series_iterate_dslope_fslope m⟩
  have htop : analyticOrderAt f 0 ≠ ⊤ := fun h => hnot (analyticOrderAt_eq_top.mp h)
  have hord : analyticOrderNatAt f 0 = m := by
    rw [(hf.analyticAt 0).analyticOrderNatAt_eq_iff htop]
    refine ⟨g, hgA, hg0, Eventually.of_forall fun z => ?_⟩
    rw [hfg z, sub_zero, smul_eq_mul]
  refine ⟨g, hg, hg0, ?_⟩
  intro z
  rw [hord]
  exact hfg z

/-- Dividing by `z ^ m` does not increase the order at infinity. -/
theorem orderLE_of_pow_mul {f g : ℂ → ℂ} {m : ℕ} {ρ : ℝ} (hf : TauCeti.OrderLE f ρ)
    (hfg : ∀ z, f z = z ^ m * g z) : TauCeti.OrderLE g ρ := by
  refine Asymptotics.IsBigO.orderLE ?_ hf
  apply Asymptotics.IsBigO.of_bound (1 : ℝ)
  filter_upwards [eventually_cobounded_le_norm (E := ℂ) (1 : ℝ)] with z hz
  have hpow : (1 : ℝ) ≤ ‖z ^ m‖ := by
    rw [norm_pow]
    exact one_le_pow₀ (a := ‖z‖) hz
  have hmul : ‖g z‖ ≤ ‖z ^ m‖ * ‖g z‖ :=
    le_mul_of_one_le_left (norm_nonneg _) hpow
  simpa [hfg z, norm_mul] using hmul

end CKMA
