/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Complex.EntireGrowth.Product
public import TauCeti.Analysis.Complex.GrowthOrder
public import TauCeti.Analysis.Complex.Liouville

import CKMA.Analysis.Complex.EntireGrowth.LowerBound
import TauCeti.Analysis.Complex.BorelCaratheodory
import TauCeti.Analysis.Complex.DivisorFactorization
import TauCeti.Analysis.Convex.SimplyConnected
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Field

/-!
# Hadamard factorization at finite order

An entire function of order at most `ρ`, nonzero at the origin, is a polynomial exponential times
the canonical product of genus `⌊ρ⌋` over its zeros. The argument reuses the zero enumeration and
the genus product, compares zero counts with `TauCeti.OrderLE.eventually_sum_divisor_le`, and
controls the logarithm by dyadic annuli. Polynomial growth of the remaining entire logarithm is
`Differentiable.isBigO_of_cexp_isBigO`, and the degree bound is
`Differentiable.exists_eq_polynomial_eval_of_isLittleO_pow`. The zero counts are in
`CKMA.Analysis.Complex.EntireGrowth.ZeroCount` and the lower bound of the canonical product on
separated circles in `CKMA.Analysis.Complex.EntireGrowth.LowerBound`.

## Main results

* `CKMA.exists_hadamard_of_orderLE`: an entire `g` with `g 0 ≠ 0` and order at most `ρ ≥ 0` is
  `exp Q` times the genus-`⌊ρ⌋` canonical product over its zeros, with `deg Q ≤ ρ`, summable
  slope weights, and locally uniform convergence of the product.
-/

public section

noncomputable section

namespace CKMA

open Asymptotics Bornology Classical Complex Filter Finset MeasureTheory Metric Set Topology
open scoped BigOperators ENNReal

/-- A constant, a lower power, and that power times a logarithm are absorbed by a higher power. -/
private theorem eventually_growth_exponent_le {B t K C : ℝ} (hBt : B < t) (ht : 0 < t) :
    ∀ᶠ R : ℝ in atTop,
      Real.log C + R ^ B + |K| * R ^ B * (Real.log (2 * R) + 1) ≤ R ^ t := by
  have hpow := eventually_mul_rpow_le (a := B) (b := t) (C := 3 * (1 + |K|)) hBt
  have hlog := eventually_log_mul_rpow_le (a := B) (b := t) (C := 3 * |K|) hBt
  have hconst := (tendsto_rpow_atTop ht).eventually_ge_atTop (3 * Real.log C)
  filter_upwards [hpow, hlog, hconst] with R hRpow hRlog hRconst
  have hpow' : 3 * ((1 + |K|) * R ^ B) ≤ R ^ t := by
    simpa [mul_assoc] using hRpow
  have hlog' : 3 * (|K| * R ^ B * Real.log (2 * R)) ≤ R ^ t := by
    have hrw : 3 * (|K| * R ^ B * Real.log (2 * R)) =
        3 * |K| * R ^ B * Real.log (2 * R) := by ring
    rwa [hrw]
  have hsum : 3 * (Real.log C + (1 + |K|) * R ^ B + |K| * R ^ B * Real.log (2 * R)) ≤
      R ^ t + R ^ t + R ^ t := by
    have hdist : 3 * (Real.log C + (1 + |K|) * R ^ B + |K| * R ^ B * Real.log (2 * R)) =
        3 * Real.log C + 3 * ((1 + |K|) * R ^ B) +
          3 * (|K| * R ^ B * Real.log (2 * R)) := by ring
    rw [hdist]
    exact add_le_add (add_le_add hRconst hpow') hlog'
  have hthree : R ^ t + R ^ t + R ^ t = 3 * R ^ t := by ring
  have hmul : 3 * (Real.log C + (1 + |K|) * R ^ B + |K| * R ^ B * Real.log (2 * R)) ≤
      3 * R ^ t := by rwa [hthree] at hsum
  have heq : Real.log C + R ^ B + |K| * R ^ B * (Real.log (2 * R) + 1) =
      Real.log C + (1 + |K|) * R ^ B + |K| * R ^ B * Real.log (2 * R) := by ring
  rw [heq]
  exact le_of_mul_le_mul_left hmul (by norm_num)

/-- Hadamard factorization for an entire function of order at most `ρ` and nonzero at the origin.
The genus is `⌊ρ⌋`, and the polynomial has degree at most `ρ`. -/
theorem exists_hadamard_of_orderLE {g : ℂ → ℂ} (hg : Differentiable ℂ g) (hg0 : g 0 ≠ 0)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hord : TauCeti.OrderLE g ρ) :
    ∃ p : ℕ, ∃ Q : Polynomial ℂ, ∃ a : ℕ → Option ℂ,
      p = Nat.floor ρ ∧ (Q.natDegree : ℝ) ≤ ρ ∧
      (∀ n w, a n = some w → w ≠ 0) ∧
      Summable (slopeWeight p a) ∧
      (∀ z, Multipliable fun n ↦ genusFactor p a n z) ∧
      (∀ K : Set ℂ, IsCompact K → TendstoUniformlyOn
        (fun N z ↦ ∏ n ∈ range N, genusFactor p a n z)
        (fun z ↦ ∏' n, genusFactor p a n z) atTop K) ∧
      ∀ z, g z = exp (Q.eval z) * ∏' n, genusFactor p a n z := by
  classical
  let p : ℕ := Nat.floor ρ
  have hp_le : (p : ℝ) ≤ ρ := by simpa [p] using Nat.floor_le hρ
  have hp_lt : ρ < (p : ℝ) + 1 := by
    simpa [p] using Nat.lt_floor_add_one ρ
  let δ : ℝ := ((p : ℝ) + 1 - ρ) / 5
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let B : ℝ := ρ + δ
  let t' : ℝ := ρ + 3 * δ
  let u : ℝ := ρ + 4 * δ
  have hρB : ρ < B := by dsimp [B]; linarith
  have hBt : B < t' := by dsimp [B, t']; linarith
  have ht'u : t' < u := by dsimp [t', u]; linarith
  have huq : u < (p : ℝ) + 1 := by dsimp [u, δ]; linarith
  have hpB : (p : ℝ) < B := by linarith
  have hBq : B < (p : ℝ) + 1 := by dsimp [B, δ]; linarith
  have hB0 : 0 ≤ B := by dsimp [B]; linarith
  have ht'0 : 0 < t' := by dsimp [t']; linarith
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  let a : ℕ → Option ℂ := enumeratedZero hg
  have hne : ∀ n w, a n = some w → w ≠ 0 :=
    fun n w hw => enumeratedZero_ne_zero hg hg0 (by simpa [a] using hw)
  have hsum : Summable (slopeWeight p a) := by
    refine (summable_enumeratedZero_rpow hg hord hp_lt).congr fun n => ?_
    cases ha : enumeratedZero hg n with
    | none => simp [slopeWeight, a, ha]
    | some w => simp [slopeWeight, a, ha]
  have hfin : ∀ R : ℝ, {n | ∃ w, a n = some w ∧ ‖w‖ ≤ R}.Finite := by
    intro R
    simpa [a] using enumeratedBall_finite hg R
  obtain ⟨C, hCpos, hcount0⟩ := exists_uniform_enumerated_count hg hord hρB hB0
    (by norm_num : (1 : ℝ) ≤ 1)
  have hcount : ∀ R : ℝ, 1 ≤ R →
      (({n | ∃ w, a n = some w ∧ ‖w‖ ≤ R}.ncard : ℝ) ≤ C * R ^ B) := by
    intro R hR
    simpa [a] using hcount0 R hR
  obtain ⟨K, hK⟩ := exists_log_norm_tprod_lower (a := a) (p := p) (B := B) (C := C) (R0 := 1)
    hpB hBq hCpos.le (by norm_num) hsum hne hfin hcount
  obtain ⟨T0, hT0⟩ := exists_good_radius (a := a) (B := B) (q := (p : ℝ) + 1) (C := C)
    (R0 := 1) hBq (by positivity) hB0 hCpos.le hfin hcount
  obtain ⟨Cg, hCg, hWith⟩ := (hord.isBigO hρB).exists_pos
  rcases (hasBasis_cobounded_norm (E := ℂ)).eventually_iff.mp (isBigOWith_iff.mp hWith) with
    ⟨M, -, hM⟩
  have habsorb := eventually_growth_exponent_le (B := B) (t := t') (K := K) (C := Cg) hBt ht'0
  have hshift := eventually_mul_rpow_le (a := t') (b := u) (C := (2 : ℝ) ^ t') ht'u
  rw [eventually_atTop] at habsorb hshift
  obtain ⟨Rφ, hRφ⟩ := habsorb
  obtain ⟨R1, hR1⟩ := hshift
  let Rstar : ℝ := max (max (max M T0) Rφ) (max R1 1)
  have hRstarM : M ≤ Rstar :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hRstarT : T0 ≤ Rstar :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hRstarφ : Rφ ≤ Rstar := le_trans (le_max_right _ _) (le_max_left _ _)
  have hRstar1 : R1 ≤ Rstar := le_trans (le_max_left _ _) (le_max_right _ _)
  have hRstar_ge : 1 ≤ Rstar := le_trans (le_max_right _ _) (le_max_right _ _)
  let P : ℂ → ℂ := fun z => ∏' n, genusFactor p a n z
  have hPdiff : Differentiable ℂ P :=
    differentiable_tprod_genusFactor (p := p) (a := a) hsum hne
  have hP0 : P 0 = 1 := by
    simpa [P] using tprod_genusFactor_zero (p := p) (a := a)
  have hdiv : MeromorphicOn.divisor g Set.univ = MeromorphicOn.divisor P Set.univ := by
    ext w
    have hgA : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
    have hPA : AnalyticOnNhd ℂ P Set.univ := fun z _ => hPdiff.analyticAt z
    rw [hgA.meromorphicOn.divisor_eq_analyticOrderNatAt (hg.analyticAt w) (mem_univ w),
      hPA.meromorphicOn.divisor_eq_analyticOrderNatAt (hPdiff.analyticAt w) (mem_univ w)]
    congr 1
    have hAt : analyticOrderAt P w = (analyticOrderNatAt g w : ℕ∞) := by
      rw [show P = fun z => ∏' n, genusFactor p a n z from rfl,
        analyticOrderAt_tprod_genusFactor (p := p) (a := a) hsum hne w]
      simpa [a] using congrArg (Nat.cast : ℕ → ℕ∞) (enumeratedZero_ncard hg w)
    have hnat : analyticOrderNatAt P w = analyticOrderNatAt g w := by
      rw [analyticOrderNatAt, hAt, ENat.toNat_natCast]
    exact hnat.symm
  have hsc : IsSimplyConnected (Set.univ : Set ℂ) :=
    (convex_univ : Convex ℝ (Set.univ : Set ℂ)).isSimplyConnected ⟨(0 : ℂ), mem_univ 0⟩
  obtain ⟨L, hLdiff, hLeq⟩ := TauCeti.exists_differentiableOn_eqOn_mul_exp_of_divisor_eq hsc
    isOpen_univ (fun z _ => hg.analyticAt z) (fun z _ => hPdiff.analyticAt z)
    ⟨0, mem_univ 0, hg0⟩ ⟨0, mem_univ 0, by simp [hP0]⟩ hdiv
  have hL : Differentiable ℂ L := by
    intro z
    exact (hLdiff z (mem_univ z)).differentiableAt (isOpen_univ.mem_nhds (mem_univ z))
  have hcircle : ∀ {R : ℝ}, Rstar ≤ R →
      (∀ n w, a n = some w → |R - ‖w‖| < 1 → ‖w‖ ^ (-((p : ℝ) + 1)) ≤ |R - ‖w‖|) →
      ∀ z : ℂ, ‖z‖ = R → ‖exp (L z)‖ ≤ Real.exp (R ^ t') := by
    intro R hR hgood z hz
    have hR1 : 1 ≤ R := hRstar_ge.trans hR
    have hRM : M ≤ R := hRstarM.trans hR
    have hPne : P z ≠ 0 := by
      intro hzero
      have hsome := (tprod_genusFactor_eq_zero_iff (p := p) (a := a) hsum hne z).mp
        (by simpa [P] using hzero)
      obtain ⟨n, hn⟩ := hsome
      have hwn := (genusFactor_eq_zero_iff (fun w hw => hne n w hw)).mp hn
      have hsep := hgood n z hwn (by simp [hz])
      exact (not_le_of_gt (Real.rpow_pos_of_pos (norm_pos_iff.mpr (hne n z hwn)) _))
        (by simpa [hz] using hsep)
    have hlogP := hK hR1 hgood z hz
    have hgbound : ‖g z‖ ≤ Cg * Real.exp (R ^ B) := by
      have hraw := hM (le_of_le_of_eq hRM hz.symm)
      have hnorm : ‖Real.exp (‖z‖ ^ B)‖ = Real.exp (R ^ B) := by
        rw [hz, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact le_of_le_of_eq hraw (congrArg (fun t : ℝ => Cg * t) hnorm)
    have hquot : g z / P z = exp (L z) := by
      rw [hLeq (mem_univ z), mul_div_cancel_left₀ _ hPne]
    have hinv : (‖P z‖)⁻¹ = Real.exp (-Real.log ‖P z‖) := by
      calc
        (‖P z‖)⁻¹ = (Real.exp (Real.log ‖P z‖))⁻¹ := by
          rw [Real.exp_log (norm_pos_iff.mpr hPne)]
        _ = Real.exp (-Real.log ‖P z‖) := (Real.exp_neg _).symm
    have hdivle : ‖g z‖ / ‖P z‖ ≤ Cg * Real.exp (R ^ B) / ‖P z‖ :=
      div_le_div_of_nonneg_right hgbound (norm_nonneg _)
    have hneglog : -Real.log ‖P z‖ ≤ K * R ^ B * (Real.log (2 * R) + 1) := by linarith
    have habsK : K * R ^ B * (Real.log (2 * R) + 1) ≤
        |K| * R ^ B * (Real.log (2 * R) + 1) := by
      have hRpos : (0 : ℝ) ≤ R := (by norm_num : (0 : ℝ) ≤ 1).trans hR1
      have htwo : (1 : ℝ) ≤ 2 * R :=
        hR1.trans (le_mul_of_one_le_left hRpos (by norm_num : (1 : ℝ) ≤ 2))
      have hpos : 0 ≤ R ^ B * (Real.log (2 * R) + 1) :=
        mul_nonneg (Real.rpow_nonneg hRpos _)
          (add_nonneg (Real.log_nonneg htwo) (by norm_num))
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right (le_abs_self K) hpos
    have hlogexp : Real.log Cg + R ^ B - Real.log ‖P z‖ ≤
        Real.log Cg + R ^ B + |K| * R ^ B * (Real.log (2 * R) + 1) :=
      (sub_eq_add_neg (Real.log Cg + R ^ B) (Real.log ‖P z‖)).trans_le
        (add_le_add_right (hneglog.trans habsK) (Real.log Cg + R ^ B))
    calc
      ‖exp (L z)‖ = ‖g z‖ / ‖P z‖ := by rw [← hquot, norm_div]
      _ ≤ Cg * Real.exp (R ^ B) / ‖P z‖ := hdivle
      _ = Cg * Real.exp (R ^ B) * (‖P z‖)⁻¹ := by rw [div_eq_mul_inv]
      _ = Real.exp (Real.log Cg) * Real.exp (R ^ B) * (‖P z‖)⁻¹ := by
        conv_lhs => rw [← Real.exp_log hCg]
      _ = Real.exp (Real.log Cg) * Real.exp (R ^ B) * Real.exp (-Real.log ‖P z‖) := by
        rw [hinv]
      _ = Real.exp (Real.log Cg + R ^ B - Real.log ‖P z‖) := by
        rw [← Real.exp_add, ← Real.exp_add, sub_eq_add_neg]
      _ ≤ Real.exp (Real.log Cg + R ^ B + |K| * R ^ B * (Real.log (2 * R) + 1)) :=
        Real.exp_le_exp.mpr hlogexp
      _ ≤ Real.exp (R ^ t') := Real.exp_le_exp.mpr (hRφ R (hRstarφ.trans hR))
  have hgrow : (fun z => exp (L z)) =O[cobounded ℂ] (fun z => Real.exp (‖z‖ ^ u)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_cobounded_le_norm (E := ℂ) Rstar] with z hz
    obtain ⟨R, hRgt, hRle, hgood⟩ := hT0 ‖z‖ (hRstarT.trans hz)
    have hRstarR : Rstar ≤ R := by linarith
    have hfront : ∀ w ∈ frontier (ball (0 : ℂ) R), ‖exp (L w)‖ ≤ Real.exp (R ^ t') := by
      intro w hw
      have hnorm : ‖w‖ = R := by
        simpa [mem_sphere, dist_zero_right] using frontier_ball_subset_sphere hw
      exact hcircle hRstarR hgood w hnorm
    have hinside : z ∈ ball 0 R := by simpa [mem_ball, dist_zero_right] using hRgt
    have hmax := norm_le_of_forall_mem_frontier_norm_le isBounded_ball (hL.cexp).diffContOnCl
      hfront (subset_closure hinside)
    have hup : (‖z‖ + 1) ^ t' ≤ ‖z‖ ^ u := by
      have hle : ‖z‖ + 1 ≤ 2 * ‖z‖ := by linarith
      have hpow : (‖z‖ + 1) ^ t' ≤ (2 * ‖z‖) ^ t' :=
        Real.rpow_le_rpow (by linarith) hle ht'0.le
      have hsplit : (2 * ‖z‖) ^ t' = (2 : ℝ) ^ t' * ‖z‖ ^ t' :=
        Real.mul_rpow (by norm_num) (by linarith)
      have hmul := hR1 ‖z‖ (hRstar1.trans hz)
      exact hpow.trans (by rw [hsplit]; exact hmul)
    have hRt : R ^ t' ≤ ‖z‖ ^ u :=
      (Real.rpow_le_rpow (by linarith) hRle ht'0.le).trans hup
    have hexp : ‖exp (L z)‖ ≤ Real.exp (‖z‖ ^ u) := hmax.trans (Real.exp_le_exp.mpr hRt)
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hexp
  have hlittle : L =o[cobounded ℂ] (fun z => z ^ (p + 1)) := by
    refine (hL.isBigO_of_cexp_isBigO hu0 hgrow).trans_isLittleO ?_
    rw [isLittleO_iff]
    intro c hc
    have hpos : 0 < (p : ℝ) + 1 - u := by linarith
    have htend :=
      ((tendsto_rpow_neg_atTop hpos).comp (tendsto_norm_cobounded_atTop (E := ℂ))).eventually
        (Iio_mem_nhds hc)
    filter_upwards [htend, eventually_cobounded_le_norm (E := ℂ) (1 : ℝ)] with z hz hz1
    have hz0 : 0 < ‖z‖ := by linarith
    have hexp : ‖z‖ ^ (u - ((p : ℝ) + 1)) = ‖z‖ ^ (-((p : ℝ) + 1 - u)) := by
      congr 1
      ring
    have hsmall : ‖z‖ ^ (u - ((p : ℝ) + 1)) < c := by
      rw [hexp]
      simpa using hz
    have hsplit : ‖z‖ ^ u = ‖z‖ ^ (u - ((p : ℝ) + 1)) * ‖z‖ ^ ((p : ℝ) + 1) := by
      rw [← Real.rpow_add hz0, sub_add_cancel]
    have hnat : ‖z ^ (p + 1)‖ = ‖z‖ ^ ((p : ℝ) + 1) := by
      rw [norm_pow, ← Real.rpow_natCast]
      congr 1
      simp [Nat.cast_add, Nat.cast_one]
    have hnn : 0 ≤ ‖z‖ ^ ((p : ℝ) + 1) := Real.rpow_nonneg hz0.le _
    calc
      ‖(‖z‖ ^ u : ℝ)‖ = ‖z‖ ^ u := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      _ = ‖z‖ ^ (u - ((p : ℝ) + 1)) * ‖z‖ ^ ((p : ℝ) + 1) := hsplit
      _ ≤ c * ‖z‖ ^ ((p : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hsmall.le hnn
      _ = c * ‖z ^ (p + 1)‖ := by rw [hnat]
  obtain ⟨Q, hdeg, hQ⟩ := hL.exists_eq_polynomial_eval_of_isLittleO_pow (n := p) hlittle
  refine ⟨p, Q, a, rfl, ?_, hne, hsum, ?_, ?_, ?_⟩
  · exact (Nat.cast_le.mpr hdeg).trans hp_le
  · intro z
    exact multipliable_genusFactor (p := p) (a := a) hsum hne z
  · intro K hK
    exact tendstoUniformlyOn_genusFactor_range (p := p) (a := a) hsum hne hK
  · intro z
    rw [hLeq (mem_univ z), hQ, mul_comm]

end CKMA
