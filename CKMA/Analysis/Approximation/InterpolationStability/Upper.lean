/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Approximation.InterpolationStability.Estimates

/-!
# Chebyshev-extrema Lebesgue upper bounds

An upper bound for the Lebesgue function and the Lebesgue constant of the Chebyshev extrema.
The matching midpoint lower bound is in
`CKMA.Analysis.Approximation.InterpolationStability.Lower`.

## Main results

* `CKMA.lebesgueFunction_chebyshev_upper`: uniform upper bound for the Chebyshev-extrema
  Lebesgue function on `[-1, 1]`.
* `CKMA.chebyshev_lebesgueConstant_upper_bound`: upper bound `(2 / π) log (n + 1) + C` for the
  Chebyshev-extrema Lebesgue constant.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Polynomial Real Polynomial.Chebyshev Finset Classical Lagrange
open scoped BigOperators

/-- Derivative of the left-cluster logarithm. -/
private lemma hasDerivAt_leftCluster (θ ψ : ℝ) (hsin : 0 < sin ((θ + ψ) / 2)) :
    HasDerivAt (fun φ => 2 * log (sin ((θ + φ) / 2))) (cot ((θ + ψ) / 2)) ψ := by
  have hu : HasDerivAt (fun φ : ℝ => (θ + φ) / 2) ((1 : ℝ) / 2) ψ := by
    simpa using ((hasDerivAt_id ψ).const_add θ).div_const 2
  convert (hu.sin.log hsin.ne').const_mul 2 using 1
  rw [cot_eq_cos_div_sin]
  field_simp [hsin.ne']

/-- Middle-index cotangent corrections are nonpositive on `(0, π / 2]`. -/
private lemma chebyshevLebesgueCorr_nonpos_of_between {n : ℕ} (hn : 1 ≤ n) {θ : ℝ}
    (hθ : θ ∈ Set.Ioc 0 (π / 2)) {i : Fin (n + 1)}
    (hbetween : Nat.floor ((n : ℝ) * θ / π) < i.val ∧
      i.val < n - Nat.floor ((n : ℝ) * θ / π)) :
    chebyshevLebesgueCorr n θ i ≤ 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let ν : ℝ := (n : ℝ) * θ / π
  let m : ℕ := Nat.floor ν
  have hν0 : 0 < ν := div_pos (mul_pos hn0 hθ.1) pi_pos
  have hνle : ν ≤ (n : ℝ) / 2 := by
    unfold ν
    rw [div_le_iff₀ pi_pos, div_mul_eq_mul_div]
    nlinarith [hθ.2, hn0, pi_pos]
  have hm_le_n : m ≤ n := by
    have hmν : (m : ℝ) ≤ n := (Nat.floor_le hν0.le).trans (hνle.trans (by linarith))
    exact_mod_cast hmν
  have hnot : m < i.val ∧ i.val < n - m := hbetween
  have hφgt : θ < nodeAngle n i := by
    unfold nodeAngle
    rw [lt_div_iff₀ hn0]
    have hiν : ν < (i.val : ℝ) := by
      have hsucc : (m : ℝ) + 1 ≤ i.val := by exact_mod_cast (Nat.succ_le_of_lt hnot.1)
      exact ((by simpa using Nat.lt_floor_add_one ν : ν < (m : ℝ) + 1)).trans_le hsucc
    have hθν : θ * n = π * ν := by unfold ν; field_simp
    nlinarith [pi_pos]
  have hφlt : nodeAngle n i < π - θ := by
    unfold nodeAngle
    rw [div_lt_iff₀ hn0]
    have hi_lt : (i.val : ℝ) < n - ν := by
      have hi_le : i.val ≤ n - m - 1 := by omega
      have hi_real : (i.val : ℝ) ≤ ((n - m - 1 : ℕ) : ℝ) := by exact_mod_cast hi_le
      have hfloor : ν < (m : ℝ) + 1 := by simpa using Nat.lt_floor_add_one ν
      have hcast : ((n - m - 1 : ℕ) : ℝ) = (n : ℝ) - m - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n - m), Nat.cast_sub hm_le_n]
        push_cast
        ring
      linarith
    have hright : (π - θ) * n = π * (n - ν) := by unfold ν; field_simp
    nlinarith [pi_pos]
  have hsign := chebyshevAngleSign_of_not_lt (n := n) (θ := θ) (i := i) (not_lt_of_gt hφgt)
  have havg : (θ + nodeAngle n i) / 2 ∈ Set.Ioo 0 (π / 2) := by
    refine ⟨by linarith [hθ.1, (nodeAngle_mem_Icc (by omega) i).1], ?_⟩
    linarith [hφlt]
  have hcot : 0 < cot ((θ + nodeAngle n i) / 2) := by
    rw [cot_eq_cos_div_sin]
    exact div_pos
      (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, havg.1], havg.2⟩)
      (sin_pos_of_pos_of_lt_pi havg.1 (havg.2.trans (by linarith [pi_pos])))
  unfold chebyshevLebesgueCorr
  rw [hsign]
  have hfac : 0 ≤ |sin ((n : ℝ) * θ)| / (2 * (n : ℝ) * chebyshevExtremalWeight n i) :=
    div_nonneg (abs_nonneg _)
      (mul_nonneg (by positivity) (chebyshevExtremalWeight_pos n i).le)
  nlinarith [mul_nonneg hfac hcot.le]

/-- Left interior cluster of cotangent corrections is bounded by `log 2 / π`. -/
private lemma sum_chebyshevLebesgueCorr_left_le {n m : ℕ} (hn : 1 ≤ n) (hm_lt : m < n)
    {θ : ℝ} (hθ : θ ∈ Set.Ioc 0 (π / 2)) (hθm : π * (m : ℝ) / n < θ) :
    ∑ k ∈ range m,
      (if hj : k + 1 < n + 1 then chebyshevLebesgueCorr n θ ⟨k + 1, hj⟩ else 0) ≤
      log 2 / π := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let Fc (j : ℕ) : ℝ :=
    if hj : j < n + 1 then chebyshevLebesgueCorr n θ ⟨j, hj⟩ else 0
  have hFc (j : ℕ) (hj : j ≤ n) : Fc j = chebyshevLebesgueCorr n θ ⟨j, by omega⟩ := by
    have hj' : j < n + 1 := by omega
    unfold Fc
    rw [dite_eq_left hj']
  have hsin1 : |sin ((n : ℝ) * θ)| ≤ 1 := abs_sin_le_one _
  let F (ψ : ℝ) : ℝ := 2 * log (sin ((θ + ψ) / 2))
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · simp [hm0]
    exact div_nonneg (log_nonneg (by norm_num)) pi_pos.le
  · have hcont : ContinuousOn F (Set.Icc 0 (π * (m : ℝ) / n)) := by
      refine ((continuous_sin.comp_continuousOn
        ((continuous_const.add continuous_id).div_const _).continuousOn).log ?_).const_mul 2
      intro ψ hψ
      have hlow : 0 < (θ + ψ) / 2 :=
        div_pos (add_pos_of_pos_of_nonneg hθ.1 hψ.1) (by norm_num)
      have hhigh : (θ + ψ) / 2 < π := by
        have hψθ : ψ < θ := lt_of_le_of_lt hψ.2 hθm
        have hhalf : (θ + ψ) / 2 < θ := by
          rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
          linarith
        exact hhalf.trans_le (hθ.2.trans (by linarith [pi_pos]))
      exact (sin_pos_of_pos_of_lt_pi hlow hhigh).ne'
    have hderivAll : ∀ ψ ∈ Set.Ioo 0 θ, HasDerivAt F (cot ((θ + ψ) / 2)) ψ := by
      intro ψ hψ
      exact hasDerivAt_leftCluster θ ψ
        (sin_pos_of_pos_of_lt_pi
          (div_pos (add_pos hθ.1 hψ.1) (by norm_num))
          (by
            have hhalf : (θ + ψ) / 2 < θ := by
              rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
              linarith [hψ.2]
            exact hhalf.trans_le (hθ.2.trans (by linarith [pi_pos]))))
    have hstep : ∀ k ∈ range m, Fc (k + 1) ≤ |sin ((n : ℝ) * θ)| / (2 * π) *
        (F (π * ((k + 1 : ℕ) : ℝ) / n) - F (π * (k : ℝ) / n)) := by
      intro k hk
      have hk' : k < m := Finset.mem_range.mp hk
      let a : ℝ := π * k / n
      let b : ℝ := π * (k + 1) / n
      have hab : a < b := by unfold a b; field_simp; linarith [pi_pos]
      have hbθ : b < θ := by
        unfold b
        have : (k + 1 : ℝ) ≤ m := by exact_mod_cast (Nat.succ_le_of_lt hk')
        have : π * (k + 1 : ℝ) / n ≤ π * (m : ℝ) / n := by gcongr
        linarith [hθm]
      have hkmul : (k + 1 : ℝ) ≤ m := by exact_mod_cast Nat.succ_le_of_lt hk'
      have hbTop : b ≤ π * (m : ℝ) / n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hkmul pi_pos.le) hn0.le
      have ha0 : (0 : ℝ) ≤ a := by unfold a; positivity
      have hcont' : ContinuousOn F (Set.Icc a b) :=
        hcont.mono (fun x hx => ⟨ha0.trans hx.1, hx.2.trans hbTop⟩)
      have hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt F (cot ((θ + x) / 2)) x :=
        fun x hx => hderivAll x ⟨ha0.trans_lt hx.1, hx.2.trans hbθ⟩
      obtain ⟨c, hc, hcEq⟩ := exists_hasDerivAt_eq_slope F (fun ψ => cot ((θ + ψ) / 2))
        hab hcont' hderiv
      have havg (x : ℝ) (hx0 : 0 ≤ x) (hxθ : x ≤ θ) :
          (θ + x) / 2 ∈ Set.Ioo 0 π := ⟨by linarith [hθ.1], by linarith [hθ.2, pi_pos]⟩
      have hc0 : 0 ≤ c := ha0.trans hc.1.le
      have hb0 : 0 ≤ b := by unfold b; positivity
      have hcotb : cot ((θ + b) / 2) ≤ cot ((θ + c) / 2) :=
        cot_antitone_Ioo (havg c hc0 (by linarith [hc.2, hbθ]))
          (havg b hb0 hbθ.le) (by
            rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by norm_num)]
            linarith [hc.2])
      have hba : b - a = π / n := by unfold a b; field_simp; ring
      have hcotle : cot ((θ + b) / 2) ≤ (F b - F a) * n / π := by
        have hcmp : cot ((θ + b) / 2) ≤ (F b - F a) / (b - a) := by rw [← hcEq]; exact hcotb
        have hrew : (F b - F a) / (π / n) = (F b - F a) * n / π := by field_simp
        rwa [hba, hrew] at hcmp
      have hi1 : k + 1 ≤ n := Nat.succ_le_of_lt (hk'.trans hm_lt)
      have hi1' : k + 1 < n + 1 := Nat.lt_succ_of_le hi1
      rw [hFc (k + 1) hi1]
      have hw : chebyshevExtremalWeight n ⟨k + 1, hi1'⟩ = 1 :=
        chebyshevExtremalWeight_of_interior (Nat.succ_ne_zero k)
          (Nat.ne_of_lt (Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hk') hm_lt))
      have hsign := chebyshevAngleSign_of_lt (n := n) (θ := θ)
        (i := ⟨k + 1, hi1'⟩) (by simpa [nodeAngle, b] using hbθ)
      unfold chebyshevLebesgueCorr
      rw [hw, hsign, show nodeAngle n ⟨k + 1, hi1'⟩ = b by simp [nodeAngle, b],
        show (2 : ℝ) * n * 1 = 2 * n by ring, mul_one]
      have hfac : 0 ≤ |sin ((n : ℝ) * θ)| / (2 * (n : ℝ)) := by positivity
      have hineq := mul_le_mul_of_nonneg_left hcotle hfac
      have hassoc : |sin ((n : ℝ) * θ)| / (2 * (n : ℝ)) * ((F b - F a) * n / π) =
          |sin ((n : ℝ) * θ)| / (2 * π) * (F b - F a) := by field_simp
      have hFab : F b - F a =
          F (π * ((k + 1 : ℕ) : ℝ) / n) - F (π * (k : ℝ) / n) := by
        unfold a b
        have hkcast : (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
        rw [hkcast]
      rw [hFab] at hineq hassoc
      exact hineq.trans_eq hassoc
    calc ∑ k ∈ range m, Fc (k + 1)
        ≤ ∑ k ∈ range m, |sin ((n : ℝ) * θ)| / (2 * π) *
            (F (π * ((k + 1 : ℕ) : ℝ) / n) - F (π * (k : ℝ) / n)) :=
          Finset.sum_le_sum hstep
      _ = |sin ((n : ℝ) * θ)| / (2 * π) *
            (F (π * (m : ℝ) / n) - F 0) := by
          rw [← Finset.mul_sum, sum_range_sub (fun k => F (π * (k : ℝ) / n)) m]
          simp
      _ ≤ log 2 / π := by
          have hdiff : F (π * (m : ℝ) / n) - F 0 ≤ 2 * log 2 := by
            have hhalf0 : 0 < θ / 2 := by linarith [hθ.1]
            have hsin_half : 0 < sin (θ / 2) :=
              sin_pos_of_pos_of_lt_pi hhalf0 (by linarith [hθ.2, pi_pos])
            have hmid0 : 0 < (θ + π * (m : ℝ) / n) / 2 :=
              div_pos (add_pos_of_pos_of_nonneg hθ.1 (by positivity)) (by norm_num)
            have hmidπ : (θ + π * (m : ℝ) / n) / 2 < π := by
              have hlt : (θ + π * (m : ℝ) / n) / 2 < θ := by
                rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
                linarith [hθm]
              exact hlt.trans_le (hθ.2.trans (le_of_lt (by linarith [pi_pos])))
            have hsin2 : 0 < sin ((θ + π * (m : ℝ) / n) / 2) :=
              sin_pos_of_pos_of_lt_pi hmid0 hmidπ
            have hle : sin ((θ + π * (m : ℝ) / n) / 2) ≤ sin θ :=
              sin_le_sin_of_le_of_le_pi_div_two
                (le_trans (by linarith [pi_pos] : -(π / 2) ≤ 0) hmid0.le) hθ.2 (by
                  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
                  linarith [hθm])
            have hdouble : sin θ = 2 * sin (θ / 2) * cos (θ / 2) := by
              have h := sin_two_mul (θ / 2)
              rwa [show 2 * (θ / 2) = θ by ring] at h
            have hratio : sin ((θ + π * (m : ℝ) / n) / 2) / sin (θ / 2) ≤ 2 := by
              have hmid : sin ((θ + π * (m : ℝ) / n) / 2) ≤
                  2 * cos (θ / 2) * sin (θ / 2) := by
                calc sin ((θ + π * (m : ℝ) / n) / 2)
                    ≤ sin θ := hle
                  _ = 2 * sin (θ / 2) * cos (θ / 2) := hdouble
                  _ = 2 * cos (θ / 2) * sin (θ / 2) := by ring
              rw [div_le_iff₀ hsin_half]
              exact hmid.trans (by nlinarith [cos_le_one (θ / 2), hsin_half.le])
            have hF : F (π * (m : ℝ) / n) - F 0 =
                2 * log (sin ((θ + π * (m : ℝ) / n) / 2) / sin (θ / 2)) := by
              unfold F
              rw [log_div hsin2.ne' hsin_half.ne']
              ring
            rw [hF]
            exact mul_le_mul_of_nonneg_left
              ((log_le_log (div_pos hsin2 hsin_half) hratio).trans_eq (by ring)) (by norm_num)
          have hcoef : 0 ≤ |sin ((n : ℝ) * θ)| / (2 * π) := by positivity
          have hineq := mul_le_mul_of_nonneg_left hdiff hcoef
          have hsmall : |sin ((n : ℝ) * θ)| / (2 * π) * (2 * log 2) ≤ log 2 / π := by
            have hlog : 0 ≤ log 2 := log_nonneg (by norm_num)
            have hrew : |sin ((n : ℝ) * θ)| / (2 * π) * (2 * log 2) =
                |sin ((n : ℝ) * θ)| * (2 * log 2) / (2 * π) := by ring
            rw [hrew]
            have hdiv : |sin ((n : ℝ) * θ)| * (2 * log 2) / (2 * π) ≤
                1 * (2 * log 2) / (2 * π) := by gcongr
            have hfin : 1 * (2 * log 2) / (2 * π) = log 2 / π := by ring
            exact hdiv.trans_eq hfin
          exact hineq.trans hsmall

/-- Right interior cluster of cotangent corrections is bounded by `1 / 4`. -/
private lemma sum_chebyshevLebesgueCorr_right_le {n m : ℕ} (hn : 1 ≤ n) (hm_lt : m < n)
    {θ : ℝ} (hθ : θ ∈ Set.Ioc 0 (π / 2)) (hm_lt_ν : (m : ℝ) < (n : ℝ) * θ / π) :
    ∑ k ∈ range m,
      (if hj : n - m + k < n + 1 then chebyshevLebesgueCorr n θ ⟨n - m + k, hj⟩ else 0) ≤
      1 / 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm_le_n : m ≤ n := hm_lt.le
  let ν : ℝ := (n : ℝ) * θ / π
  have hνle : ν ≤ (n : ℝ) / 2 := by
    unfold ν
    rw [div_le_iff₀ pi_pos, div_mul_eq_mul_div]
    nlinarith [hθ.2, hn0, pi_pos]
  let Fc (j : ℕ) : ℝ :=
    if hj : j < n + 1 then chebyshevLebesgueCorr n θ ⟨j, hj⟩ else 0
  have hFc (j : ℕ) (hj : j ≤ n) : Fc j = chebyshevLebesgueCorr n θ ⟨j, by omega⟩ := by
    have hj' : j < n + 1 := by omega
    unfold Fc
    rw [dite_eq_left hj']
  have hterm : ∀ k ∈ range m, Fc (n - m + k) ≤ 1 / (2 * (n : ℝ)) := by
    intro k hk
    have hk' : k < m := Finset.mem_range.mp hk
    have hi : n - m + k ≤ n := by
      calc n - m + k ≤ n - m + m := Nat.add_le_add_left (Nat.le_of_lt hk') _
        _ = n := Nat.sub_add_cancel hm_le_n
    have hi' : n - m + k < n + 1 := Nat.lt_succ_of_le hi
    rw [hFc (n - m + k) hi]
    have hltn : n - m + k < n := by
      have h1 : n - m + k < n - m + m := Nat.add_lt_add_left hk' _
      rwa [Nat.sub_add_cancel hm_le_n] at h1
    have hw : chebyshevExtremalWeight n ⟨n - m + k, hi'⟩ = 1 :=
      chebyshevExtremalWeight_of_interior
        (Nat.ne_of_gt (Nat.add_pos_left (Nat.sub_pos_of_lt hm_lt) k))
        (Nat.ne_of_lt hltn)
    have hcastφ : ((n - m + k : ℕ) : ℝ) = (n : ℝ) - m + k := by
      rw [Nat.cast_add, Nat.cast_sub hm_le_n]
    let φj : ℝ := π * (n - m + k : ℝ) / n
    have hφj : nodeAngle n ⟨n - m + k, hi'⟩ = φj := by
      simp only [nodeAngle, φj, hcastφ]
    have hgt : π - θ < φj := by
      unfold φj
      rw [lt_div_iff₀ hn0]
      have hbase : (n : ℝ) - ν < ((n - m : ℕ) : ℝ) := by
        rw [Nat.cast_sub hm_le_n]
        linarith [hm_lt_ν]
      have hkm : ((n - m : ℕ) : ℝ) ≤ (n - m + k : ℝ) := by
        exact_mod_cast Nat.le_add_right (n - m) k
      have hright : (π - θ) * n = π * (n - ν) := by unfold ν; field_simp
      nlinarith [pi_pos]
    have hsign := chebyshevAngleSign_of_not_lt (n := n) (θ := θ)
      (i := ⟨n - m + k, hi'⟩) (by
        rw [hφj]
        exact not_lt_of_gt (lt_of_le_of_lt (by linarith [hθ.2] : θ ≤ π - θ) hgt))
    have harg : (φj - (π - θ)) / 2 ≤ π / 4 := by
      have hφle : φj ≤ π := by
        unfold φj
        rw [div_le_iff₀ hn0, ← hcastφ]
        have hleR : ((n - m + k : ℕ) : ℝ) ≤ n := by exact_mod_cast hi
        nlinarith [pi_pos, hleR]
      linarith [hθ.2]
    have htan : tan ((φj - (π - θ)) / 2) ≤ 1 := by
      have hmono := strictMonoOn_tan.monotoneOn
      have hx : (φj - (π - θ)) / 2 ∈ Set.Ioo (-(π / 2)) (π / 2) :=
        ⟨by linarith [hgt], by linarith [harg, pi_pos]⟩
      have hy : π / 4 ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
      simpa [tan_pi_div_four] using hmono hx hy harg
    have hid : -cot ((θ + φj) / 2) = tan ((φj - (π - θ)) / 2) := by
      rw [cot_eq_cos_div_sin, tan_eq_sin_div_cos,
        show (φj - (π - θ)) / 2 = (θ + φj) / 2 - π / 2 by ring, sin_sub, cos_sub,
        sin_pi_div_two, cos_pi_div_two]
      have hsin : sin ((θ + φj) / 2) ≠ 0 := by
        apply (sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, hgt])
          (by linarith [hθ.2, pi_pos] : (θ + φj) / 2 < π)).ne'
      field_simp [hsin]
      ring
    have hprod : |sin ((n : ℝ) * θ)| / (2 * (n : ℝ) * 1) * -1 *
        cot ((θ + φj) / 2) =
        |sin ((n : ℝ) * θ)| / (2 * (n : ℝ)) * tan ((φj - (π - θ)) / 2) := by
      rw [← hid]
      ring
    unfold chebyshevLebesgueCorr
    rw [hw, hsign, hφj, hprod]
    have hfac : 0 ≤ tan ((φj - (π - θ)) / 2) / (2 * (n : ℝ)) := by
      have : 0 ≤ tan ((φj - (π - θ)) / 2) :=
        tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith [hgt]) (by linarith [harg, pi_pos])
      positivity
    have hineq := mul_le_mul_of_nonneg_right (abs_sin_le_one ((n : ℝ) * θ)) hfac
    have hrew : |sin ((n : ℝ) * θ)| * (tan ((φj - (π - θ)) / 2) / (2 * (n : ℝ))) =
        |sin ((n : ℝ) * θ)| / (2 * (n : ℝ)) * tan ((φj - (π - θ)) / 2) := by ring
    rw [← hrew]
    have hright : tan ((φj - (π - θ)) / 2) / (2 * (n : ℝ)) ≤ 1 / (2 * (n : ℝ)) :=
      div_le_div_of_nonneg_right htan (mul_nonneg (by norm_num) hn0.le)
    have hmul1 : 1 * (tan ((φj - (π - θ)) / 2) / (2 * (n : ℝ))) =
        tan ((φj - (π - θ)) / 2) / (2 * (n : ℝ)) := by ring
    exact hineq.trans ((le_of_eq hmul1).trans hright)
  calc ∑ k ∈ range m, Fc (n - m + k)
      ≤ ∑ k ∈ range m, (1 : ℝ) / (2 * n) := Finset.sum_le_sum hterm
    _ = (m : ℝ) / (2 * n) := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ 1 / 4 := by
        have hmhalf : (m : ℝ) ≤ n / 2 := by linarith [hm_lt_ν, hνle]
        have hdiv := div_le_div_of_nonneg_right hmhalf
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hn0.le)
        have hrew : (n : ℝ) / 2 / (2 * n) = 1 / 4 := by field_simp; ring
        exact hdiv.trans_eq hrew

/-- Positive cotangent corrections on `(0, π/2]` sum to an absolute constant. -/
private lemma sum_chebyshevLebesgueCorr_le {n : ℕ} (hn : 1 ≤ n) {θ : ℝ}
    (hθ : θ ∈ Set.Ioc 0 (π / 2)) (hnode : ∀ i, θ ≠ nodeAngle n i) :
    ∑ i, chebyshevLebesgueCorr n θ i ≤ 3 / 4 + π / 8 + log 2 / π := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let ν : ℝ := (n : ℝ) * θ / π
  let m : ℕ := Nat.floor ν
  have hν0 : 0 < ν := div_pos (mul_pos hn0 hθ.1) pi_pos
  have hνle : ν ≤ (n : ℝ) / 2 := by
    unfold ν
    rw [div_le_iff₀ pi_pos, div_mul_eq_mul_div]
    nlinarith [hθ.2, hn0, pi_pos]
  have hm_le_n : m ≤ n := by
    have hmν : (m : ℝ) ≤ n := (Nat.floor_le hν0.le).trans (hνle.trans (by linarith))
    exact_mod_cast hmν
  have hm_fin : m < n + 1 := Nat.lt_succ_of_le hm_le_n
  have hm_lt_ν : (m : ℝ) < ν := by
    refine lt_of_le_of_ne (Nat.floor_le hν0.le) ?_
    intro hνeq
    have hθeq : θ = nodeAngle n ⟨m, hm_fin⟩ := by
      simp only [nodeAngle]
      rw [hνeq]
      unfold ν
      field_simp
    exact hnode ⟨m, hm_fin⟩ hθeq
  have hsep : m < n - m := by
    have h2 : (2 : ℝ) * m < n := by linarith [hm_lt_ν, hνle]
    have h2n : 2 * m < n := by exact_mod_cast h2
    omega
  have hm_lt : m < n := by omega
  let Fc (j : ℕ) : ℝ :=
    if hj : j < n + 1 then chebyshevLebesgueCorr n θ ⟨j, hj⟩ else 0
  have hFc (j : ℕ) (hj : j ≤ n) : Fc j = chebyshevLebesgueCorr n θ ⟨j, by omega⟩ := by
    have hj' : j < n + 1 := by omega
    unfold Fc
    rw [dite_eq_left hj']
  have hdrop : ∑ i, chebyshevLebesgueCorr n θ i ≤
      ∑ i ∈ univ.filter (fun i : Fin (n + 1) => i.val ≤ m ∨ n - m ≤ i.val),
        chebyshevLebesgueCorr n θ i := by
    have hadd := Finset.sum_filter_add_sum_filter_not univ
      (fun i : Fin (n + 1) => i.val ≤ m ∨ n - m ≤ i.val)
      (fun i => chebyshevLebesgueCorr n θ i)
    have hneg : ∑ i ∈ univ.filter (fun i : Fin (n + 1) =>
        ¬ (i.val ≤ m ∨ n - m ≤ i.val)), chebyshevLebesgueCorr n θ i ≤ 0 := by
      refine Finset.sum_nonpos fun i hi => ?_
      have h := (Finset.mem_filter.mp hi).2
      exact chebyshevLebesgueCorr_nonpos_of_between hn hθ ⟨by change m < i.val; omega, by change i.val < n - m; omega⟩
    rw [← hadd]
    exact add_le_of_nonpos_right hneg
  have hdisj : Disjoint (univ.filter (fun i : Fin (n + 1) => i.val ≤ m))
      (univ.filter (fun i : Fin (n + 1) => n - m ≤ i.val)) := by
    rw [Finset.disjoint_filter]
    intro i _ hle hge
    omega
  have hunion := Finset.filter_or (fun i : Fin (n + 1) => i.val ≤ m)
    (fun i : Fin (n + 1) => n - m ≤ i.val) univ
  have hleftIdx : ∑ i ∈ univ.filter (fun i : Fin (n + 1) => i.val ≤ m),
        chebyshevLebesgueCorr n θ i = ∑ j ∈ range (m + 1), Fc j := by
    refine Finset.sum_bij' (fun i _ => i.val)
      (fun j hj => ⟨j, Nat.lt_succ_of_le
        ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans hm_le_n)⟩)
      (fun i hi => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hi).2))
      (fun j hj => Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)⟩)
      (fun i _ => by ext; rfl) (fun j _ => rfl)
      (fun i hi => (hFc i.val ((Finset.mem_filter.mp hi).2.trans hm_le_n)).symm)
  have hrightIdx : ∑ i ∈ univ.filter (fun i : Fin (n + 1) => n - m ≤ i.val),
        chebyshevLebesgueCorr n θ i = ∑ k ∈ range (m + 1), Fc (n - m + k) := by
    refine Finset.sum_bij' (fun i _ => i.val - (n - m))
      (fun k hk => ⟨n - m + k, by
        have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        exact Nat.lt_succ_of_le (by
          calc n - m + k ≤ n - m + m := Nat.add_le_add_left hk' _
            _ = n := Nat.sub_add_cancel hm_le_n)⟩)
      (fun i hi => Finset.mem_range.mpr (by
        have hle : i.val - (n - m) ≤ n - (n - m) :=
          Nat.sub_le_sub_right (Nat.le_of_lt_succ i.isLt) _
        rw [Nat.sub_sub_self hm_le_n] at hle
        exact Nat.lt_succ_of_le hle))
      (fun k _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_add_right _ _⟩)
      (fun i hi => by
        apply Fin.ext
        exact Nat.add_sub_of_le (Finset.mem_filter.mp hi).2)
      (fun k _ => Nat.add_sub_cancel_left (n - m) k)
      (fun i hi => by
        have hidx : n - m + (i.val - (n - m)) = i.val :=
          Nat.add_sub_of_le (Finset.mem_filter.mp hi).2
        rw [hidx]
        exact (hFc i.val (Nat.le_of_lt_succ i.isLt)).symm)
  rw [hunion, Finset.sum_union hdisj] at hdrop
  have hzero : Fc 0 ≤ 1 / 2 := by rw [hFc 0 (by omega)]; exact chebyshevLebesgueCorr_zero_le hn hθ
  have hlast : Fc n ≤ π / 8 := by rw [hFc n (by omega)]; exact chebyshevLebesgueCorr_last_le hn hθ
  have hθm : π * (m : ℝ) / n < θ := by
    have hθν : θ * n = π * ν := by unfold ν; field_simp
    rw [div_lt_iff₀ hn0]
    nlinarith [hm_lt_ν, pi_pos, hθν]
  have hleftInt : ∑ k ∈ range m, Fc (k + 1) ≤ log 2 / π :=
    sum_chebyshevLebesgueCorr_left_le hn hm_lt hθ hθm
  have hrightInt : ∑ k ∈ range m, Fc (n - m + k) ≤ 1 / 4 :=
    sum_chebyshevLebesgueCorr_right_le hn hm_lt hθ hm_lt_ν
  have hleftSum : ∑ j ∈ range (m + 1), Fc j ≤ log 2 / π + 1 / 2 := by
    rw [Finset.sum_range_succ' Fc m]
    exact add_le_add hleftInt hzero
  have hnm : n - m + m = n := by omega
  have hrightSum : ∑ k ∈ range (m + 1), Fc (n - m + k) ≤ 1 / 4 + π / 8 := by
    rw [Finset.sum_range_succ (fun k => Fc (n - m + k)) m, hnm]
    exact add_le_add hrightInt hlast
  calc ∑ i, chebyshevLebesgueCorr n θ i
      ≤ (∑ i ∈ univ.filter (fun i : Fin (n + 1) => i.val ≤ m),
            chebyshevLebesgueCorr n θ i) +
          ∑ i ∈ univ.filter (fun i : Fin (n + 1) => n - m ≤ i.val),
            chebyshevLebesgueCorr n θ i := hdrop
    _ = (∑ j ∈ range (m + 1), Fc j) + ∑ k ∈ range (m + 1), Fc (n - m + k) := by
        rw [hleftIdx, hrightIdx]
    _ ≤ (log 2 / π + 1 / 2) + (1 / 4 + π / 8) := add_le_add hleftSum hrightSum
    _ = 3 / 4 + π / 8 + log 2 / π := by ring

/-- Lebesgue values on the right half of `(0, π]` fold to the left half. -/
private lemma lebesgueFunction_Ioc_le {n : ℕ} (hn : 1 ≤ n) {θ : ℝ}
    (hθ : θ ∈ Set.Ioc 0 (π / 2)) :
    lebesgueFunction (chebyshevExtremalNodes n) (cos θ) ≤
      (2 / π) * log ((n : ℝ) + 1) + chebyshevLebesgueSlack := by
  have hlog0 : 0 ≤ log ((n : ℝ) + 1) :=
    log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hone : (1 : ℝ) ≤ (2 / π) * log ((n : ℝ) + 1) + chebyshevLebesgueSlack := by
    have hcoef : 0 ≤ 2 / π := by positivity
    linarith [one_le_chebyshevLebesgueSlack, mul_nonneg hcoef hlog0]
  by_cases hnode : ∀ i, θ ≠ nodeAngle n i
  · have hopen : θ ∈ Set.Ioo 0 π := ⟨hθ.1, hθ.2.trans_lt (by linarith [pi_pos])⟩
    rw [lebesgueFunction_cos_eq hn hopen hnode]
    have hmain := sum_chebyshevLebesgueMain_le hn hopen hnode
    have hcorr := sum_chebyshevLebesgueCorr_le hn hθ hnode
    unfold chebyshevLebesgueSlack
    linarith
  · have hex : ∃ i, θ = nodeAngle n i := by simpa using hnode
    obtain ⟨i, hi⟩ := hex
    rw [show cos θ = chebyshevExtremalNodes n i by rw [hi, chebyshevExtremalNodes_eq_cos],
      lebesgueFunction_chebyshev_node (by omega) i]
    exact hone

/-- Uniform bound for the extremal Lebesgue function on `[-1, 1]`. -/
lemma lebesgueFunction_chebyshev_upper {n : ℕ} (hn : 1 ≤ n) {t : ℝ}
    (ht : t ∈ Set.Icc (-1) 1) :
    lebesgueFunction (chebyshevExtremalNodes n) t ≤
      (2 / π) * log ((n : ℝ) + 1) + chebyshevLebesgueSlack := by
  let θ : ℝ := arccos t
  have hθmem : θ ∈ Set.Icc 0 π := ⟨arccos_nonneg t, arccos_le_pi t⟩
  have htθ : cos θ = t := cos_arccos ht.1 ht.2
  have hlog0 : 0 ≤ log ((n : ℝ) + 1) :=
    log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hone : (1 : ℝ) ≤ (2 / π) * log ((n : ℝ) + 1) + chebyshevLebesgueSlack := by
    linarith [one_le_chebyshevLebesgueSlack, mul_nonneg (by positivity : 0 ≤ 2 / π) hlog0]
  rw [← htθ]
  by_cases h0 : θ = 0
  · have hnode : chebyshevExtremalNodes n ⟨0, by omega⟩ = cos θ := by
      simp [chebyshevExtremalNodes, h0, cos_zero]
    rw [← hnode, lebesgueFunction_chebyshev_node (by omega)]
    exact hone
  by_cases hπ : θ = π
  · have hnode : chebyshevExtremalNodes n ⟨n, by omega⟩ = cos θ := by
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      simp [chebyshevExtremalNodes, hπ, hn0, cos_pi]
    rw [← hnode, lebesgueFunction_chebyshev_node (by omega)]
    exact hone
  have hopen : 0 < θ ∧ θ < π := ⟨lt_of_le_of_ne hθmem.1 (Ne.symm h0), lt_of_le_of_ne hθmem.2 hπ⟩
  by_cases hhalf : θ ≤ π / 2
  · exact lebesgueFunction_Ioc_le hn ⟨hopen.1, hhalf⟩
  · have hθ' : π - θ ∈ Set.Ioc 0 (π / 2) := by
      constructor
      · linarith [hopen.2]
      · linarith [hθmem.1]
    have hcos : cos θ = -cos (π - θ) := by
      calc
        cos θ = - -cos θ := (neg_neg _).symm
        _ = -cos (π - θ) := congrArg Neg.neg (cos_pi_sub θ).symm
    rw [hcos, lebesgueFunction_neg hn]
    exact lebesgueFunction_Ioc_le hn hθ'

/-- Upper bound `(2 / π) log (n + 1) + C` for the Chebyshev-extrema Lebesgue constant. -/
theorem chebyshev_lebesgueConstant_upper_bound (n : ℕ) :
    interpolationLebesgueConstant (chebyshevExtremalNodes n) ≤
      (2 / Real.pi) * Real.log (n + 1) + chebyshevLebesgueSlack := by
  by_cases hn0 : n = 0
  · subst hn0
    rw [interpolationLebesgueConstant_chebyshev_zero, Nat.cast_zero, zero_add, Real.log_one,
      mul_zero, zero_add]
    exact one_le_chebyshevLebesgueSlack
  · have hn : 1 ≤ n := by omega
    rw [interpolationLebesgueConstant]
    refine csSup_le ⟨lebesgueFunction (chebyshevExtremalNodes n) 0, 0, by norm_num, rfl⟩ ?_
    rintro _ ⟨t, ht, rfl⟩
    exact lebesgueFunction_chebyshev_upper hn ht

end CKMA
