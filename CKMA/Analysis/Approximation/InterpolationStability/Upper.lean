/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Approximation.InterpolationStability.Estimates

public import CKMA.Analysis.Approximation.Polynomial
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Chebyshev-extrema Lebesgue bounds

An upper bound for the Lebesgue function of the Chebyshev extrema and a matching
lower bound at one midpoint. The logarithmic comparison is in
`CKMA.Analysis.Approximation.InterpolationStability`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Polynomial
open scoped BigOperators

open Real Polynomial.Chebyshev Finset Classical Lagrange

/-- Derivative of the left-cluster logarithm. -/
private lemma hasDerivAt_leftCluster (θ ψ : ℝ) (hsin : 0 < sin ((θ + ψ) / 2)) :
    HasDerivAt (fun φ => 2 * log (sin ((θ + φ) / 2))) (cot ((θ + ψ) / 2)) ψ := by
  have hu : HasDerivAt (fun φ : ℝ => (θ + φ) / 2) ((1 : ℝ) / 2) ψ := by
    simpa using ((hasDerivAt_id ψ).const_add θ).div_const 2
  convert (hu.sin.log hsin.ne').const_mul 2 using 1
  rw [cot_eq_cos_div_sin]
  field_simp [hsin.ne']

/-- Positive cotangent corrections on `(0, π/2]` sum to an absolute constant. -/
private lemma sum_chebyshevLebesgueCorr_le {n : ℕ} (hn : 1 ≤ n) {θ : ℝ}
    (hθ : θ ∈ Set.Ioc 0 (π / 2)) (hnode : ∀ i, θ ≠ nodeAngle n i) :
    ∑ i, chebyshevLebesgueCorr n θ i ≤ 3 / 4 + π / 8 + log 2 / π := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnpos : (n : ℝ) ≠ 0 := hn0.ne'
  let ν : ℝ := (n : ℝ) * θ / π
  let m : ℕ := Nat.floor ν
  have hν0 : 0 < ν := by unfold ν; exact div_pos (mul_pos hn0 hθ.1) pi_pos
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
      have hnot : m < i.val ∧ i.val < n - m := by
        have h := (Finset.mem_filter.mp hi).2
        omega
      have hφgt : θ < nodeAngle n i := by
        unfold nodeAngle
        rw [lt_div_iff₀ hn0]
        have hiν : ν < (i.val : ℝ) := by
          have hsucc : (m : ℝ) + 1 ≤ i.val := by
            exact_mod_cast (Nat.succ_le_of_lt hnot.1)
          exact ((by simpa using Nat.lt_floor_add_one ν : ν < (m : ℝ) + 1)).trans_le hsucc
        have hθν : θ * n = π * ν := by
          unfold ν
          field_simp
        nlinarith [pi_pos]
      have hφlt : nodeAngle n i < π - θ := by
        unfold nodeAngle
        rw [div_lt_iff₀ hn0]
        have hi_lt : (i.val : ℝ) < n - ν := by
          have hi_le : i.val ≤ n - m - 1 := by omega
          have hi_real : (i.val : ℝ) ≤ ((n - m - 1 : ℕ) : ℝ) := by exact_mod_cast hi_le
          have hfloor : ν < (m : ℝ) + 1 := by simpa using Nat.lt_floor_add_one ν
          have hcast : ((n - m - 1 : ℕ) : ℝ) = (n : ℝ) - m - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ n - m), Nat.cast_sub (by omega : m ≤ n)]
            push_cast
            ring
          linarith
        have hright : (π - θ) * n = π * (n - ν) := by
          unfold ν
          field_simp
        nlinarith [pi_pos]
      have hsign := chebyshevAngleSign_of_not_lt (n := n) (θ := θ) (i := i)
        (not_lt_of_gt hφgt)
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
      have hfac : 0 ≤ |sin ((n : ℝ) * θ)| /
          (2 * (n : ℝ) * chebyshevExtremalWeight n i) :=
        div_nonneg (abs_nonneg _)
          (mul_nonneg (by positivity) (chebyshevExtremalWeight_pos n i).le)
      nlinarith [mul_nonneg hfac hcot.le]
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
      (fun k hk => Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_add_right _ _⟩)
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
  have hsin1 : |sin ((n : ℝ) * θ)| ≤ 1 := abs_sin_le_one _
  have hθm : π * (m : ℝ) / n < θ := by
    have hθν : θ * n = π * ν := by
      unfold ν
      field_simp
    rw [div_lt_iff₀ hn0]
    nlinarith [hm_lt_ν, pi_pos, hθν]
  let F (ψ : ℝ) : ℝ := 2 * log (sin ((θ + ψ) / 2))
  have hleftInt : ∑ k ∈ range m, Fc (k + 1) ≤ log 2 / π := by
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
          have hsum : θ + ψ < 2 * θ := by linarith
          have hhalf : (θ + ψ) / 2 < θ := by
            rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
            linarith
          exact hhalf.trans_le (hθ.2.trans (by linarith [pi_pos]))
        exact (sin_pos_of_pos_of_lt_pi hlow hhigh).ne'
      have hderivAll : ∀ ψ ∈ Set.Ioo 0 θ,
          HasDerivAt F (cot ((θ + ψ) / 2)) ψ := by
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
        have hbTop : b ≤ π * (m : ℝ) / n := by
          unfold b
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hkmul pi_pos.le) hn0.le
        have ha0 : (0 : ℝ) ≤ a := by unfold a; positivity
        have hcont' : ContinuousOn F (Set.Icc a b) :=
          hcont.mono (by
            intro x hx
            rcases hx with ⟨hxa, hxb⟩
            exact ⟨ha0.trans hxa, hxb.trans hbTop⟩)
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
          have hcmp : cot ((θ + b) / 2) ≤ (F b - F a) / (b - a) := by
            rw [← hcEq]
            exact hcotb
          have hrew : (F b - F a) / (π / n) = (F b - F a) * n / π := by
            field_simp
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
              have hsin1 : 0 < sin (θ / 2) :=
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
                rw [div_le_iff₀ hsin1]
                exact hmid.trans (by nlinarith [cos_le_one (θ / 2), hsin1.le])
              have hF : F (π * (m : ℝ) / n) - F 0 =
                  2 * log (sin ((θ + π * (m : ℝ) / n) / 2) / sin (θ / 2)) := by
                unfold F
                rw [log_div hsin2.ne' hsin1.ne']
                ring
              rw [hF]
              exact mul_le_mul_of_nonneg_left
                ((log_le_log (div_pos hsin2 hsin1) hratio).trans_eq (by ring)) (by norm_num)
            have hcoef : 0 ≤ |sin ((n : ℝ) * θ)| / (2 * π) := by positivity
            have hineq := mul_le_mul_of_nonneg_left hdiff hcoef
            have hsmall : |sin ((n : ℝ) * θ)| / (2 * π) * (2 * log 2) ≤ log 2 / π := by
              have hlog : 0 ≤ log 2 := log_nonneg (by norm_num)
              have hineq' := mul_le_mul_of_nonneg_right hsin1
                (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlog)
              have hrew : |sin ((n : ℝ) * θ)| / (2 * π) * (2 * log 2) =
                  |sin ((n : ℝ) * θ)| * (2 * log 2) / (2 * π) := by ring
              rw [hrew]
              have hdiv : |sin ((n : ℝ) * θ)| * (2 * log 2) / (2 * π) ≤
                  1 * (2 * log 2) / (2 * π) := by
                gcongr
              have hfin : 1 * (2 * log 2) / (2 * π) = log 2 / π := by ring
              exact hdiv.trans_eq hfin
            exact hineq.trans hsmall
  have hrightInt : ∑ k ∈ range m, Fc (n - m + k) ≤ 1 / 4 := by
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
          rw [Nat.cast_sub (by omega : m ≤ n)]
          linarith [hm_lt_ν]
        have hkm : ((n - m : ℕ) : ℝ) ≤ (n - m + k : ℝ) := by
          exact_mod_cast Nat.le_add_right (n - m) k
        have hright : (π - θ) * n = π * (n - ν) := by
          unfold ν
          field_simp
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

/-- Half-integer reciprocals dominate `log(2q + 3)`. -/
private lemma sum_half_ge_log (q : ℕ) :
    log (2 * (q : ℝ) + 3) ≤ ∑ k ∈ range (q + 1), (1 : ℝ) / ((k : ℝ) + 1 / 2) := by
  have hcoeff (k : ℕ) :
      (1 : ℝ) / ((k : ℝ) + 1 / 2) = 2 * (1 / (2 * (k : ℝ) + 1)) := by
    field_simp
  simp_rw [hcoeff]
  rw [← Finset.mul_sum]
  have h := sum_odd_reciprocal_ge_log q
  linarith

/-- Off the nodes, the Lebesgue function is the sum of main and correction terms. -/
private lemma lebesgueFunction_cos_eq {n : ℕ} (hn : 1 ≤ n) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 π) (hnode : ∀ i, θ ≠ nodeAngle n i) :
    lebesgueFunction (chebyshevExtremalNodes n) (cos θ) =
      (∑ i, chebyshevLebesgueMain n θ i) + ∑ i, chebyshevLebesgueCorr n θ i := by
  unfold lebesgueFunction
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => abs_cardinal_eq_main_add_corr hn hθ hnode i

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

set_option maxHeartbeats 1000000 in
/-- The central angular midpoint sees the full logarithmic growth. -/
lemma lebesgueFunction_chebyshev_midpoint_ge {n : ℕ} (hn : 1 ≤ n) :
    (2 / π) * log ((n : ℝ) + 1) - (2 / π + π / 4 + 1 / 2) ≤
      lebesgueFunction (chebyshevExtremalNodes n)
        (cos ((((n - 1) / 2 : ℕ) + (1 : ℝ) / 2) * π / n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let q : ℕ := (n - 1) / 2
  let ν : ℝ := (q : ℝ) + 1 / 2
  let θ : ℝ := ν * π / n
  have hθdef : θ = ((((n - 1) / 2 : ℕ) : ℝ) + 1 / 2) * π / n := rfl
  have hνpos : 0 < ν := by unfold ν; positivity
  have hνle : ν ≤ (n : ℝ) / 2 := by
    have hq : (q : ℝ) ≤ ((n - 1 : ℕ) : ℝ) / 2 := Nat.cast_div_le
    have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      simp
    unfold ν
    linarith
  have hθmem : θ ∈ Set.Ioc 0 (π / 2) := by
    refine ⟨by unfold θ; positivity, ?_⟩
    unfold θ
    rw [div_le_iff₀ hn0]
    nlinarith [hνle, pi_pos]
  have hnode : ∀ i, θ ≠ nodeAngle n i := by
    intro i hi
    have hval : (i.val : ℝ) = ν := by
      unfold nodeAngle at hi
      have hθv : θ = π * ν / n := by unfold θ; ring
      rw [hθv] at hi
      field_simp at hi
      linarith
    have heven : (2 : ℝ) * i.val = 2 * (q : ℝ) + 1 := by
      unfold ν at hval
      linarith
    have hnat : 2 * i.val = 2 * q + 1 := by exact_mod_cast heven
    omega
  have hsin : |sin ((n : ℝ) * θ)| = 1 := by
    have harg : (n : ℝ) * θ = (q : ℝ) * π + π / 2 := by
      unfold θ ν; field_simp
    rw [harg, sin_add, sin_nat_mul_pi, cos_nat_mul_pi, sin_pi_div_two, cos_pi_div_two]
    simp only [mul_zero, zero_add, mul_one]
    exact abs_neg_one_pow q
  have hopen : θ ∈ Set.Ioo 0 π := ⟨hθmem.1, hθmem.2.trans_lt (by linarith [pi_pos])⟩
  have hcosarg : ((((n - 1) / 2 : ℕ) + (1 : ℝ) / 2) * π / n) = θ := by
    simp only [θ, ν, q]
  rw [hcosarg, lebesgueFunction_cos_eq hn hopen hnode]
  let d : Fin (n + 1) → ℝ := fun i => |(i.val : ℝ) - ν|
  let wt : Fin (n + 1) → ℝ := fun i => chebyshevExtremalWeight n i
  have hdiv' : n - 1 = 2 * q + (n - 1) % 2 := by
    have h := Nat.div_add_mod (n - 1) 2
    omega
  have hqle : q + 1 ≤ n - q := by
    have h2q : 2 * q ≤ n - 1 := by omega
    omega
  have hlogCmp : log ((n : ℝ) + 1) ≤ log (2 * (q : ℝ) + 3) := by
    have hr : (n - 1) % 2 ≤ 1 := by
      have hlt := Nat.mod_lt (n - 1) (by decide : 0 < 2)
      omega
    have hcast : (n : ℝ) = 2 * (q : ℝ) + (Nat.cast ((n - 1) % 2) : ℝ) + 1 := by
      have h1 := congrArg (Nat.cast : ℕ → ℝ) hdiv'
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h1
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at h1
      linarith
    have hrR : (Nat.cast ((n - 1) % 2) : ℝ) ≤ 1 := by
      simpa using (Nat.cast_le (α := ℝ)).mpr hr
    exact (log_le_log_iff (by positivity) (by positivity)).mpr (by linarith)
  have hdistL (j : ℕ) (hj : j ≤ q) :
      |(j : ℝ) - ν| = ((q - j : ℕ) : ℝ) + 1 / 2 := by
    have hjν : (j : ℝ) ≤ ν := by
      have : (j : ℝ) ≤ q := by exact_mod_cast hj
      unfold ν; linarith
    rw [abs_of_nonpos (sub_nonpos.mpr hjν), Nat.cast_sub hj]
    unfold ν; ring
  have hleft : ∑ j ∈ range (q + 1), (1 : ℝ) / |(j : ℝ) - ν| =
      ∑ j ∈ range (q + 1), (1 : ℝ) / ((j : ℝ) + 1 / 2) := by
    have hrew : ∑ j ∈ range (q + 1), (1 : ℝ) / |(j : ℝ) - ν| =
        ∑ j ∈ range (q + 1), (1 : ℝ) / (((q - j : ℕ) : ℝ) + 1 / 2) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      exact congrArg (fun t => (1 : ℝ) / t)
        (hdistL j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
    rw [hrew, ← Finset.sum_range_reflect (fun j => (1 : ℝ) / ((j : ℝ) + 1 / 2)) (q + 1)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hidx : q + 1 - 1 - j = q - j := by have := Finset.mem_range.mp hj; omega
    rw [hidx]
  have hright : ∑ k ∈ range (n - q), (1 : ℝ) / |((q + 1 + k : ℕ) : ℝ) - ν| =
      ∑ k ∈ range (n - q), (1 : ℝ) / ((k : ℝ) + 1 / 2) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hpos : ν ≤ ((q + 1 + k : ℕ) : ℝ) := by push_cast; unfold ν; linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hpos)]
    unfold ν; push_cast; ring
  have hrange : ∑ i, (1 : ℝ) / d i =
      ∑ j ∈ range (n + 1), (1 : ℝ) / |(j : ℝ) - ν| := by
    simpa [d] using Fin.sum_univ_eq_sum_range (fun j => (1 : ℝ) / |(j : ℝ) - ν|) (n + 1)
  have hsplit := Finset.sum_range_add (fun j => (1 : ℝ) / |(j : ℝ) - ν|) (q + 1) (n - q)
  have hcount : q + 1 + (n - q) = n + 1 := by omega
  have hrecip : 2 * log ((n : ℝ) + 1) ≤ ∑ i, (1 : ℝ) / d i := by
    rw [hrange]
    rw [hcount] at hsplit
    rw [hsplit, hleft, hright]
    have hsub : ∑ k ∈ range (q + 1), (1 : ℝ) / ((k : ℝ) + 1 / 2) ≤
        ∑ k ∈ range (n - q), (1 : ℝ) / ((k : ℝ) + 1 / 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hqle)
        fun _ _ _ => div_nonneg (by norm_num) (by positivity)
    have htwice : 2 * ∑ k ∈ range (q + 1), (1 : ℝ) / ((k : ℝ) + 1 / 2) ≤
        (∑ j ∈ range (q + 1), (1 : ℝ) / ((j : ℝ) + 1 / 2)) +
          ∑ k ∈ range (n - q), (1 : ℝ) / ((k : ℝ) + 1 / 2) := by
      have h := add_le_add_left hsub (∑ k ∈ range (q + 1), (1 : ℝ) / ((k : ℝ) + 1 / 2))
      simpa [two_mul, add_comm] using h
    exact (mul_le_mul_of_nonneg_left hlogCmp (by norm_num)).trans
      ((mul_le_mul_of_nonneg_left (sum_half_ge_log q) (by norm_num)).trans htwice)
  have hdef : ∑ i, (1 : ℝ) / (wt i * d i) ≥ ∑ i, (1 : ℝ) / d i - 2 := by
    have hdrop (i : Fin (n + 1)) : (1 : ℝ) / d i - 1 / (wt i * d i) ≤
        if i.val = 0 ∨ i.val = n then 1 else 0 := by
      have hdpos : 0 < d i := by
        unfold d
        rw [abs_pos]
        intro hz
        have hiν : (i.val : ℝ) = ν := sub_eq_zero.mp hz
        exact hnode i (by
          unfold nodeAngle
          rw [hiν, show θ = π * ν / n by unfold θ; ring])
      by_cases hend : i.val = 0 ∨ i.val = n
      · have hwt2 : wt i = 2 := by
          unfold wt chebyshevExtremalWeight
          exact ite_eq_left hend
        have hdhalf : 1 / 2 ≤ d i := by
          unfold d
          rcases hend with h0 | hnI
          · rw [h0, Nat.cast_zero, abs_of_nonpos (sub_nonpos.mpr hνpos.le)]
            unfold ν
            have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
            linarith
          · rw [hnI]
            have hhalf : (n : ℝ) / 2 ≤ n :=
              div_le_self hn0.le (by norm_num : (1 : ℝ) ≤ 2)
            rw [abs_of_nonneg (sub_nonneg.mpr (hνle.trans hhalf)), le_sub_iff_add_le]
            have hνeq : ν = (q : ℝ) + 1 / 2 := rfl
            rw [hνeq, show (1 : ℝ) / 2 + ((q : ℝ) + 1 / 2) = (q : ℝ) + 1 by ring]
            exact_mod_cast (show q + 1 ≤ n by omega)
        rw [hwt2, ite_eq_left hend]
        have : (1 : ℝ) / d i - 1 / (2 * d i) = 1 / (2 * d i) := by field_simp; ring
        rw [this]
        have hden : 0 < 2 * d i := by positivity
        rw [div_le_one hden]
        linarith
      · have hwt1 : wt i = 1 := chebyshevExtremalWeight_of_interior
          (by simpa using (not_or.mp hend).1) (by simpa using (not_or.mp hend).2)
        rw [hwt1, ite_eq_right (by simpa using hend)]
        have : (1 : ℝ) / d i - 1 / (1 * d i) = 0 := by field_simp; ring
        linarith
    have hind : ∑ i : Fin (n + 1), (if i.val = 0 ∨ i.val = n then (1 : ℝ) else 0) = 2 := by
      let i0 : Fin (n + 1) := ⟨0, by omega⟩
      let iN : Fin (n + 1) := ⟨n, by omega⟩
      have hpair : univ.filter (fun i : Fin (n + 1) => i.val = 0 ∨ i.val = n) = {i0, iN} := by
        ext i
        simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, i0, iN]
        constructor
        · rintro (h | h) <;> [left; right] <;> exact Fin.ext h
        · rintro (h | h) <;> simp [h]
      have hne : i0 ≠ iN := by intro h; have := congrArg Fin.val h; simp [i0, iN] at this; omega
      have hfilter := (Finset.sum_filter (s := univ)
        (fun i : Fin (n + 1) => i.val = 0 ∨ i.val = n) (fun _ => (1 : ℝ))).symm
      rw [hfilter, hpair, Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
      norm_num
    have hsum := Finset.sum_le_sum (s := univ) (fun i _ => hdrop i)
    have hsub := Finset.sum_sub_distrib (s := univ) (fun i => (1 : ℝ) / d i)
      (fun i => (1 : ℝ) / (wt i * d i))
    linarith
  have herr : ∑ i, π * d i / (8 * (n : ℝ) ^ 2 * wt i) ≤ π / 4 := by
    have hterm (i : Fin (n + 1)) : π * d i / (8 * (n : ℝ) ^ 2 * wt i) ≤ π / (8 * n) := by
      have hdpos : 0 < d i := by
        unfold d
        rw [abs_pos]
        intro hz
        have hiν : (i.val : ℝ) = ν := sub_eq_zero.mp hz
        exact hnode i (by
          unfold nodeAngle
          rw [hiν, show θ = π * ν / n by unfold θ; ring])
      have hdlt : d i < n := by
        unfold d
        rcases le_total (i.val : ℝ) ν with hle | hge
        · rw [abs_of_nonpos (sub_nonpos.mpr hle)]
          nlinarith [hνle, hn0]
        · rw [abs_of_nonneg (sub_nonneg.mpr hge)]
          have hi : (i.val : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ i.isLt
          have hνge : (1 : ℝ) / 2 ≤ ν := by
            have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
            unfold ν; linarith
          linarith
      have hα : 1 ≤ wt i := one_le_chebyshevExtremalWeight n i
      calc π * d i / (8 * (n : ℝ) ^ 2 * wt i)
          ≤ π * n / (8 * (n : ℝ) ^ 2 * wt i) := by gcongr
        _ ≤ π * n / (8 * (n : ℝ) ^ 2 * 1) :=
            div_le_div_of_nonneg_left (by positivity : 0 ≤ π * (n : ℝ)) (by positivity)
              (by gcongr)
        _ = π / (8 * n) := by field_simp
    have hsum := Finset.sum_le_sum (s := univ) fun i _ => hterm i
    have hconst : ∑ i : Fin (n + 1), π / (8 * n) = (n + 1 : ℝ) * (π / (8 * n)) := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsmall : (n + 1 : ℝ) * (π / (8 * n)) ≤ π / 4 := by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hratio : (n + 1 : ℝ) / n ≤ 2 := by rw [div_le_iff₀ hn0]; linarith
      calc (n + 1 : ℝ) * (π / (8 * n)) = π / 8 * ((n + 1 : ℝ) / n) := by ring
        _ ≤ π / 8 * 2 := by gcongr
        _ = π / 4 := by ring
    linarith
  have hmain : (2 / π) * log ((n : ℝ) + 1) - (2 / π + π / 4) ≤
      ∑ i, chebyshevLebesgueMain n θ i := by
    have hterm (i : Fin (n + 1)) : (1 : ℝ) / (wt i * π * d i) -
        π * d i / (8 * (n : ℝ) ^ 2 * wt i) ≤ chebyshevLebesgueMain n θ i := by
      have hdpos : 0 < d i := by
        unfold d
        rw [abs_pos]
        intro hz
        have hiν : (i.val : ℝ) = ν := sub_eq_zero.mp hz
        exact hnode i (by
          unfold nodeAngle
          rw [hiν, show θ = π * ν / n by unfold θ; ring])
      have hαpos : 0 < wt i := chebyshevExtremalWeight_pos n i
      let u : ℝ := |θ - nodeAngle n i| / 2
      have hu_eq : u = π * d i / (2 * n) := by
        have hθv : θ = π * ν / n := by unfold θ; ring
        have hsub : π * ν / n - π * (i.val : ℝ) / n = π * (ν - (i.val : ℝ)) / n := by
          field_simp
        unfold u d
        rw [hθv, nodeAngle, hsub, abs_div, abs_mul, abs_of_pos pi_pos, abs_of_pos hn0,
          abs_sub_comm]
        ring
      have hu : u ∈ Set.Ioo 0 (π / 2) := by
        rw [hu_eq]
        refine ⟨by positivity, ?_⟩
        have hdlt : d i < n := by
          unfold d
          rcases le_total (i.val : ℝ) ν with hle | hge
          · rw [abs_of_nonpos (sub_nonpos.mpr hle)]; nlinarith [hνle, hn0]
          · rw [abs_of_nonneg (sub_nonneg.mpr hge)]
            have hi : (i.val : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ i.isLt
            have hνge : (1 : ℝ) / 2 ≤ ν := by
              have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
              unfold ν; linarith
            linarith
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hdlt, pi_pos]
      have hcot := cot_ge_inv_sub hu
      have hcoef : 0 ≤ 1 / (2 * (n : ℝ) * wt i) := by positivity
      have hineq := mul_le_mul_of_nonneg_left hcot hcoef
      have hmaineq : chebyshevLebesgueMain n θ i =
          1 / (2 * (n : ℝ) * wt i) * cot u := by
        unfold chebyshevLebesgueMain wt
        rw [hsin]
      have halg : 1 / (2 * (n : ℝ) * wt i) * (1 / u - u / 2) =
          1 / (wt i * π * d i) - π * d i / (8 * (n : ℝ) ^ 2 * wt i) := by
        rw [hu_eq]
        field_simp [hdpos.ne', hαpos.ne', hn0.ne', pi_ne_zero]
        ring
      linarith
    have hsum := Finset.sum_le_sum (s := univ) fun i _ => hterm i
    have hrew : ∑ i, ((1 : ℝ) / (wt i * π * d i) -
          π * d i / (8 * (n : ℝ) ^ 2 * wt i)) =
        (1 / π) * ∑ i, (1 : ℝ) / (wt i * d i) -
          ∑ i, π * d i / (8 * (n : ℝ) ^ 2 * wt i) := by
      rw [Finset.sum_sub_distrib]
      congr 1
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by
          have hdne : d i ≠ 0 := by
            unfold d
            rw [ne_eq, abs_eq_zero]
            intro hz
            have hiν : (i.val : ℝ) = ν := sub_eq_zero.mp hz
            exact hnode i (by
              unfold nodeAngle
              rw [hiν, show θ = π * ν / n by unfold θ; ring])
          have hαne := (chebyshevExtremalWeight_pos n i).ne'
          field_simp [hdne, hαne, pi_ne_zero]
    have hcoef : (1 / π) * (2 : ℝ) = 2 / π := by rw [div_mul_eq_mul_div, one_mul]
    have hbase : (2 : ℝ) * log ((n : ℝ) + 1) - 2 ≤ ∑ i, (1 : ℝ) / (wt i * d i) :=
      (sub_le_sub_right hrecip 2).trans hdef
    have hscale : (1 / π) * ((2 : ℝ) * log ((n : ℝ) + 1) - 2) ≤
        (1 / π) * ∑ i, (1 : ℝ) / (wt i * d i) :=
      mul_le_mul_of_nonneg_left hbase (div_nonneg (by norm_num) pi_pos.le)
    have hdropB : (1 / π) * ((2 : ℝ) * log ((n : ℝ) + 1) - 2) -
        ∑ i, π * d i / (8 * (n : ℝ) ^ 2 * wt i) ≤
        (1 / π) * ∑ i, (1 : ℝ) / (wt i * d i) -
          ∑ i, π * d i / (8 * (n : ℝ) ^ 2 * wt i) :=
      sub_le_sub_right hscale _
    have hfloor : (1 / π) * ((2 : ℝ) * log ((n : ℝ) + 1) - 2) - π / 4 ≤
        (1 / π) * ((2 : ℝ) * log ((n : ℝ) + 1) - 2) -
          ∑ i, π * d i / (8 * (n : ℝ) ^ 2 * wt i) :=
      sub_le_sub_left herr _
    have hident : (1 / π) * ((2 : ℝ) * log ((n : ℝ) + 1) - 2) - π / 4 =
        (2 / π) * log ((n : ℝ) + 1) - (2 / π + π / 4) := by
      rw [mul_sub, ← mul_assoc, hcoef, sub_sub]
    have hrewSum : (1 / π) * ∑ i, (1 : ℝ) / (wt i * d i) -
        ∑ i, π * d i / (8 * (n : ℝ) ^ 2 * wt i) ≤
        ∑ i, chebyshevLebesgueMain n θ i := by
      rw [← hrew]
      exact hsum
    rw [← hident]
    exact hfloor.trans (hdropB.trans hrewSum)
  have hcorr : -(1 / 2) ≤ ∑ i, chebyshevLebesgueCorr n θ i := by
    let p : Fin (n + 1) → Prop := fun i => i.val ≤ q ∨ n - q ≤ i.val
    have hadd := Finset.sum_filter_add_sum_filter_not univ p
      (fun i => chebyshevLebesgueCorr n θ i)
    have hside (i : Fin (n + 1)) (hp : p i) : 0 ≤ chebyshevLebesgueCorr n θ i := by
      have hpref : 0 ≤ |sin ((n : ℝ) * θ)| /
          (2 * (n : ℝ) * chebyshevExtremalWeight n i) :=
        div_nonneg (abs_nonneg _)
          (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hn0)
            (chebyshevExtremalWeight_pos n i)).le
      rcases hp with hleftI | hrightI
      · have hφ : nodeAngle n i < θ := by
          have hiν : (i.val : ℝ) < ν := by
            have : (i.val : ℝ) ≤ q := by exact_mod_cast hleftI
            unfold ν; linarith
          unfold nodeAngle
          rw [show θ = π * ν / n by unfold θ; ring, div_lt_div_iff₀ hn0 hn0]
          have hmul := mul_lt_mul_of_pos_left hiν pi_pos
          nlinarith [hmul, hn0]
        have hsign := chebyshevAngleSign_of_lt hφ
        have havg : (θ + nodeAngle n i) / 2 < π / 2 := by
          have hsum : θ + nodeAngle n i < θ + θ := by linarith
          linarith [hθmem.2]
        have havg0 : 0 < (θ + nodeAngle n i) / 2 := by
          linarith [hθmem.1, (nodeAngle_mem_Icc (by omega) i).1]
        have hcot : 0 < cot ((θ + nodeAngle n i) / 2) := by
          rw [cot_eq_cos_div_sin]
          exact div_pos
            (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], havg⟩)
            (sin_pos_of_pos_of_lt_pi havg0 (havg.trans (by linarith [pi_pos])))
        unfold chebyshevLebesgueCorr
        rw [hsign, mul_one]
        exact mul_nonneg hpref hcot.le
      · have hφ : π - θ < nodeAngle n i := by
          have hiν : (n : ℝ) - ν < (i.val : ℝ) := by
            have hi : ((n - q : ℕ) : ℝ) ≤ i.val := by exact_mod_cast hrightI
            have hcast : ((n - q : ℕ) : ℝ) = (n : ℝ) - q := Nat.cast_sub (by omega)
            have hν : (n : ℝ) - ν = (n : ℝ) - q - 1 / 2 := by unfold ν; ring
            linarith
          unfold nodeAngle
          rw [lt_div_iff₀ hn0]
          have hright : (π - θ) * n = π * ((n : ℝ) - ν) := by
            unfold θ; field_simp
          have hmul := mul_lt_mul_of_pos_left hiν pi_pos
          rw [hright]
          exact hmul
        have hθle : θ ≤ π - θ := by
          rw [le_sub_iff_add_le, ← two_mul]
          calc
            2 * θ ≤ 2 * (π / 2) := mul_le_mul_of_nonneg_left hθmem.2 (by norm_num)
            _ = π := by ring
        have hsign := chebyshevAngleSign_of_not_lt (not_lt_of_gt (hθle.trans_lt hφ))
        have havg : π / 2 < (θ + nodeAngle n i) / 2 := by linarith
        have havgπ : (θ + nodeAngle n i) / 2 < π := by
          have hφπ : nodeAngle n i ≤ π := (nodeAngle_mem_Icc (by omega) i).2
          linarith [hθmem.2]
        have hcot : cot ((θ + nodeAngle n i) / 2) < 0 := by
          rw [cot_eq_cos_div_sin]
          have hsin : 0 < sin ((θ + nodeAngle n i) / 2) :=
            sin_pos_of_pos_of_lt_pi (by linarith) havgπ
          have hcos : cos ((θ + nodeAngle n i) / 2) < 0 :=
            cos_neg_of_pi_div_two_lt_of_lt havg
              (havgπ.trans (lt_add_of_pos_right π (div_pos pi_pos (by norm_num))))
          exact div_neg_of_neg_of_pos hcos hsin
        unfold chebyshevLebesgueCorr
        rw [hsign]
        have hnonnegCot : 0 ≤ -cot ((θ + nodeAngle n i) / 2) := neg_nonneg.mpr hcot.le
        have hrew : |sin ((n : ℝ) * θ)| / (2 * (n : ℝ) * chebyshevExtremalWeight n i) *
            -1 * cot ((θ + nodeAngle n i) / 2) =
            |sin ((n : ℝ) * θ)| / (2 * (n : ℝ) * chebyshevExtremalWeight n i) *
              (-cot ((θ + nodeAngle n i) / 2)) := by ring
        rw [hrew]
        exact mul_nonneg hpref hnonnegCot
    have hgood : 0 ≤ ∑ i ∈ univ.filter p, chebyshevLebesgueCorr n θ i :=
      Finset.sum_nonneg fun i hi => hside i (mem_filter.mp hi).2
    have hbad : -(1 / 2) ≤ ∑ i ∈ univ.filter (fun i => ¬ p i), chebyshevLebesgueCorr n θ i := by
      by_cases hr0 : (n - 1) % 2 = 0
      · have hempty : univ.filter (fun i : Fin (n + 1) => ¬ p i) = ∅ := by
          ext i
          simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty]
          constructor
          · intro h
            have hgap : n - q = q + 1 := by omega
            simp only [p, not_or, not_le] at h
            omega
          · intro h
            exact h.elim
        rw [hempty, Finset.sum_empty]
        exact neg_nonpos.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2)
      · have hr1 : (n - 1) % 2 = 1 := by
          have hlt := Nat.mod_lt (n - 1) (by decide : 0 < 2)
          omega
        have honly : univ.filter (fun i : Fin (n + 1) => ¬ p i) = {⟨q + 1, by omega⟩} := by
          ext i
          simp only [mem_filter, mem_univ, true_and, mem_singleton]
          constructor
          · intro hnp
            have hlt : q < i.val := by
              have : ¬ i.val ≤ q := by intro h; exact hnp (Or.inl h)
              omega
            have hgt : i.val < n - q := by
              have : ¬ n - q ≤ i.val := by intro h; exact hnp (Or.inr h)
              omega
            have hgap : n - q = q + 2 := by omega
            have : i.val = q + 1 := by omega
            exact Fin.ext this
          · intro hi
            rw [hi]
            intro hp
            have hgap : n - q = q + 2 := by omega
            simp only [p] at hp
            omega
        rw [honly, Finset.sum_singleton]
        let j : Fin (n + 1) := ⟨q + 1, by omega⟩
        have hnEven : n = 2 * (q + 1) := by omega
        have hφ : nodeAngle n j = π / 2 := by
          unfold nodeAngle
          have hcast : ((q + 1 : ℕ) : ℝ) = (n : ℝ) / 2 := by
            have hnR : (n : ℝ) = 2 * ((q + 1 : ℕ) : ℝ) := by exact_mod_cast hnEven
            rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
            linarith
          rw [hcast]; field_simp
        have hθeq : θ = π / 2 - π / (2 * n) := by
          unfold θ ν
          have hνeq : (q : ℝ) + 1 / 2 = (n : ℝ) / 2 - 1 / 2 := by
            have : (n : ℝ) = 2 * ((q : ℝ) + 1) := by exact_mod_cast hnEven
            linarith
          rw [hνeq]; field_simp
        have havg : (θ + nodeAngle n j) / 2 = π / 2 - π / (4 * n) := by
          rw [hφ, hθeq]; ring
        have hcot : cot ((θ + nodeAngle n j) / 2) = tan (π / (4 * n)) := by
          rw [havg, cot_eq_cos_div_sin, cos_pi_div_two_sub, sin_pi_div_two_sub,
            tan_eq_sin_div_cos]
        have hw : chebyshevExtremalWeight n j = 1 :=
          chebyshevExtremalWeight_of_interior (by simp [j]) (by simp [j]; omega)
        have hsign : chebyshevAngleSign n θ j = -1 :=
          chebyshevAngleSign_of_not_lt (by
            rw [hφ, hθeq]
            exact not_lt_of_gt (sub_lt_self (π / 2)
              (div_pos pi_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hn0))))
        have htan : tan (π / (4 * n)) ≤ 1 := by
          have h4pos : (0 : ℝ) < 4 := by norm_num
          have h2pos : (0 : ℝ) < 2 := by norm_num
          have hden : 0 < 4 * (n : ℝ) := mul_pos h4pos hn0
          have h1n : (1 : ℝ) ≤ n := by exact_mod_cast hn
          have h4n : (4 : ℝ) ≤ 4 * n := by
            simpa [mul_one] using mul_le_mul_of_nonneg_left h1n h4pos.le
          have h2lt : (2 : ℝ) < 4 * n := (by norm_num : (2 : ℝ) < 4).trans_le h4n
          have hxlt : π / (4 * n) < π / 2 := by
            rw [div_lt_div_iff₀ hden h2pos]
            exact mul_lt_mul_of_pos_left h2lt pi_pos
          have hx0 : 0 ≤ π / (4 * n) := div_nonneg pi_pos.le hden.le
          have hxneg : -(π / 2) < π / (4 * n) :=
            (neg_lt_zero.mpr (div_pos pi_pos h2pos)).trans_le hx0
          have hx : π / (4 * n) ∈ Set.Ioo (-(π / 2)) (π / 2) := ⟨hxneg, hxlt⟩
          have hπ4 : π / 4 < π / 2 := by
            rw [div_lt_div_iff₀ h4pos h2pos]
            exact mul_lt_mul_of_pos_left (by norm_num : (2 : ℝ) < 4) pi_pos
          have hy : π / 4 ∈ Set.Ioo (-(π / 2)) (π / 2) :=
            ⟨(neg_lt_zero.mpr (div_pos pi_pos h2pos)).trans_le (div_nonneg pi_pos.le h4pos.le),
              hπ4⟩
          have hle : π / (4 * n) ≤ π / 4 := by
            rw [div_le_div_iff₀ hden h4pos]
            exact mul_le_mul_of_nonneg_left h4n pi_pos.le
          simpa [tan_pi_div_four] using strictMonoOn_tan.monotoneOn hx hy hle
        unfold chebyshevLebesgueCorr
        rw [hw, hsign, hcot, hsin]
        have hnonneg : 0 ≤ tan (π / (4 * n)) := by
          have hden : 0 < 4 * (n : ℝ) := mul_pos (by norm_num) hn0
          have h2le : (2 : ℝ) ≤ 4 * n := by
            have h1n : (1 : ℝ) ≤ n := by exact_mod_cast hn
            exact (by norm_num : (2 : ℝ) ≤ 4).trans
              (by simpa [mul_one] using
                mul_le_mul_of_nonneg_left h1n (by norm_num : (0 : ℝ) ≤ 4))
          exact tan_nonneg_of_nonneg_of_le_pi_div_two (div_nonneg pi_pos.le hden.le)
            (div_le_div_of_nonneg_left pi_pos.le (by norm_num : (0 : ℝ) < 2) h2le)
        have hstep : tan (π / (4 * n)) / (2 * (n : ℝ)) ≤ 1 / 2 := by
          have hden : 0 < 2 * (n : ℝ) := mul_pos (by norm_num : (0 : ℝ) < 2) hn0
          have hfrac : tan (π / (4 * n)) / (2 * (n : ℝ)) ≤ 1 / (2 * (n : ℝ)) :=
            div_le_div_of_nonneg_right htan hden.le
          have hsmall : (1 : ℝ) / (2 * n) ≤ 1 / 2 := by
            rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2), one_mul, one_mul]
            have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
            simpa [mul_one] using mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)
          exact hfrac.trans hsmall
        have hid : (1 : ℝ) / (2 * n * 1) * -1 * tan (π / (4 * n)) =
            -(tan (π / (4 * n)) / (2 * n)) := by
          rw [mul_one, mul_assoc, neg_one_mul, mul_neg, mul_comm, mul_one_div]
        rw [hid]
        exact neg_le_neg hstep
    have hsumc := add_le_add hgood hbad
    rw [hadd] at hsumc
    simpa using hsumc
  have hsum := add_le_add hmain hcorr
  have hL : (2 / π) * log ((n : ℝ) + 1) - (2 / π + π / 4 + 1 / 2) =
      (2 / π) * log ((n : ℝ) + 1) - (2 / π + π / 4) + -(1 / 2) :=
    (sub_sub ((2 / π) * log ((n : ℝ) + 1)) (2 / π + π / 4) (1 / 2)).symm.trans
      (sub_eq_add_neg _ _)
  rw [hL]
  exact hsum


end CKMA
