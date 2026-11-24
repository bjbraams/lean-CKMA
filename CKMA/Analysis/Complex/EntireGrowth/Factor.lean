/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Complex.EntireGrowth.Product
public import TauCeti.Analysis.Complex.GrowthOrder
public import TauCeti.Analysis.Complex.Liouville

public import CKMA.Analysis.Complex.EntireGrowth.Zeros
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.Analysis.Complex.BorelCaratheodory
import TauCeti.Analysis.Complex.DivisorFactorization
import TauCeti.Analysis.Convex.SimplyConnected
import TauCeti.Analysis.SpecialFunctions.Log.Base
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Field

/-!
# Hadamard factorization at finite order

An entire function of order at most `ρ`, nonzero at the origin, is a polynomial exponential times
the canonical product of genus `⌊ρ⌋` over its zeros. The argument reuses the zero enumeration and
the genus product, compares zero counts with `TauCeti.OrderLE.eventually_sum_divisor_le`, and
controls the logarithm by dyadic annuli. Polynomial growth of the remaining entire logarithm is
`Differentiable.isBigO_of_cexp_isBigO`, and the degree bound is
`Differentiable.exists_eq_polynomial_eval_of_isLittleO_pow`.
-/

public section

noncomputable section

namespace CKMA

open Asymptotics Bornology Classical Complex Filter Finset MeasureTheory Metric Set Topology
open scoped BigOperators ENNReal

variable {g : ℂ → ℂ}

/-- The listed zeros of modulus at most `R` form a finite set. -/
private theorem enumeratedBall_finite (hg : Differentiable ℂ g) (R : ℝ) :
    {n | ∃ w, enumeratedZero hg n = some w ∧ ‖w‖ ≤ R}.Finite := by
  classical
  let d := MeromorphicOn.divisor g Set.univ
  let s : Set d.support := {ρ | ‖(ρ : ℂ)‖ ≤ R}
  have hs : s.Finite := MeromorphicOn.divisor_norm_sublevel_finite g R
  let σ := Σ ρ : s, Fin ((d (ρ.1 : ℂ)).toNat)
  have hσ : Finite σ := by
    have : Finite s := hs
    infer_instance
  let e : σ ≃ {a : ZeroAtom g // ‖(a.1 : ℂ)‖ ≤ R} :=
    { toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      invFun := fun a => ⟨⟨a.1.1, a.2⟩, a.1.2⟩
      left_inv := fun x => rfl
      right_inv := fun a => rfl }
  have hatom : Finite {a : ZeroAtom g // ‖(a.1 : ℂ)‖ ≤ R} := Finite.of_equiv σ e
  have himage : {n | ∃ w, enumeratedZero hg n = some w ∧ ‖w‖ ≤ R} =
      range fun a : {a : ZeroAtom g // ‖(a.1 : ℂ)‖ ≤ R} => zeroEncode hg a.1 := by
    ext n
    constructor
    · intro hn
      obtain ⟨w, hw, hR⟩ := hn
      obtain ⟨a, haenc, ha1⟩ := exists_zeroAtom_of_enumeratedZero hg hw
      exact ⟨⟨a, by simpa [ha1] using hR⟩, haenc⟩
    · intro ⟨a, ha⟩
      refine ⟨(a.1.1 : ℂ), ?_, ?_⟩
      · rw [← ha]
        exact enumeratedZero_zeroEncode hg a.1
      · simpa [ha] using a.2
  rw [himage]
  exact finite_range _

/-- The number of listed zeros of modulus at most `R` is `O(R ^ B)` for every `B` above the order.
  -/
private theorem exists_enumerated_count_bound (hg : Differentiable ℂ g) {ρ B : ℝ}
    (hord : TauCeti.OrderLE g ρ) (hB : ρ < B) :
    ∃ C > 0, ∀ᶠ R : ℝ in atTop,
      (({n | ∃ w, enumeratedZero hg n = some w ∧ ‖w‖ ≤ R}.ncard : ℝ) ≤ C * R ^ B) := by
  classical
  obtain ⟨C, hCpos, hC⟩ := hord.eventually_sum_divisor_le hg hB
  refine ⟨C, hCpos, hC.mono ?_⟩
  intro R hR
  let d := MeromorphicOn.divisor g Set.univ
  let s : Set d.support := {ρ | ‖(ρ : ℂ)‖ ≤ R}
  have hs : s.Finite := MeromorphicOn.divisor_norm_sublevel_finite g R
  have : Fintype s := hs.fintype
  let σ := Σ ρ : s, Fin ((d (ρ.1 : ℂ)).toNat)
  let eAtom : σ ≃ {a : ZeroAtom g // ‖(a.1 : ℂ)‖ ≤ R} :=
    { toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      invFun := fun a => ⟨⟨a.1.1, a.2⟩, a.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eIdx : {a : ZeroAtom g // ‖(a.1 : ℂ)‖ ≤ R} ≃
      {n // ∃ w, enumeratedZero hg n = some w ∧ ‖w‖ ≤ R} :=
    Equiv.ofBijective
      (fun a => ⟨zeroEncode hg a.1, ⟨(a.1.1 : ℂ), enumeratedZero_zeroEncode hg a.1, a.2⟩⟩)
      ⟨fun a b hab => Subtype.ext (zeroEncode_injective hg (congrArg Subtype.val hab)),
        fun n => by
          obtain ⟨w, hw, hRn⟩ := n.2
          obtain ⟨a, haenc, ha1⟩ := exists_zeroAtom_of_enumeratedZero hg hw
          exact ⟨⟨a, by simpa [ha1] using hRn⟩, Subtype.ext haenc⟩⟩
  have hcard : ({n | ∃ w, enumeratedZero hg n = some w ∧ ‖w‖ ≤ R}.ncard) =
      ∑ ρ : s, (d (ρ.1 : ℂ)).toNat := by
    rw [ncard_ofPred, ← Nat.card_congr (eAtom.trans eIdx)]
    refine (Nat.card_sigma (β := fun ρ : s ↦ Fin ((d (ρ.1 : ℂ)).toNat))).trans ?_
    refine Finset.sum_congr rfl fun ρ _ ↦ ?_
    simp [Nat.card_fin]
  have hreal : (({n | ∃ w, enumeratedZero hg n = some w ∧ ‖w‖ ≤ R}.ncard : ℝ)) =
      ∑' ρ : s, (d (ρ.1 : ℂ) : ℝ) := by
    rw [hcard, Nat.cast_sum, tsum_fintype]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    exact divisor_toNat_cast hg (ρ.1 : ℂ)
  have hA : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  have hsub : ∀ ρ ∈ s, ‖(ρ : ℂ)‖ ≤ R := fun ρ hρ => by simpa [s] using hρ
  have htsum := hA.tsum_divisor_subtype_le_sum_closedBall (R := R) s hsub
  exact (hreal.symm ▸ htsum).trans hR

/-- Zeros of modulus at least `2R` contribute at most a constant times `R ^ (B - q)` to
`∑ ‖w‖ ^ (-q)`. -/
private theorem dyadic_tail_le {a : ℕ → Option ℂ} {B q C R0 : ℝ} (hBq : B < q) (hq : 0 ≤ q)
    (hC : 0 ≤ C) (hR0 : 1 ≤ R0)
    (hfin : ∀ R : ℝ, {n | ∃ w, a n = some w ∧ ‖w‖ ≤ R}.Finite)
    (hcount : ∀ R : ℝ, R0 ≤ R →
      (({n | ∃ w, a n = some w ∧ ‖w‖ ≤ R}.ncard : ℝ) ≤ C * R ^ B))
    {R : ℝ} (hR : R0 ≤ R) :
    ∑' n, (match a n with
      | none => (0 : ℝ)
      | some w => if 2 * R ≤ ‖w‖ then ‖w‖ ^ (-q) else 0) ≤
      C * (2 : ℝ) ^ B / (1 - (2 : ℝ) ^ (B - q)) * R ^ (B - q) := by
  classical
  let θ : ℝ := (2 : ℝ) ^ (B - q)
  have hθ0 : 0 < θ := Real.rpow_pos_of_pos (by norm_num) _
  have hθ1 : θ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hBq)
  let N : ℕ := ⌊Real.logb 2 R⌋₊ + 1
  have hRN : R < (2 : ℝ) ^ N := by
    simpa [N] using Real.lt_pow_natFloor_logb_add_one (by norm_num) (by linarith : 0 < R)
  let f : ℕ → ℝ := fun n => match a n with
    | none => 0
    | some w => if 2 * R ≤ ‖w‖ then ‖w‖ ^ (-q) else 0
  have hf0 : ∀ n, 0 ≤ f n := by
    intro n
    cases ha : a n with
    | none => simp [f, ha]
    | some w =>
      simp only [f, ha]
      split_ifs with hle
      · exact Real.rpow_nonneg (norm_nonneg _) _
      · exact le_rfl
  refine Real.tsum_le_of_sum_le hf0 ?_
  intro u
  let s := u.filter fun n => ∃ w, a n = some w ∧ 2 * R ≤ ‖w‖
  have hsumeq : ∑ n ∈ u, f n = ∑ n ∈ s, f n := by
    have hpoint : ∀ n ∈ u, f n =
        if ∃ w, a n = some w ∧ 2 * R ≤ ‖w‖ then f n else 0 := by
      intro n hn
      by_cases h : ∃ w, a n = some w ∧ 2 * R ≤ ‖w‖
      · simp [h]
      · have hf0n : f n = 0 := by
          cases ha : a n with
          | none => simp [f, ha]
          | some w =>
            have hlt : ¬2 * R ≤ ‖w‖ := fun hle => h ⟨w, ha, hle⟩
            simp [f, ha, hlt]
        simp [h, hf0n]
    rw [Finset.sum_congr rfl hpoint, Finset.sum_filter]
  rw [hsumeq]
  let wOf : ℕ → ℂ := fun n =>
    if h : ∃ w, a n = some w ∧ 2 * R ≤ ‖w‖ then Classical.choose h else 0
  let bin : ℕ → ℕ := fun n => ⌊Real.logb 2 ‖wOf n‖⌋₊
  have hwOf (n : ℕ) (hn : n ∈ s) : a n = some (wOf n) ∧ 2 * R ≤ ‖wOf n‖ := by
    have h := (Finset.mem_filter.mp hn).2
    have hw : wOf n = Classical.choose h := by simp [wOf, h]
    rw [hw]
    exact Classical.choose_spec h
  have hbin (n : ℕ) (hn : n ∈ s) :
      (2 : ℝ) ^ bin n ≤ ‖wOf n‖ ∧ ‖wOf n‖ < (2 : ℝ) ^ (bin n + 1) := by
    have h1 : (1 : ℝ) ≤ ‖wOf n‖ := by
      have h2 : (2 : ℝ) ≤ ‖wOf n‖ := by
        have h2R : 2 * R ≤ ‖wOf n‖ := (hwOf n hn).2
        have hR2 : (2 : ℝ) ≤ 2 * R := by nlinarith
        linarith
      exact one_le_two.trans h2
    exact ⟨Real.pow_natFloor_logb_le_self (by norm_num) h1,
      Real.lt_pow_natFloor_logb_add_one (by norm_num) (by linarith : 0 < ‖wOf n‖)⟩
  have hbinN (n : ℕ) (hn : n ∈ s) : N ≤ bin n := by
    have hlog : Real.logb 2 R + (1 : ℕ) ≤ Real.logb 2 ‖wOf n‖ := by
      have hmul : Real.logb 2 (2 * R) = 1 + Real.logb 2 R := by
        rw [Real.logb_mul (by norm_num) (by linarith : (R : ℝ) ≠ 0),
          Real.logb_self_eq_one (by norm_num)]
      have hle : Real.logb 2 (2 * R) ≤ Real.logb 2 ‖wOf n‖ :=
        Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by nlinarith : 0 < 2 * R)
          (hwOf n hn).2
      rw [Nat.cast_one]
      linarith [hmul, hle]
    have hfloor := Nat.floor_le_floor hlog
    rw [Nat.floor_add_natCast (Real.logb_nonneg (by norm_num) (by linarith : 1 ≤ R)) 1] at hfloor
    exact hfloor
  have hweight (n : ℕ) (hn : n ∈ s) : f n ≤ ((2 : ℝ) ^ bin n) ^ (-q) := by
    have hw := hwOf n hn
    have hf : f n = ‖wOf n‖ ^ (-q) := by simp [f, hw.1, hw.2]
    rw [hf]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (hbin n hn).1 (neg_nonpos.mpr hq)
  have hann (k : ℕ) (hk : N ≤ k) :
      ((s.filter fun n => bin n = k).card : ℝ) ≤ C * ((2 : ℝ) ^ (k + 1)) ^ B := by
    have hball : R0 ≤ (2 : ℝ) ^ (k + 1) := by
      have hlt : R0 ≤ R := hR
      have hpow : R < (2 : ℝ) ^ N := hRN
      have hk' : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ (k + 1) := by
        exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
      linarith
    have hcard : (s.filter fun n => bin n = k).card ≤
        {n | ∃ w, a n = some w ∧ ‖w‖ ≤ (2 : ℝ) ^ (k + 1)}.ncard := by
      have hset := hfin ((2 : ℝ) ^ (k + 1))
      rw [Set.ncard_eq_toFinset_card _ hset]
      refine Finset.card_le_card ?_
      intro n hn
      have hn' := Finset.mem_filter.mp hn
      have hw := hwOf n hn'.1
      have hlt : ‖wOf n‖ ≤ (2 : ℝ) ^ (k + 1) := by
        have hkbin : bin n = k := by simpa using hn'.2
        simpa [hkbin] using (hbin n hn'.1).2.le
      exact hset.mem_toFinset.mpr ⟨wOf n, hw.1, hlt⟩
    exact (Nat.cast_le.mpr hcard).trans (hcount _ hball)
  have hinner (k : ℕ) (hk : k ∈ s.image bin) :
      ∑ n ∈ s.filter fun n => bin n = k, f n ≤ C * (2 : ℝ) ^ B * θ ^ k := by
    have hNk : N ≤ k := by
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
      exact hbinN n hn
    calc
      ∑ n ∈ s.filter fun n => bin n = k, f n
          ≤ ∑ n ∈ s.filter fun n => bin n = k, ((2 : ℝ) ^ k) ^ (-q) := by
            refine Finset.sum_le_sum fun n hn => ?_
            have hn' := Finset.mem_filter.mp hn
            have hkbin : bin n = k := by simpa using hn'.2
            simpa [hkbin] using hweight n hn'.1
      _ = ((s.filter fun n => bin n = k).card : ℝ) * ((2 : ℝ) ^ k) ^ (-q) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (C * ((2 : ℝ) ^ (k + 1)) ^ B) * ((2 : ℝ) ^ k) ^ (-q) := by
            gcongr
            exact hann k hNk
      _ = C * (2 : ℝ) ^ B * θ ^ k := by
            have hscale := Real.pow_succ_rpow_mul_pow_rpow (a := (2 : ℝ)) (by norm_num) B (-q) k
            rw [mul_assoc, hscale]
            dsimp [θ]
            ring_nf
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (g := bin) (s := s) (t := s.image bin) (f := fun n => f n)
    (fun n hn => Finset.mem_image_of_mem bin hn)
  have hsumθ : ∑ k ∈ s.image bin, θ ^ k ≤ θ ^ N / (1 - θ) := by
    have hM : ∃ M, ∀ k ∈ s.image bin, k < M := by
      refine ⟨(s.image bin).sup id + 1, ?_⟩
      intro k hk
      have hk' : k ≤ (s.image bin).sup id := Finset.le_sup (f := id) hk
      omega
    obtain ⟨M, hM⟩ := hM
    have hsub : ∑ k ∈ s.image bin, θ ^ k ≤ ∑ k ∈ Finset.Ico N M, θ ^ k := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro k hk
        rw [Finset.mem_Ico]
        exact ⟨by
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
          exact hbinN n hn, hM k hk⟩
      · intro k _ _
        exact pow_nonneg hθ0.le k
    exact hsub.trans (geom_sum_Ico_le_of_lt_one hθ0.le hθ1)
  have hθN : θ ^ N ≤ R ^ (B - q) := by
    have hbase : R ≤ (2 : ℝ) ^ N := le_of_lt hRN
    have hpow : ((2 : ℝ) ^ N) ^ (B - q) ≤ R ^ (B - q) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hbase (sub_nonpos.mpr hBq.le)
    have hθ : θ ^ N = ((2 : ℝ) ^ N) ^ (B - q) := by
      dsimp [θ]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
      rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
    linarith
  have hden : 0 < 1 - θ := sub_pos.mpr hθ1
  have hcoef : 0 ≤ C * (2 : ℝ) ^ B / (1 - θ) :=
    div_nonneg (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)) hden.le
  have hbound : ∑ n ∈ s, f n ≤ C * (2 : ℝ) ^ B / (1 - θ) * R ^ (B - q) := by
    have hsum1 : ∑ n ∈ s, f n ≤ ∑ k ∈ s.image bin, C * (2 : ℝ) ^ B * θ ^ k := by
      rw [hfiber.symm]
      exact Finset.sum_le_sum fun k hk => hinner k hk
    have hsum2 : ∑ k ∈ s.image bin, C * (2 : ℝ) ^ B * θ ^ k =
        C * (2 : ℝ) ^ B * ∑ k ∈ s.image bin, θ ^ k := by
      rw [Finset.mul_sum]
    have hsum3 : C * (2 : ℝ) ^ B * ∑ k ∈ s.image bin, θ ^ k ≤
        C * (2 : ℝ) ^ B * (θ ^ N / (1 - θ)) :=
      mul_le_mul_of_nonneg_left hsumθ (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _))
    have hmul : C * (2 : ℝ) ^ B * (θ ^ N / (1 - θ)) =
        (C * (2 : ℝ) ^ B / (1 - θ)) * θ ^ N := by
      rw [mul_div_assoc']
      exact (div_mul_eq_mul_div (C * (2 : ℝ) ^ B) (1 - θ) (θ ^ N)).symm
    have hsum4 : C * (2 : ℝ) ^ B * (θ ^ N / (1 - θ)) ≤
        C * (2 : ℝ) ^ B / (1 - θ) * R ^ (B - q) := by
      rw [hmul]
      exact mul_le_mul_of_nonneg_left hθN hcoef
    exact hsum1.trans ((le_of_eq hsum2).trans (hsum3.trans hsum4))
  simpa [θ] using hbound

/-- An eventual zero-count bound holds at every radius past a fixed threshold. -/
private theorem exists_uniform_enumerated_count (hg : Differentiable ℂ g)
    {ρ B R0 : ℝ} (hord : TauCeti.OrderLE g ρ) (hρB : ρ < B) (hB : 0 ≤ B) (hR0 : 1 ≤ R0) :
    ∃ C > 0, ∀ R : ℝ, R0 ≤ R →
      (({n | ∃ w, enumeratedZero hg n = some w ∧ ‖w‖ ≤ R}.ncard : ℝ) ≤ C * R ^ B) := by
  obtain ⟨C, hCpos, hEv⟩ := exists_enumerated_count_bound hg hord hρB
  obtain ⟨R1, hR1⟩ := eventually_atTop.mp hEv
  let S := max R1 R0
  have hS1 : R1 ≤ S := le_max_left _ _
  have hSR0 : R0 ≤ S := le_max_right _ _
  have hR0pos : (0 : ℝ) < R0 := by linarith
  have hone : (1 : ℝ) ≤ S / R0 := by rw [one_le_div hR0pos]; exact hSR0
  refine ⟨C * (S / R0) ^ B, by positivity, ?_⟩
  intro R hR
  let T := max R R1
  have hTR1 : R1 ≤ T := le_max_right _ _
  have hsubset : {n | ∃ w, enumeratedZero hg n = some w ∧ ‖w‖ ≤ R} ⊆
      {n | ∃ w, enumeratedZero hg n = some w ∧ ‖w‖ ≤ T} := by
    intro n ⟨w, hw, hle⟩
    exact ⟨w, hw, hle.trans (le_max_left _ _)⟩
  have hcard : (({n | ∃ w, enumeratedZero hg n = some w ∧ ‖w‖ ≤ R}.ncard : ℝ)) ≤
      C * T ^ B :=
    (Nat.cast_le.mpr (Set.ncard_le_ncard hsubset (enumeratedBall_finite hg T))).trans
      (hR1 T hTR1)
  have hRle : R ≤ R * (S / R0) := le_mul_of_one_le_right (by linarith) hone
  have hSle : S ≤ R * (S / R0) := by
    have hcancel : R0 * (S / R0) = S := by rw [mul_div_cancel₀ _ hR0pos.ne']
    calc
      S = R0 * (S / R0) := hcancel.symm
      _ ≤ R * (S / R0) := mul_le_mul_of_nonneg_right hR
        (div_nonneg (hR0pos.le.trans hSR0) hR0pos.le)
  have hTle : T ≤ R * (S / R0) := max_le hRle ((le_max_left R1 R0).trans hSle)
  have hT0 : (0 : ℝ) ≤ T := (hR0pos.le.trans hR).trans (le_max_left _ _)
  have hpow : T ^ B ≤ (R * (S / R0)) ^ B := Real.rpow_le_rpow hT0 hTle hB
  have hsplit : (R * (S / R0)) ^ B = R ^ B * (S / R0) ^ B :=
    Real.mul_rpow (by linarith) (div_nonneg (hR0pos.le.trans hSR0) hR0pos.le)
  have hfinal : C * T ^ B ≤ C * (S / R0) ^ B * R ^ B := by
    have hpow' : T ^ B ≤ R ^ B * (S / R0) ^ B := by rwa [hsplit] at hpow
    calc
      C * T ^ B ≤ C * (R ^ B * (S / R0) ^ B) :=
        mul_le_mul_of_nonneg_left hpow' hCpos.le
      _ = C * (S / R0) ^ B * R ^ B := by ring
  exact hcard.trans hfinal

/-- The power sum of moduli in `R0 ≤ ‖w‖ < 2R`, estimated by dyadic annuli. -/
private theorem dyadic_head_le {a : ℕ → Option ℂ} {B α C R0 : ℝ}
    (hα : 0 ≤ α) (hαB : α < B) (hC : 0 ≤ C) (hR0 : 1 ≤ R0)
    (hfin : ∀ R : ℝ, {n | ∃ w, a n = some w ∧ ‖w‖ ≤ R}.Finite)
    (hcount : ∀ R : ℝ, R0 ≤ R →
      (({n | ∃ w, a n = some w ∧ ‖w‖ ≤ R}.ncard : ℝ) ≤ C * R ^ B))
    {R : ℝ} (hR : R0 ≤ R) (u : Finset ℕ)
    (hu : ∀ n ∈ u, ∃ w, a n = some w ∧ R0 ≤ ‖w‖ ∧ ‖w‖ < 2 * R) :
    ∑ n ∈ u, (match a n with
      | none => (0 : ℝ)
      | some w => ‖w‖ ^ (-α)) ≤
      C * (2 : ℝ) ^ B * (4 : ℝ) ^ (B - α) / ((2 : ℝ) ^ (B - α) - 1) * R ^ (B - α) := by
  classical
  let θ : ℝ := (2 : ℝ) ^ (B - α)
  have hθ1 : 1 < θ := Real.one_lt_rpow (by norm_num) (sub_pos.mpr hαB)
  have hθ0 : 0 < θ := zero_lt_one.trans hθ1
  let M : ℕ := ⌊Real.logb 2 R⌋₊ + 1
  let f : ℕ → ℝ := fun n => match a n with
    | none => 0
    | some w => ‖w‖ ^ (-α)
  let wOf : ℕ → ℂ := fun n => if h : ∃ w, a n = some w ∧ R0 ≤ ‖w‖ ∧ ‖w‖ < 2 * R then
      Classical.choose h else 0
  let bin : ℕ → ℕ := fun n => ⌊Real.logb 2 ‖wOf n‖⌋₊
  have hwOf (n : ℕ) (hn : n ∈ u) :
      a n = some (wOf n) ∧ R0 ≤ ‖wOf n‖ ∧ ‖wOf n‖ < 2 * R := by
    have h := hu n hn
    have hw : wOf n = Classical.choose h := by simp [wOf, h]
    rw [hw]
    exact Classical.choose_spec h
  have hf (n : ℕ) (hn : n ∈ u) : f n = ‖wOf n‖ ^ (-α) := by simp [f, (hwOf n hn).1]
  have hbin (n : ℕ) (hn : n ∈ u) :
      (2 : ℝ) ^ bin n ≤ ‖wOf n‖ ∧ ‖wOf n‖ < (2 : ℝ) ^ (bin n + 1) := by
    have h1 : (1 : ℝ) ≤ ‖wOf n‖ := hR0.trans (hwOf n hn).2.1
    exact ⟨Real.pow_natFloor_logb_le_self (by norm_num) h1,
      Real.lt_pow_natFloor_logb_add_one (by norm_num) (by linarith : 0 < ‖wOf n‖)⟩
  have hbinM (n : ℕ) (hn : n ∈ u) : bin n ≤ M := by
    have hx : Real.logb 2 ‖wOf n‖ < Real.logb 2 R + 1 := by
      have hmul : Real.logb 2 (2 * R) = 1 + Real.logb 2 R := by
        rw [Real.logb_mul (by norm_num) (by linarith : (R : ℝ) ≠ 0),
          Real.logb_self_eq_one (by norm_num)]
      have hwpos : 0 < ‖wOf n‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
        (hR0.trans (hwOf n hn).2.1)
      have hlt := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) hwpos (hwOf n hn).2.2
      linarith [hmul]
    have hy : Real.logb 2 R < (⌊Real.logb 2 R⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hx' : Real.logb 2 ‖wOf n‖ < (⌊Real.logb 2 R⌋₊ : ℝ) + 2 := by linarith
    have hxcast : Real.logb 2 ‖wOf n‖ < ↑(⌊Real.logb 2 R⌋₊ + 2) := by
      rw [Nat.cast_add]
      simpa using hx'
    have hfloor : bin n < ⌊Real.logb 2 R⌋₊ + 2 :=
      (Nat.floor_lt (Real.logb_nonneg (by norm_num) (hR0.trans (hwOf n hn).2.1))).mpr hxcast
    omega
  have hweight (n : ℕ) (hn : n ∈ u) : f n ≤ ((2 : ℝ) ^ bin n) ^ (-α) := by
    rw [hf n hn]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (hbin n hn).1 (neg_nonpos.mpr hα)
  have hann (k : ℕ) : ((u.filter fun n => bin n = k).card : ℝ) ≤
      C * ((2 : ℝ) ^ (k + 1)) ^ B := by
    by_cases hball : R0 ≤ (2 : ℝ) ^ (k + 1)
    · have hcard : (u.filter fun n => bin n = k).card ≤
          {n | ∃ w, a n = some w ∧ ‖w‖ ≤ (2 : ℝ) ^ (k + 1)}.ncard := by
        have hset := hfin ((2 : ℝ) ^ (k + 1))
        rw [Set.ncard_eq_toFinset_card _ hset]
        refine Finset.card_le_card ?_
        intro n hn
        have hn' := Finset.mem_filter.mp hn
        have hw := hwOf n hn'.1
        have hkbin : bin n = k := by simpa using hn'.2
        have hlt : ‖wOf n‖ ≤ (2 : ℝ) ^ (k + 1) := by simpa [hkbin] using (hbin n hn'.1).2.le
        exact hset.mem_toFinset.mpr ⟨wOf n, hw.1, hlt⟩
      exact (Nat.cast_le.mpr hcard).trans (hcount _ hball)
    · have hempty : u.filter (fun n => bin n = k) = ∅ := by
        ext n
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro hn hkbin
        have hlt : ‖wOf n‖ < (2 : ℝ) ^ (k + 1) := by simpa [hkbin] using (hbin n hn).2
        have hge : R0 ≤ ‖wOf n‖ := (hwOf n hn).2.1
        have hpow : (2 : ℝ) ^ (k + 1) < R0 := lt_of_not_ge hball
        linarith
      rw [hempty]
      simp only [Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
  have hinner (k : ℕ) (hk : k ∈ u.image bin) :
      ∑ n ∈ u.filter fun n => bin n = k, f n ≤ C * (2 : ℝ) ^ B * θ ^ k := by
    calc
      ∑ n ∈ u.filter fun n => bin n = k, f n
          ≤ ∑ n ∈ u.filter fun n => bin n = k, ((2 : ℝ) ^ k) ^ (-α) := by
            refine Finset.sum_le_sum fun n hn => ?_
            have hn' := Finset.mem_filter.mp hn
            have hkbin : bin n = k := by simpa using hn'.2
            simpa [hkbin] using hweight n hn'.1
      _ = ((u.filter fun n => bin n = k).card : ℝ) * ((2 : ℝ) ^ k) ^ (-α) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (C * ((2 : ℝ) ^ (k + 1)) ^ B) * ((2 : ℝ) ^ k) ^ (-α) := by
            exact mul_le_mul_of_nonneg_right (hann k)
              (Real.rpow_nonneg (pow_nonneg (by norm_num) _) _)
      _ = C * (2 : ℝ) ^ B * θ ^ k := by
            have hscale :=
              Real.pow_succ_rpow_mul_pow_rpow (a := (2 : ℝ)) (by norm_num) B (-α) k
            rw [mul_assoc, hscale]
            dsimp [θ]
            ring_nf
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (g := bin) (s := u) (t := u.image bin) (f := fun n => f n)
    (fun n hn => Finset.mem_image_of_mem bin hn)
  have hsumθ : ∑ k ∈ u.image bin, θ ^ k ≤ θ ^ (M + 1) / (θ - 1) := by
    have hsub : ∑ k ∈ u.image bin, θ ^ k ≤ ∑ k ∈ Finset.range (M + 1), θ ^ k := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro k hk
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (by
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
          exact hbinM n hn)
      · intro _ _ _
        exact pow_nonneg hθ0.le _
    have hgeom : ∑ k ∈ Finset.range (M + 1), θ ^ k = (θ ^ (M + 1) - 1) / (θ - 1) :=
      geom_sum_eq (ne_of_gt hθ1) (M + 1)
    have hle : (θ ^ (M + 1) - 1) / (θ - 1) ≤ θ ^ (M + 1) / (θ - 1) := by
      refine div_le_div_of_nonneg_right ?_ (sub_pos.mpr hθ1).le
      have hpow : 0 ≤ θ ^ (M + 1) := pow_nonneg hθ0.le _
      linarith
    exact hsub.trans (hgeom.symm ▸ hle)
  have hθM : θ ^ (M + 1) ≤ (4 * R) ^ (B - α) := by
    have hbase : (2 : ℝ) ^ (⌊Real.logb 2 R⌋₊) ≤ R :=
      Real.pow_natFloor_logb_le_self (by norm_num) (by linarith : 1 ≤ R)
    have hfour : (2 : ℝ) ^ (M + 1) ≤ 4 * R := by
      have hpow : (2 : ℝ) ^ (M + 1) = 4 * (2 : ℝ) ^ ⌊Real.logb 2 R⌋₊ := by
        dsimp [M]
        have hshift : ⌊Real.logb 2 R⌋₊ + 1 + 1 = ⌊Real.logb 2 R⌋₊ + 2 := by omega
        rw [hshift, pow_add, pow_two]
        ring
      linarith [mul_le_mul_of_nonneg_left hbase (by norm_num : (0 : ℝ) ≤ 4)]
    have hpow := Real.rpow_le_rpow (by positivity) hfour (sub_nonneg.mpr hαB.le)
    have hθeq : θ ^ (M + 1) = ((2 : ℝ) ^ (M + 1)) ^ (B - α) := by
      dsimp [θ]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
      rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
    linarith
  have hden : 0 < θ - 1 := sub_pos.mpr hθ1
  have hcoef : 0 ≤ C * (2 : ℝ) ^ B / (θ - 1) :=
    div_nonneg (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)) hden.le
  have hbound : ∑ n ∈ u, f n ≤
      C * (2 : ℝ) ^ B * (4 : ℝ) ^ (B - α) / (θ - 1) * R ^ (B - α) := by
    have hsum1 : ∑ n ∈ u, f n ≤ ∑ k ∈ u.image bin, C * (2 : ℝ) ^ B * θ ^ k := by
      rw [hfiber.symm]
      exact Finset.sum_le_sum fun k hk => hinner k hk
    have hsum2 : ∑ k ∈ u.image bin, C * (2 : ℝ) ^ B * θ ^ k =
        C * (2 : ℝ) ^ B * ∑ k ∈ u.image bin, θ ^ k := by
      rw [Finset.mul_sum]
    have hsum3 : C * (2 : ℝ) ^ B * ∑ k ∈ u.image bin, θ ^ k ≤
        C * (2 : ℝ) ^ B * (θ ^ (M + 1) / (θ - 1)) :=
      mul_le_mul_of_nonneg_left hsumθ (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _))
    have hmul : C * (2 : ℝ) ^ B * (θ ^ (M + 1) / (θ - 1)) =
        (C * (2 : ℝ) ^ B / (θ - 1)) * θ ^ (M + 1) := by
      rw [mul_div_assoc']
      exact (div_mul_eq_mul_div (C * (2 : ℝ) ^ B) (θ - 1) (θ ^ (M + 1))).symm
    have hsum4 : C * (2 : ℝ) ^ B * (θ ^ (M + 1) / (θ - 1)) ≤
        C * (2 : ℝ) ^ B / (θ - 1) * (4 * R) ^ (B - α) := by
      rw [hmul]
      exact mul_le_mul_of_nonneg_left hθM hcoef
    have hfour : (4 * R) ^ (B - α) = (4 : ℝ) ^ (B - α) * R ^ (B - α) :=
      Real.mul_rpow (by norm_num) (by linarith)
    have hsum5 : C * (2 : ℝ) ^ B / (θ - 1) * (4 * R) ^ (B - α) =
        C * (2 : ℝ) ^ B * (4 : ℝ) ^ (B - α) / (θ - 1) * R ^ (B - α) := by
      rw [hfour]
      ring
    exact hsum1.trans ((le_of_eq hsum2).trans (hsum3.trans (hsum4.trans (le_of_eq hsum5))))
  simpa [θ, f] using hbound

/-- A constant multiple of a lower power is eventually at most a higher power. -/
private theorem eventually_mul_rpow_le {a b C : ℝ} (hab : a < b) :
    ∀ᶠ R : ℝ in atTop, C * R ^ a ≤ R ^ b := by
  have hpos : 0 < b - a := sub_pos.mpr hab
  have htend := (tendsto_rpow_neg_atTop hpos).const_mul C
  have htend0 : Tendsto (fun R : ℝ => C * R ^ (-(b - a))) atTop (𝓝 0) := by
    rw [← mul_zero C]
    exact htend
  have hnhds : Iio (1 : ℝ) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds one_pos
  filter_upwards [htend0.eventually hnhds, eventually_gt_atTop (0 : ℝ)] with R hR hRpos
  have hsplit : R ^ a = R ^ (-(b - a)) * R ^ b := by
    rw [← Real.rpow_add hRpos, neg_sub, sub_add_cancel]
  have hRb : 0 ≤ R ^ b := Real.rpow_nonneg hRpos.le _
  calc
    C * R ^ a = C * R ^ (-(b - a)) * R ^ b := by rw [hsplit, mul_assoc]
    _ ≤ 1 * R ^ b := mul_le_mul_of_nonneg_right hR.le hRb
    _ = R ^ b := one_mul _

/-- A constant multiple of a lower power times a logarithm is eventually at most a higher
power. -/
private theorem eventually_log_mul_rpow_le {a b C : ℝ} (hab : a < b) :
    ∀ᶠ R : ℝ in atTop, C * R ^ a * Real.log (2 * R) ≤ R ^ b := by
  have hpos : 0 < b - a := sub_pos.mpr hab
  have hlog := (isLittleO_log_rpow_atTop hpos).tendsto_div_nhds_zero
  have hconst := (tendsto_rpow_neg_atTop hpos).const_mul (Real.log 2)
  have hconst0 : Tendsto (fun R : ℝ => Real.log 2 * R ^ (-(b - a))) atTop (𝓝 0) := by
    rw [← mul_zero (Real.log 2)]
    exact hconst
  have hsum0 : Tendsto
      (fun R : ℝ => Real.log 2 * R ^ (-(b - a)) + Real.log R / R ^ (b - a)) atTop (𝓝 0) := by
    rw [← add_zero (0 : ℝ)]
    exact hconst0.add hlog
  have hquot : Tendsto (fun R : ℝ => Real.log (2 * R) / R ^ (b - a)) atTop (𝓝 0) := by
    refine hsum0.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [Real.log_mul (by norm_num) hR.ne', add_div, div_eq_mul_inv,
      Real.rpow_neg hR.le (b - a), div_eq_mul_inv]
  have htend := hquot.const_mul C
  have htend0 : Tendsto (fun R : ℝ => C * (Real.log (2 * R) / R ^ (b - a))) atTop (𝓝 0) := by
    rw [← mul_zero C]
    exact htend
  have hnhds : Iio (1 : ℝ) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds one_pos
  filter_upwards [htend0.eventually hnhds, eventually_ge_atTop (1 : ℝ)] with R hR hR1
  have hRpos : 0 < R := by linarith
  have hsplit : R ^ a = R ^ (-(b - a)) * R ^ b := by
    rw [← Real.rpow_add hRpos, neg_sub, sub_add_cancel]
  have hRb : 0 ≤ R ^ b := Real.rpow_nonneg hRpos.le _
  calc
    C * R ^ a * Real.log (2 * R)
        = C * (R ^ (-(b - a)) * R ^ b) * Real.log (2 * R) := by rw [hsplit]
    _ = (C * (Real.log (2 * R) / R ^ (b - a))) * R ^ b := by
          rw [div_eq_mul_inv, ← Real.rpow_neg hRpos.le (b - a)]
          ring
    _ ≤ 1 * R ^ b := mul_le_mul_of_nonneg_right hR.le hRb
    _ = R ^ b := one_mul _

/-- Every large interval `(T, T + 1]` contains a radius separated from the listed zeros. -/
private theorem exists_good_radius {a : ℕ → Option ℂ} {B q C R0 : ℝ}
    (hBq : B < q) (hq : 0 < q) (hB : 0 ≤ B) (hC : 0 ≤ C) (hR0 : 1 ≤ R0)
    (hfin : ∀ R : ℝ, {n | ∃ w, a n = some w ∧ ‖w‖ ≤ R}.Finite)
    (hcount : ∀ R : ℝ, R0 ≤ R →
      (({n | ∃ w, a n = some w ∧ ‖w‖ ≤ R}.ncard : ℝ) ≤ C * R ^ B)) :
    ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T → ∃ R : ℝ, T < R ∧ R ≤ T + 1 ∧
      ∀ n w, a n = some w → |R - ‖w‖| < 1 → ‖w‖ ^ (-q) ≤ |R - ‖w‖| := by
  classical
  let K : ℝ := 2 * C * (4 : ℝ) ^ B
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (by norm_num) hC) (Real.rpow_nonneg (by norm_num) _)
  have hqB : 0 < q - B := sub_pos.mpr hBq
  let base : ℝ := K + 1
  have hbase : 0 < base := by dsimp [base]; linarith
  let expo : ℝ := (q - B)⁻¹
  let T0 : ℝ := max (max R0 2) (1 + base ^ expo)
  refine ⟨T0, ?_⟩
  intro T hT
  have hTge : (2 : ℝ) ≤ T :=
    ((le_max_right R0 2).trans (le_max_left _ _)).trans hT
  have hTR0 : R0 ≤ T := ((le_max_left R0 2).trans (le_max_left _ _)).trans hT
  have hTm : 0 < T - 1 := by linarith
  have hbasepow : base ^ expo ≤ T - 1 := by
    have h1 : 1 + base ^ expo ≤ T := (le_max_right _ _).trans hT
    linarith
  have hpow : base ≤ (T - 1) ^ (q - B) := by
    have hmono := Real.rpow_le_rpow (Real.rpow_nonneg hbase.le _) hbasepow hqB.le
    have hmul : expo * (q - B) = 1 := inv_mul_cancel₀ hqB.ne'
    have hid : (base ^ expo) ^ (q - B) = base := by
      rw [← Real.rpow_mul hbase.le, hmul, Real.rpow_one]
    calc
      base = (base ^ expo) ^ (q - B) := hid.symm
      _ ≤ (T - 1) ^ (q - B) := hmono
  have hball : {n | ∃ w, a n = some w ∧ ‖w‖ ≤ T + 2}.Finite := hfin (T + 2)
  have hT2 : R0 ≤ T + 2 := by linarith
  let u : Finset ℕ := hball.toFinset.filter fun n =>
    ∃ w, a n = some w ∧ T - 1 ≤ ‖w‖ ∧ ‖w‖ ≤ T + 2
  let wOf : ℕ → ℂ := fun n =>
    if h : ∃ w, a n = some w ∧ T - 1 ≤ ‖w‖ ∧ ‖w‖ ≤ T + 2 then Classical.choose h else 0
  let rad : ℕ → ℝ := fun n => ‖wOf n‖ ^ (-q)
  let bad : ℕ → Set ℝ := fun n =>
    if h : ∃ w, a n = some w ∧ T - 1 ≤ ‖w‖ ∧ ‖w‖ ≤ T + 2 then
      Ioo (‖wOf n‖ - rad n) (‖wOf n‖ + rad n)
    else ∅
  have hlen : ∀ n ∈ u, volume (bad n) ≤ ENNReal.ofReal (2 * (T - 1) ^ (-q)) := by
    intro n hn
    have hn' : ∃ w, a n = some w ∧ T - 1 ≤ ‖w‖ ∧ ‖w‖ ≤ T + 2 :=
      (Finset.mem_filter.mp hn).2
    have hw : a n = some (wOf n) ∧ T - 1 ≤ ‖wOf n‖ ∧ ‖wOf n‖ ≤ T + 2 := by
      have hwOf : wOf n = Classical.choose hn' := by
        simp only [wOf]
        rw [dite_eq_left hn']
      rw [hwOf]
      exact Classical.choose_spec hn'
    have hrle : rad n ≤ (T - 1) ^ (-q) := by
      dsimp [rad]
      exact Real.rpow_le_rpow_of_nonpos hTm hw.2.1 (neg_nonpos.mpr hq.le)
    have hbadn : bad n = Ioo (‖wOf n‖ - rad n) (‖wOf n‖ + rad n) := by
      simp only [bad]
      rw [dite_eq_left hn']
    rw [hbadn, Real.volume_Ioo]
    have hdiff : (‖wOf n‖ + rad n) - (‖wOf n‖ - rad n) = 2 * rad n := by ring
    rw [hdiff]
    refine ENNReal.ofReal_le_ofReal ?_
    exact mul_le_mul_of_nonneg_left hrle (by norm_num)
  have hcard : (u.card : ℝ) ≤ C * (T + 2) ^ B := by
    refine (Nat.cast_le.mpr ?_).trans (hcount (T + 2) hT2)
    refine (Finset.card_le_card (Finset.filter_subset _ _)).trans ?_
    rw [Set.ncard_eq_toFinset_card _ hball]
  have hscale : (u.card : ℝ) * (2 * (T - 1) ^ (-q)) ≤ K * (T - 1) ^ (B - q) := by
    have hnonneg : 0 ≤ 2 * (T - 1) ^ (-q) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg hTm.le _)
    have hstep1 : (u.card : ℝ) * (2 * (T - 1) ^ (-q)) ≤
        C * (T + 2) ^ B * (2 * (T - 1) ^ (-q)) :=
      mul_le_mul_of_nonneg_right hcard hnonneg
    have hfour : T + 2 ≤ 4 * (T - 1) := by linarith
    have hpow4 : (T + 2) ^ B ≤ (4 * (T - 1)) ^ B :=
      Real.rpow_le_rpow (by linarith) hfour hB
    have hsplit : (4 * (T - 1)) ^ B = (4 : ℝ) ^ B * (T - 1) ^ B :=
      Real.mul_rpow (by norm_num) hTm.le
    have hradd : (T - 1) ^ B * (T - 1) ^ (-q) = (T - 1) ^ (B - q) := by
      rw [← Real.rpow_add hTm]
      exact (congrArg (fun t : ℝ => (T - 1) ^ t) (sub_eq_add_neg B q)).symm
    calc
      (u.card : ℝ) * (2 * (T - 1) ^ (-q))
          ≤ C * (T + 2) ^ B * (2 * (T - 1) ^ (-q)) := hstep1
      _ ≤ C * ((4 : ℝ) ^ B * (T - 1) ^ B) * (2 * (T - 1) ^ (-q)) := by
          refine mul_le_mul_of_nonneg_right ?_ hnonneg
          exact mul_le_mul_of_nonneg_left (hpow4.trans_eq hsplit) hC
      _ = (2 * C * (4 : ℝ) ^ B) * ((T - 1) ^ B * (T - 1) ^ (-q)) := by ring
      _ = K * (T - 1) ^ (B - q) := by rw [hradd]
  have hlt : K * (T - 1) ^ (B - q) < 1 := by
    have hden : 0 < (T - 1) ^ (q - B) := Real.rpow_pos_of_pos hTm _
    have hinv : (T - 1) ^ (B - q) = ((T - 1) ^ (q - B))⁻¹ := by
      rw [← Real.rpow_neg hTm.le, neg_sub]
    rw [hinv]
    have hfrac : K / (T - 1) ^ (q - B) ≤ K / base :=
      div_le_div_of_nonneg_left hK0 hbase hpow
    have hunit : K / base < 1 := by
      dsimp [base]
      rw [div_lt_one (by linarith)]
      linarith
    calc
      K * ((T - 1) ^ (q - B))⁻¹ = K / (T - 1) ^ (q - B) := by rw [div_eq_mul_inv]
      _ ≤ K / base := hfrac
      _ < 1 := hunit
  have hvol : volume (⋃ n ∈ u, bad n) ≤ ENNReal.ofReal (K * (T - 1) ^ (B - q)) := by
    refine (measure_biUnion_finset_le u bad).trans ?_
    refine (Finset.sum_le_sum hlen).trans ?_
    have hconst : ∑ n ∈ u, ENNReal.ofReal (2 * (T - 1) ^ (-q)) =
        ENNReal.ofReal ((u.card : ℝ) * (2 * (T - 1) ^ (-q))) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [show (u.card : ℝ≥0∞) = ENNReal.ofReal (u.card : ℝ) from
        (ENNReal.ofReal_natCast u.card).symm,
        (ENNReal.ofReal_mul (Nat.cast_nonneg u.card)).symm]
    rw [hconst]
    exact ENNReal.ofReal_le_ofReal hscale
  have hnot : ¬ Ioc T (T + 1) ⊆ ⋃ n ∈ u, bad n := by
    intro hinc
    have hle := measure_mono (μ := volume) hinc
    have hleft : volume (Ioc T (T + 1)) = 1 := by
      have hsub : (T + 1) - T = 1 := by ring
      rw [Real.volume_Ioc, hsub, ENNReal.ofReal_one]
    have hright : volume (⋃ n ∈ u, bad n) < 1 := by
      refine lt_of_le_of_lt hvol ?_
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hlt
    exact lt_irrefl _ <| hleft.symm.trans_lt (hle.trans_lt hright)
  obtain ⟨R, hRmem, hRout⟩ := Set.not_subset.mp hnot
  refine ⟨R, hRmem.1, hRmem.2, ?_⟩
  intro n w hw hclose
  have hwin : T - 1 ≤ ‖w‖ ∧ ‖w‖ ≤ T + 2 := by
    have habs := abs_lt.mp hclose
    constructor <;> linarith [hRmem.1, hRmem.2, habs.1, habs.2]
  have hnex : ∃ w', a n = some w' ∧ T - 1 ≤ ‖w'‖ ∧ ‖w'‖ ≤ T + 2 :=
    ⟨w, hw, hwin.1, hwin.2⟩
  have hn : n ∈ u := by
    refine Finset.mem_filter.mpr ⟨?_, hnex⟩
    exact hball.mem_toFinset.mpr ⟨w, hw, hwin.2⟩
  have hnotn : R ∉ bad n := by
    intro hbadR
    exact hRout (mem_iUnion₂.mpr ⟨n, hn, hbadR⟩)
  have hwOf : w = wOf n := by
    have hspec := Classical.choose_spec hnex
    have hwo : wOf n = Classical.choose hnex := by
      simp only [wOf]
      rw [dite_eq_left hnex]
    exact Option.some_injective _ (hw.symm.trans (hwo ▸ hspec.1))
  have hbadn : bad n = Ioo (‖w‖ - ‖w‖ ^ (-q)) (‖w‖ + ‖w‖ ^ (-q)) := by
    simp only [bad, rad]
    rw [dite_eq_left hnex, hwOf]
  rw [hbadn] at hnotn
  have hge : ¬ |R - ‖w‖| < ‖w‖ ^ (-q) := by
    intro hltR
    rw [abs_lt] at hltR
    exact hnotn ⟨by linarith, by linarith⟩
  exact le_of_not_gt hge

/-- A lower bound for `log ‖Eₚ(z / w)‖` on the circle of radius `R`. -/
private def genusFactorLogLower (p : ℕ) (a : ℕ → Option ℂ) (R : ℝ) (n : ℕ) : ℝ :=
  match a n with
  | none => 0
  | some w =>
      if 2 * R ≤ ‖w‖ then -2 * R ^ ((p : ℝ) + 1) * ‖w‖ ^ (-((p : ℝ) + 1))
      else -((p : ℝ) + 2) * Real.log (2 * R) - (p : ℝ) -
        (p : ℝ) * R ^ (p : ℝ) * ‖w‖ ^ (-(p : ℝ))

/-- Each canonical factor lies above `genusFactorLogLower` on a separated circle. -/
private theorem log_norm_genusFactor_lower {p : ℕ} {a : ℕ → Option ℂ} {n : ℕ} {z : ℂ} {R : ℝ}
    (hne : ∀ w, a n = some w → w ≠ 0) (hR : 1 ≤ R) (hz : ‖z‖ = R)
    (hgood : ∀ w, a n = some w → |R - ‖w‖| < 1 →
      ‖w‖ ^ (-((p : ℝ) + 1)) ≤ |R - ‖w‖|) :
    genusFactorLogLower p a R n ≤ Real.log ‖genusFactor p a n z‖ := by
  classical
  cases ha : a n with
  | none =>
    have hlow : genusFactorLogLower p a R n = 0 := by simp [genusFactorLogLower, ha]
    rw [hlow, genusFactor_none ha, norm_one, Real.log_one]
  | some w =>
    have hw0 : w ≠ 0 := hne w ha
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hlow : genusFactorLogLower p a R n =
        if 2 * R ≤ ‖w‖ then -2 * R ^ ((p : ℝ) + 1) * ‖w‖ ^ (-((p : ℝ) + 1))
        else -((p : ℝ) + 2) * Real.log (2 * R) - (p : ℝ) -
          (p : ℝ) * R ^ (p : ℝ) * ‖w‖ ^ (-(p : ℝ)) := by
      simp [genusFactorLogLower, ha]
    rw [hlow, genusFactor_some ha]
    split_ifs with hfar
    ·
      have hu : ‖z / w‖ ≤ 1 / 2 := by
        rw [norm_div, hz, div_le_iff₀ hwpos]
        linarith
      have hhalf := log_norm_weierstrassFactor_ge_half (p := p) hu
      have hpow : (R / ‖w‖) ^ (p + 1) =
          R ^ ((p : ℝ) + 1) * ‖w‖ ^ (-((p : ℝ) + 1)) := by
        have hcast : ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 := by simp [Nat.cast_add, Nat.cast_one]
        rw [div_pow, ← Real.rpow_natCast R (p + 1), ← Real.rpow_natCast ‖w‖ (p + 1), hcast,
          div_eq_mul_inv, ← Real.rpow_neg (norm_nonneg w)]
      calc
        -2 * R ^ ((p : ℝ) + 1) * ‖w‖ ^ (-((p : ℝ) + 1))
            = -2 * (R / ‖w‖) ^ (p + 1) := by rw [mul_assoc, ← hpow]
        _ = -2 * ‖z / w‖ ^ (p + 1) := by rw [norm_div, hz]
        _ ≤ Real.log ‖weierstrassFactor p (z / w)‖ := hhalf
    · have hnear : ‖w‖ ≤ 2 * R := le_of_lt (lt_of_not_ge hfar)
      have hu : z / w ≠ 1 := by
        intro hdiv
        have hz_w : z = w := by rw [div_eq_iff hw0, one_mul] at hdiv; exact hdiv
        have hzero : |R - ‖w‖| = 0 := by rw [← hz_w, hz, sub_self, abs_zero]
        have hsep := hgood w ha (by rw [hzero]; norm_num)
        exact (not_le_of_gt (Real.rpow_pos_of_pos hwpos _)) (by simpa [hzero] using hsep)
      have hbase := log_norm_weierstrassFactor_ge (p := p) (u := z / w) hu
      have hdist : |R - ‖w‖| ≤ ‖z - w‖ := by simpa [hz] using abs_norm_sub_norm_le z w
      have hzwpos : 0 < ‖z - w‖ := by
        rw [norm_pos_iff, ne_eq, sub_eq_zero]
        intro hzw
        exact hu (by rw [hzw, div_self hw0])
      have hnorm : ‖(1 : ℂ) - z / w‖ = ‖z - w‖ / ‖w‖ := by
        have hsub : (w - z) / w = 1 - z / w := by rw [sub_div, div_self hw0]
        rw [← hsub, norm_div, norm_sub_rev]
      have hlogu : Real.log ‖(1 : ℂ) - z / w‖ = Real.log ‖z - w‖ - Real.log ‖w‖ := by
        rw [hnorm, Real.log_div hzwpos.ne' hwpos.ne']
      have hlogw : Real.log ‖w‖ ≤ Real.log (2 * R) :=
        Real.log_le_log hwpos hnear
      have hlog2 : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
      have hlogzw : -((p : ℝ) + 1) * Real.log (2 * R) ≤ Real.log ‖z - w‖ := by
        by_cases hclose : |R - ‖w‖| < 1
        · have hsep := (hgood w ha hclose).trans hdist
          have hlogsep := Real.log_le_log (Real.rpow_pos_of_pos hwpos _) hsep
          rw [Real.log_rpow hwpos] at hlogsep
          have habs := abs_lt.mp hclose
          have hwR : ‖w‖ ≤ 2 * R := by linarith
          exact hlogsep.trans' <|
            mul_le_mul_of_nonpos_left (Real.log_le_log hwpos hwR) (by linarith)
        · have hone : (1 : ℝ) ≤ ‖z - w‖ := (le_of_not_gt hclose).trans hdist
          have hnonneg : 0 ≤ Real.log ‖z - w‖ := by
            rw [← Real.log_one]
            exact Real.log_le_log zero_lt_one hone
          exact hnonneg.trans' <| mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog2
      have hlog1 : -((p : ℝ) + 2) * Real.log (2 * R) ≤ Real.log ‖(1 : ℂ) - z / w‖ := by
        rw [hlogu]
        calc
          -((p : ℝ) + 2) * Real.log (2 * R)
              = -((p : ℝ) + 1) * Real.log (2 * R) + -Real.log (2 * R) := by ring
          _ ≤ Real.log ‖z - w‖ + -Real.log ‖w‖ := by
              refine add_le_add hlogzw ?_
              exact neg_le_neg hlogw
          _ = Real.log ‖z - w‖ - Real.log ‖w‖ := by ring
      have hupow : ‖z / w‖ ^ p = R ^ (p : ℝ) * ‖w‖ ^ (-(p : ℝ)) := by
        rw [norm_div, hz, div_pow, ← Real.rpow_natCast R p, ← Real.rpow_natCast ‖w‖ p,
          div_eq_mul_inv, ← Real.rpow_neg (norm_nonneg w)]
      calc
        -((p : ℝ) + 2) * Real.log (2 * R) - (p : ℝ) -
              (p : ℝ) * R ^ (p : ℝ) * ‖w‖ ^ (-(p : ℝ))
            = -((p : ℝ) + 2) * Real.log (2 * R) -
              (p : ℝ) * (‖z / w‖ ^ p + 1) := by rw [hupow]; ring
        _ ≤ Real.log ‖(1 : ℂ) - z / w‖ - (p : ℝ) * (‖z / w‖ ^ p + 1) := by
            linarith
        _ ≤ Real.log ‖weierstrassFactor p (z / w)‖ := hbase

/-- On separated circles the canonical product has a power-logarithmic lower bound. -/
private theorem exists_log_norm_tprod_lower {a : ℕ → Option ℂ} {p : ℕ} {B C R0 : ℝ}
    (hpB : (p : ℝ) < B) (hBq : B < (p : ℝ) + 1) (hC : 0 ≤ C) (hR0 : 1 ≤ R0)
    (hsum : Summable (slopeWeight p a)) (hne : ∀ n w, a n = some w → w ≠ 0)
    (hfin : ∀ R : ℝ, {n | ∃ w, a n = some w ∧ ‖w‖ ≤ R}.Finite)
    (hcount : ∀ R : ℝ, R0 ≤ R →
      (({n | ∃ w, a n = some w ∧ ‖w‖ ≤ R}.ncard : ℝ) ≤ C * R ^ B)) :
    ∃ K : ℝ, ∀ {R : ℝ}, R0 ≤ R →
      (∀ n w, a n = some w → |R - ‖w‖| < 1 →
        ‖w‖ ^ (-((p : ℝ) + 1)) ≤ |R - ‖w‖|) →
      ∀ z : ℂ, ‖z‖ = R →
        -K * R ^ B * (Real.log (2 * R) + 1) ≤
          Real.log ‖∏' n, genusFactor p a n z‖ := by
  classical
  let q : ℝ := (p : ℝ) + 1
  let α : ℝ := (p : ℝ)
  have hqB : B < q := by simpa [q] using hBq
  have hαB : α < B := by dsimp [α]; exact hpB
  let sSmall : Finset ℕ := (hfin R0).toFinset.filter fun n =>
    ∃ w, a n = some w ∧ ‖w‖ ≤ R0
  let wpow : ℕ → ℝ := fun n =>
    match a n with
    | none => 0
    | some w => ‖w‖ ^ (-α)
  let S0 : ℝ := ∑ n ∈ sSmall, wpow n
  have hS0 : 0 ≤ S0 := by
    dsimp [S0]
    refine Finset.sum_nonneg fun n _ => ?_
    cases ha : a n with
    | none => simp [wpow, ha]
    | some w => simp [wpow, ha, Real.rpow_nonneg]
  let headCoeff : ℝ :=
    C * (2 : ℝ) ^ B * (4 : ℝ) ^ (B - α) / ((2 : ℝ) ^ (B - α) - 1)
  let tailCoeff : ℝ := C * (2 : ℝ) ^ B / (1 - (2 : ℝ) ^ (B - q))
  have hhead : 0 ≤ headCoeff := by
    have hden : 0 < (2 : ℝ) ^ (B - α) - 1 := by
      have hgt := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (sub_pos.mpr hαB)
      linarith
    dsimp [headCoeff]
    exact div_nonneg (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg (by norm_num) _)) hden.le
  have htail : 0 ≤ tailCoeff := by
    have hden : 0 < 1 - (2 : ℝ) ^ (B - q) := by
      have hlt := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
        (sub_neg.mpr hqB)
      linarith
    dsimp [tailCoeff]
    exact div_nonneg (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)) hden.le
  let K : ℝ := C * (2 : ℝ) ^ B * (α + 2) + α * (S0 + headCoeff) + 2 * tailCoeff
  refine ⟨K, ?_⟩
  intro R hR hgood z hz
  have hR1 : 1 ≤ R := hR0.trans hR
  have hRpos : 0 < R := by linarith
  have h2R : R0 ≤ 2 * R := by linarith
  let low : ℕ → ℝ := genusFactorLogLower p a R
  have hlow : ∀ n, low n ≤ Real.log ‖genusFactor p a n z‖ := by
    intro n
    exact log_norm_genusFactor_lower (fun w hw => hne n w hw) hR1 hz
      (fun w hw hclose => hgood n w hw hclose)
  let nearFun : ℕ → ℝ := fun n =>
    match a n with
    | none => 0
    | some w =>
        if ‖w‖ < 2 * R then
          -(α + 2) * Real.log (2 * R) - α - α * R ^ α * ‖w‖ ^ (-α)
        else 0
  let farFun : ℕ → ℝ := fun n =>
    match a n with
    | none => 0
    | some w =>
        if 2 * R ≤ ‖w‖ then -2 * R ^ q * ‖w‖ ^ (-q) else 0
  have hsplit : ∀ n, low n = nearFun n + farFun n := by
    intro n
    cases ha : a n with
    | none => simp [low, genusFactorLogLower, nearFun, farFun, ha]
    | some w =>
      by_cases hfar : 2 * R ≤ ‖w‖
      · simp [low, genusFactorLogLower, nearFun, farFun, ha, hfar, q]
      · have hlt : ‖w‖ < 2 * R := lt_of_not_ge hfar
        simp [low, genusFactorLogLower, nearFun, farFun, ha, hfar, hlt, α]
  let weight : ℕ → ℝ := fun n =>
    match a n with
    | none => 0
    | some w => if 2 * R ≤ ‖w‖ then ‖w‖ ^ (-q) else 0
  have hweight_nn : ∀ n, 0 ≤ weight n := by
    intro n
    cases ha : a n with
    | none => simp [weight, ha]
    | some w =>
      simp only [weight, ha]
      split_ifs
      · exact Real.rpow_nonneg (norm_nonneg _) _
      · exact le_rfl
  have hweight_le : ∀ n, weight n ≤ slopeWeight p a n := by
    intro n
    cases ha : a n with
    | none => simp [weight, slopeWeight, ha]
    | some w =>
      simp only [weight, slopeWeight, ha, q]
      split_ifs
      · rfl
      · exact Real.rpow_nonneg (norm_nonneg _) _
  have hweight_sum : Summable weight :=
    Summable.of_norm_bounded hsum fun n => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hweight_nn n)]
      exact hweight_le n
  have hfar_eq : ∀ n, farFun n = -2 * R ^ q * weight n := by
    intro n
    cases ha : a n with
    | none => simp [farFun, weight, ha]
    | some w =>
      by_cases hfar : 2 * R ≤ ‖w‖
      · simp [farFun, weight, ha, hfar]
      · simp [farFun, weight, ha, hfar]
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have htail_bound := dyadic_tail_le (a := a) (B := B) (q := q) (C := C) (R0 := R0)
    hqB hq0 hC hR0 hfin hcount hR
  have htsum_weight : ∑' n, weight n ≤ tailCoeff * R ^ (B - q) := by
    simpa [weight, tailCoeff, q] using htail_bound
  have hfar_sum : Summable farFun := by
    have hmul : Summable fun n => -2 * R ^ q * weight n := hweight_sum.mul_left _
    exact hmul.congr fun n => (hfar_eq n).symm
  have htsum_far : -2 * tailCoeff * R ^ B ≤ ∑' n, farFun n := by
    have hmul := tsum_mul_left (L := SummationFilter.unconditional ℕ)
      (a := -2 * R ^ q) (f := weight)
    have hnonpos : -2 * R ^ q ≤ 0 := by
      have hpow : 0 ≤ R ^ q := Real.rpow_nonneg hRpos.le _
      linarith
    have hstep := mul_le_mul_of_nonpos_left htsum_weight hnonpos
    have hprod : R ^ q * R ^ (B - q) = R ^ B := by
      rw [← Real.rpow_add hRpos]
      exact congrArg (fun t : ℝ => R ^ t) (by ring)
    have hfun : farFun = fun n => -2 * R ^ q * weight n := funext hfar_eq
    calc
      -2 * tailCoeff * R ^ B = -2 * R ^ q * (tailCoeff * R ^ (B - q)) := by
        rw [← hprod]; ring
      _ ≤ -2 * R ^ q * ∑' n, weight n := hstep
      _ = ∑' n, -2 * R ^ q * weight n := hmul.symm
      _ = ∑' n, farFun n := congrArg (fun f : ℕ → ℝ => ∑' n, f n) hfun.symm
  let sNear : Finset ℕ := (hfin (2 * R)).toFinset.filter fun n =>
    ∃ w, a n = some w ∧ ‖w‖ < 2 * R
  have hnear_zero : ∀ n ∉ sNear, nearFun n = 0 := by
    intro n hn
    cases ha : a n with
    | none => simp [nearFun, ha]
    | some w =>
      by_cases hlt : ‖w‖ < 2 * R
      · have hmem : n ∈ sNear := by
          refine Finset.mem_filter.mpr ⟨?_, ⟨w, ha, hlt⟩⟩
          exact (hfin (2 * R)).mem_toFinset.mpr ⟨w, ha, hlt.le⟩
        exact (hn hmem).elim
      · simp [nearFun, ha, hlt]
  have hnear_sum : Summable nearFun := summable_of_ne_finset_zero hnear_zero
  have htsum_near : ∑' n, nearFun n = ∑ n ∈ sNear, nearFun n :=
    tsum_eq_sum (L := SummationFilter.unconditional ℕ) hnear_zero
  have hcard : (sNear.card : ℝ) ≤ C * (2 * R) ^ B := by
    refine (Nat.cast_le.mpr ?_).trans (hcount (2 * R) h2R)
    refine (Finset.card_le_card (Finset.filter_subset _ _)).trans ?_
    exact le_of_eq (Set.ncard_eq_toFinset_card _ (hfin (2 * R))).symm
  have htwo : (2 * R) ^ B = (2 : ℝ) ^ B * R ^ B :=
    Real.mul_rpow (by norm_num) hRpos.le
  let sHead : Finset ℕ := (hfin (2 * R)).toFinset.filter fun n =>
    ∃ w, a n = some w ∧ R0 ≤ ‖w‖ ∧ ‖w‖ < 2 * R
  have hhead_sum : ∑ n ∈ sHead, wpow n ≤ headCoeff * R ^ (B - α) := by
    have hmem : ∀ n ∈ sHead, ∃ w, a n = some w ∧ R0 ≤ ‖w‖ ∧ ‖w‖ < 2 * R :=
      fun n hn => (Finset.mem_filter.mp hn).2
    have hdy := dyadic_head_le (a := a) (B := B) (α := α) (C := C) (R0 := R0)
      (Nat.cast_nonneg p) hαB hC hR0 hfin hcount hR sHead hmem
    simpa [wpow, headCoeff, α] using hdy
  have hsmall_sum : ∑ n ∈ sSmall, wpow n = S0 := rfl
  have hcover : sNear ⊆ sSmall ∪ sHead := by
    intro n hn
    obtain ⟨hball, hex⟩ := Finset.mem_filter.mp hn
    obtain ⟨w, hw, hlt⟩ := hex
    by_cases hle : ‖w‖ ≤ R0
    · exact Finset.mem_union_left _ <| Finset.mem_filter.mpr
        ⟨(hfin R0).mem_toFinset.mpr ⟨w, hw, hle⟩, ⟨w, hw, hle⟩⟩
    · exact Finset.mem_union_right _ <| Finset.mem_filter.mpr
        ⟨hball, ⟨w, hw, le_of_not_ge hle, hlt⟩⟩
  have hwpow_nn : ∀ n, 0 ≤ wpow n := by
    intro n
    cases ha : a n with
    | none => simp [wpow, ha]
    | some w => simp [wpow, ha, Real.rpow_nonneg]
  have hnear_w : ∑ n ∈ sNear, wpow n ≤ S0 + headCoeff * R ^ (B - α) := by
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg hcover
      (fun n _ _ => hwpow_nn n)
    have hinter : 0 ≤ ∑ n ∈ sSmall ∩ sHead, wpow n :=
      Finset.sum_nonneg fun n _ => hwpow_nn n
    have hunion := Finset.sum_union_inter (s₁ := sSmall) (s₂ := sHead) (f := wpow)
    have hsplit_sum : ∑ n ∈ sSmall ∪ sHead, wpow n ≤ ∑ n ∈ sSmall, wpow n +
        ∑ n ∈ sHead, wpow n := by linarith
    have hsum_le : ∑ n ∈ sSmall ∪ sHead, wpow n ≤ S0 + headCoeff * R ^ (B - α) := by
      calc
        ∑ n ∈ sSmall ∪ sHead, wpow n ≤ ∑ n ∈ sSmall, wpow n + ∑ n ∈ sHead, wpow n :=
          hsplit_sum
        _ ≤ S0 + headCoeff * R ^ (B - α) := by
          rw [hsmall_sum]
          exact add_le_add le_rfl hhead_sum
    exact hsub.trans hsum_le
  have hpoint : ∀ n ∈ sNear, nearFun n =
      -(α + 2) * Real.log (2 * R) - α - α * R ^ α * wpow n := by
    intro n hn
    obtain ⟨_, hex⟩ := Finset.mem_filter.mp hn
    obtain ⟨w, hw, hlt⟩ := hex
    simp [nearFun, wpow, hw, hlt, α]
  have hsum_near_eq : ∑ n ∈ sNear, nearFun n =
      (sNear.card : ℝ) * (-(α + 2) * Real.log (2 * R) - α) -
        α * R ^ α * ∑ n ∈ sNear, wpow n := by
    rw [Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      Finset.mul_sum]
  have hlognn : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  have hlog1 : 1 ≤ Real.log (2 * R) + 1 := by linarith
  have hRb : 0 ≤ R ^ B := Real.rpow_nonneg hRpos.le _
  have hRα : R ^ α ≤ R ^ B :=
    Real.rpow_le_rpow_of_exponent_le hR1 (le_of_lt hαB)
  have hRsplit : R ^ α * R ^ (B - α) = R ^ B := by
    rw [← Real.rpow_add hRpos]
    exact congrArg (fun t : ℝ => R ^ t) (by ring)
  have hN : (sNear.card : ℝ) * ((α + 2) * Real.log (2 * R) + α) ≤
      C * (2 : ℝ) ^ B * (α + 2) * R ^ B * (Real.log (2 * R) + 1) := by
    have hterm : (α + 2) * Real.log (2 * R) + α ≤ (α + 2) * (Real.log (2 * R) + 1) := by
      linarith
    have hcard' : (sNear.card : ℝ) ≤ C * (2 : ℝ) ^ B * R ^ B := by
      calc
        (sNear.card : ℝ) ≤ C * (2 * R) ^ B := hcard
        _ = C * (2 : ℝ) ^ B * R ^ B := by rw [htwo]; ring
    have hnonneg : 0 ≤ (α + 2) * Real.log (2 * R) + α := by
      have hα2 : 0 ≤ α + 2 := by dsimp [α]; linarith
      nlinarith
    calc
      (sNear.card : ℝ) * ((α + 2) * Real.log (2 * R) + α)
          ≤ (C * (2 : ℝ) ^ B * R ^ B) * ((α + 2) * (Real.log (2 * R) + 1)) := by
            exact mul_le_mul hcard' hterm hnonneg (mul_nonneg
              (mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)) hRb)
      _ = C * (2 : ℝ) ^ B * (α + 2) * R ^ B * (Real.log (2 * R) + 1) := by ring
  have hpow_bound : α * R ^ α * ∑ n ∈ sNear, wpow n ≤
      α * (S0 + headCoeff) * R ^ B * (Real.log (2 * R) + 1) := by
    have hα0 : 0 ≤ α := by dsimp [α]; exact Nat.cast_nonneg p
    have hRαnn : 0 ≤ R ^ α := Real.rpow_nonneg hRpos.le _
    have hleft : α * (R ^ α * S0) ≤ α * (R ^ B * S0) := by
      refine mul_le_mul_of_nonneg_left ?_ hα0
      exact mul_le_mul_of_nonneg_right hRα hS0
    have hright : α * (R ^ α * (headCoeff * R ^ (B - α))) = α * (headCoeff * R ^ B) := by
      calc
        α * (R ^ α * (headCoeff * R ^ (B - α)))
            = α * headCoeff * (R ^ α * R ^ (B - α)) := by ring
        _ = α * headCoeff * R ^ B := by rw [hRsplit]
        _ = α * (headCoeff * R ^ B) := by ring
    calc
      α * R ^ α * ∑ n ∈ sNear, wpow n
          ≤ α * R ^ α * (S0 + headCoeff * R ^ (B - α)) :=
            mul_le_mul_of_nonneg_left hnear_w (mul_nonneg hα0 hRαnn)
      _ = α * (R ^ α * S0) + α * (R ^ α * (headCoeff * R ^ (B - α))) := by ring
      _ ≤ α * (R ^ B * S0) + α * (headCoeff * R ^ B) := by
          exact add_le_add hleft (le_of_eq hright)
      _ = α * (S0 + headCoeff) * R ^ B := by ring
      _ ≤ α * (S0 + headCoeff) * R ^ B * (Real.log (2 * R) + 1) :=
          le_mul_of_one_le_right
            (mul_nonneg (mul_nonneg hα0 (add_nonneg hS0 hhead)) hRb) hlog1
  have hnear_ge : -(C * (2 : ℝ) ^ B * (α + 2) + α * (S0 + headCoeff)) * R ^ B *
      (Real.log (2 * R) + 1) ≤ ∑ n ∈ sNear, nearFun n := by
    rw [hsum_near_eq]
    have hident : (sNear.card : ℝ) * (-(α + 2) * Real.log (2 * R) - α) -
        α * R ^ α * ∑ n ∈ sNear, wpow n =
        -((sNear.card : ℝ) * ((α + 2) * Real.log (2 * R) + α)) -
          α * R ^ α * ∑ n ∈ sNear, wpow n := by ring
    rw [hident]
    have hneg1 : -(C * (2 : ℝ) ^ B * (α + 2) * R ^ B * (Real.log (2 * R) + 1)) ≤
        -((sNear.card : ℝ) * ((α + 2) * Real.log (2 * R) + α)) := neg_le_neg hN
    have hneg2 : -(α * (S0 + headCoeff) * R ^ B * (Real.log (2 * R) + 1)) ≤
        -(α * R ^ α * ∑ n ∈ sNear, wpow n) := neg_le_neg hpow_bound
    have hjoin : -(C * (2 : ℝ) ^ B * (α + 2) + α * (S0 + headCoeff)) * R ^ B *
        (Real.log (2 * R) + 1) =
        -(C * (2 : ℝ) ^ B * (α + 2) * R ^ B * (Real.log (2 * R) + 1)) +
          -(α * (S0 + headCoeff) * R ^ B * (Real.log (2 * R) + 1)) := by ring
    exact hjoin.trans_le (add_le_add hneg1 hneg2)
  have hfar_ge : -((2 * tailCoeff) * R ^ B * (Real.log (2 * R) + 1)) ≤ ∑' n, farFun n := by
    have hscale : 2 * tailCoeff * R ^ B ≤ 2 * tailCoeff * R ^ B * (Real.log (2 * R) + 1) :=
      le_mul_of_one_le_right (mul_nonneg (mul_nonneg (by norm_num) htail) hRb) hlog1
    have hneg_eq : -(2 * tailCoeff * R ^ B) = -2 * tailCoeff * R ^ B := by ring
    exact (neg_le_neg hscale).trans (hneg_eq.trans_le htsum_far)
  have hlow_sum : Summable low :=
    (hnear_sum.add hfar_sum).congr fun n => (hsplit n).symm
  have htsum_split : ∑' n, low n = ∑' n, nearFun n + ∑' n, farFun n := by
    rw [← hnear_sum.tsum_add hfar_sum]
    refine tsum_congr ?_
    intro n
    exact hsplit n
  have htsum_low : -K * R ^ B * (Real.log (2 * R) + 1) ≤ ∑' n, low n := by
    rw [htsum_split, htsum_near]
    have hjoin : -K * R ^ B * (Real.log (2 * R) + 1) =
        -(C * (2 : ℝ) ^ B * (α + 2) + α * (S0 + headCoeff)) * R ^ B *
          (Real.log (2 * R) + 1) +
          -((2 * tailCoeff) * R ^ B * (Real.log (2 * R) + 1)) := by
      dsimp [K]
      ring
    exact hjoin.trans_le (add_le_add hnear_ge hfar_ge)
  have hsub := summable_norm_genusFactor_sub_one p a hsum hne z
  have hlogsum : Summable fun n => Real.log ‖genusFactor p a n z‖ := by
    have h := (hsub.summable_log_norm_one_add (f := fun n => genusFactor p a n z - 1))
    refine h.congr fun n => ?_
    rw [show (1 : ℂ) + (genusFactor p a n z - 1) = genusFactor p a n z by ring]
  have hcmp : ∑' n, low n ≤ ∑' n, Real.log ‖genusFactor p a n z‖ :=
    hlow_sum.tsum_le_tsum hlow hlogsum
  have hFne : ∀ n, genusFactor p a n z ≠ 0 := by
    intro n hzero
    have hsome := (genusFactor_eq_zero_iff (fun w hw => hne n w hw)).mp hzero
    have hsep := hgood n z hsome (by simp [hz])
    exact (not_le_of_gt (Real.rpow_pos_of_pos (norm_pos_iff.mpr (hne n z hsome)) _))
      (by simpa [hz] using hsep)
  have hposF : ∀ n, 0 < ‖genusFactor p a n z‖ := fun n => norm_pos_iff.mpr (hFne n)
  have hprod := Real.rexp_tsum_eq_tprod hposF hlogsum
  have hnorm := (multipliable_genusFactor p a hsum hne z).norm_tprod
  have hlogeq : Real.log ‖∏' n, genusFactor p a n z‖ =
      ∑' n, Real.log ‖genusFactor p a n z‖ := by
    rw [hnorm, ← hprod, Real.log_exp]
  exact (htsum_low.trans hcmp).trans_eq hlogeq.symm

/-- A constant, a lower power, and that power times a logarithm are absorbed by a higher power. -/
private theorem eventually_growth_exponent_le {B t K C : ℝ} (hBt : B < t) (ht : 0 < t)
    (hC : 0 < C) :
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
    (R0 := 1) hBq (by positivity) hB0 hCpos.le (by norm_num) hfin hcount
  obtain ⟨Cg, hCg, hWith⟩ := (hord.isBigO hρB).exists_pos
  rcases (hasBasis_cobounded_norm (E := ℂ)).eventually_iff.mp (isBigOWith_iff.mp hWith) with
    ⟨M, -, hM⟩
  have habsorb := eventually_growth_exponent_le (B := B) (t := t') (K := K) (C := Cg) hBt ht'0 hCg
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
