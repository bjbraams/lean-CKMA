/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Complex.EntireGrowth.Zeros

import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.Field
import TauCeti.Analysis.Complex.GrowthOrder
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Counting the enumerated zeros of an entire function

Counting estimates for an `Option`-valued list of zeros `a : ℕ → Option ℂ`, used in Hadamard
factorization. The listed zeros of an entire function of order at most `ρ` in the disk of radius
`R` number `O(R ^ B)` for every `B > ρ`, by `TauCeti.OrderLE.eventually_sum_divisor_le`. For any
list with this count, dyadic annuli bound the power sums `∑ ‖w‖ ^ (-q)` over `‖w‖ ≥ 2R` and over
`R0 ≤ ‖w‖ < 2R`.

## Main results

* `CKMA.enumeratedBall_finite`, `CKMA.exists_enumerated_count_bound`: finiteness and the
  `O(R ^ B)` count of the enumerated zeros in a disk.
* `CKMA.exists_uniform_enumerated_count`: the count bound at every radius past a threshold.
* `CKMA.dyadic_tail_le`: `∑_{‖w‖ ≥ 2R} ‖w‖ ^ (-q) ≤ C' R ^ (B - q)` for `B < q`.
* `CKMA.dyadic_head_le`: `∑_{R0 ≤ ‖w‖ < 2R} ‖w‖ ^ (-α) ≤ C' R ^ (B - α)` for `α < B`.
* `CKMA.eventually_mul_rpow_le`, `CKMA.eventually_log_mul_rpow_le`: a lower power, also times
  `log (2R)`, is eventually absorbed by a higher one.
-/

public section

noncomputable section

namespace CKMA

open Asymptotics Bornology Classical Complex Filter Finset MeasureTheory Metric Set Topology
open scoped BigOperators ENNReal

variable {g : ℂ → ℂ}

/-- The listed zeros of modulus at most `R` form a finite set. -/
theorem enumeratedBall_finite (hg : Differentiable ℂ g) (R : ℝ) :
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
theorem exists_enumerated_count_bound (hg : Differentiable ℂ g) {ρ B : ℝ}
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
    simp
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
theorem dyadic_tail_le {a : ℕ → Option ℂ} {B q C R0 : ℝ} (hBq : B < q) (hq : 0 ≤ q)
    (hC : 0 ≤ C) (hR0 : 1 ≤ R0)
    (hfin : ∀ R : ℝ, {n | ∃ w, a n = some w ∧ ‖w‖ ≤ R}.Finite)
    (hcount : ∀ R : ℝ, R0 ≤ R →
      (({n | ∃ w, a n = some w ∧ ‖w‖ ≤ R}.ncard : ℝ) ≤ C * R ^ B))
    {R : ℝ} (hR : R0 ≤ R) :
    ∑' n, (a n).elim (0 : ℝ) (fun w => if 2 * R ≤ ‖w‖ then ‖w‖ ^ (-q) else 0) ≤
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
  suffices hf : ∑' n, f n ≤ C * (2 : ℝ) ^ B / (1 - (2 : ℝ) ^ (B - q)) * R ^ (B - q) by
    convert hf using 3 with n
    dsimp only [f]
    cases a n <;> rfl
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
theorem exists_uniform_enumerated_count (hg : Differentiable ℂ g)
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
theorem dyadic_head_le {a : ℕ → Option ℂ} {B α C R0 : ℝ}
    (hα : 0 ≤ α) (hαB : α < B) (hC : 0 ≤ C) (hR0 : 1 ≤ R0)
    (hfin : ∀ R : ℝ, {n | ∃ w, a n = some w ∧ ‖w‖ ≤ R}.Finite)
    (hcount : ∀ R : ℝ, R0 ≤ R →
      (({n | ∃ w, a n = some w ∧ ‖w‖ ≤ R}.ncard : ℝ) ≤ C * R ^ B))
    {R : ℝ} (hR : R0 ≤ R) (u : Finset ℕ)
    (hu : ∀ n ∈ u, ∃ w, a n = some w ∧ R0 ≤ ‖w‖ ∧ ‖w‖ < 2 * R) :
    ∑ n ∈ u, (a n).elim (0 : ℝ) (fun w => ‖w‖ ^ (-α)) ≤
      C * (2 : ℝ) ^ B * (4 : ℝ) ^ (B - α) / ((2 : ℝ) ^ (B - α) - 1) * R ^ (B - α) := by
  classical
  let θ : ℝ := (2 : ℝ) ^ (B - α)
  have hθ1 : 1 < θ := Real.one_lt_rpow (by norm_num) (sub_pos.mpr hαB)
  have hθ0 : 0 < θ := zero_lt_one.trans hθ1
  let M : ℕ := ⌊Real.logb 2 R⌋₊ + 1
  let f : ℕ → ℝ := fun n => match a n with
    | none => 0
    | some w => ‖w‖ ^ (-α)
  suffices hf : ∑ n ∈ u, f n ≤
      C * (2 : ℝ) ^ B * (4 : ℝ) ^ (B - α) / ((2 : ℝ) ^ (B - α) - 1) * R ^ (B - α) by
    convert hf using 2 with n
    dsimp only [f]
    cases a n <;> rfl
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
theorem eventually_mul_rpow_le {a b C : ℝ} (hab : a < b) :
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
theorem eventually_log_mul_rpow_le {a b C : ℝ} (hab : a < b) :
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

end CKMA
