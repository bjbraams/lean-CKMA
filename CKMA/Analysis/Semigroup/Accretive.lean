/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Semigroup.Accretive.Estimates

/-!
# Crandall–Liggett semigroup

Implicit Euler products of an m-accretive resolvent converge to a nonlinear contraction
semigroup on the closure of the graph domain. Uniform convergence on bounded time
intervals holds for initial values in the graph. Source: GAPS 24.52.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Finset Function Topology
open scoped NNReal BigOperators

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- Pointwise limit of the implicit Euler products. -/
private noncomputable def accretiveSemigroup (G : Set (X × X)) (t : ℝ≥0) (x : X) : X :=
  limUnder atTop (fun n => accretiveEulerProduct G t n x)

/-- A Cauchy Euler sequence converges to the selected semigroup value. -/
private lemma accretiveSemigroup_tendsto_of_cauchy (G : Set (X × X)) (t : ℝ≥0) (x : X)
    (h : CauchySeq (fun n => accretiveEulerProduct G t n x)) :
    Tendsto (fun n => accretiveEulerProduct G t n x) atTop
      (𝓝 (accretiveSemigroup G t x)) := by
  simpa [accretiveSemigroup] using h.tendsto_limUnder

/-- Euler products from a graph point converge to the semigroup. -/
private lemma accretiveSemigroup_tendsto_domain {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    {x u : X} (hx : (x, u) ∈ G) (t : ℝ≥0) :
    Tendsto (fun n => accretiveEulerProduct G t n x) atTop
      (𝓝 (accretiveSemigroup G t x)) :=
  accretiveSemigroup_tendsto_of_cauchy G t x (accretiveEulerProduct_cauchy_domain hG hx t)

/-- The Euler defect at a graph point is at most time times the slope over the square root. -/
private lemma norm_accretiveEulerProduct_sub_semigroup {G : Set (X × X)}
    (hG : IsMAccretiveGraph G) {x u : X} (hx : (x, u) ∈ G) (n : ℕ) (t : ℝ≥0) :
    ‖accretiveEulerProduct G t n x - accretiveSemigroup G t x‖ ≤
      (t : ℝ) * ‖u‖ * Real.sqrt (1 / ((n : ℝ) + 1)) := by
  let bound (m : ℕ) : ℝ :=
    (t : ℝ) * ‖u‖ * Real.sqrt (1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1))
  have hdist : Tendsto (fun m => ‖accretiveEulerProduct G t n x - accretiveEulerProduct G t m x‖)
      atTop (𝓝 ‖accretiveEulerProduct G t n x - accretiveSemigroup G t x‖) := by
    exact (continuous_norm.tendsto _).comp
      (tendsto_const_nhds.sub (accretiveSemigroup_tendsto_domain hG hx t))
  have hbd : Tendsto bound atTop
      (𝓝 ((t : ℝ) * ‖u‖ * Real.sqrt (1 / ((n : ℝ) + 1)))) := by
    have hinv : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hsum0 : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1)) atTop
        (𝓝 (0 + (1 : ℝ) / ((n : ℝ) + 1))) := hinv.add tendsto_const_nhds
    have hsum : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1)) atTop
        (𝓝 ((1 : ℝ) / ((n : ℝ) + 1))) := by simpa [zero_add] using hsum0
    have hsq : Tendsto (fun m : ℕ => Real.sqrt (1 / ((m : ℝ) + 1) + 1 / ((n : ℝ) + 1))) atTop
        (𝓝 (Real.sqrt (1 / ((n : ℝ) + 1)))) := by
      simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto _).comp hsum
    have hmul := (tendsto_const_nhds (x := (t : ℝ) * ‖u‖)).mul hsq
    simpa only [bound] using hmul
  refine le_of_tendsto_of_tendsto hdist hbd ?_
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [norm_sub_rev]
  exact norm_accretiveEulerProduct_cross hG hx hm t

/-- On a graph point the semigroup is Lipschitz in time, with constant a graph slope. -/
private lemma norm_accretiveSemigroup_time {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    {x u : X} (hx : (x, u) ∈ G) (s t : ℝ≥0) :
    ‖accretiveSemigroup G s x - accretiveSemigroup G t x‖ ≤ |(s : ℝ) - (t : ℝ)| * ‖u‖ := by
  have hdist : Tendsto (fun n =>
      ‖accretiveEulerProduct G s n x - accretiveEulerProduct G t n x‖) atTop
      (𝓝 ‖accretiveSemigroup G s x - accretiveSemigroup G t x‖) := by
    exact (continuous_norm.tendsto _).comp
      ((accretiveSemigroup_tendsto_domain hG hx s).sub
        (accretiveSemigroup_tendsto_domain hG hx t))
  exact le_of_tendsto_of_tendsto' hdist tendsto_const_nhds
    (fun n => norm_accretiveEulerProduct_time hG hx n s t)

/-- The semigroup is the identity at time zero. -/
private lemma accretiveSemigroup_zero (G : Set (X × X)) (x : X) :
    accretiveSemigroup G 0 x = x := by
  have hcauchy : CauchySeq (fun n => accretiveEulerProduct G 0 n x) := by
    simp only [accretiveEulerProduct_zero]
    exact cauchySeq_const x
  exact tendsto_nhds_unique (accretiveSemigroup_tendsto_of_cauchy G 0 x hcauchy) <| by
    simp only [accretiveEulerProduct_zero]
    exact tendsto_const_nhds

omit [CompleteSpace X] in
/-- Euler products from the closure of the domain are Cauchy. -/
private lemma accretiveEulerProduct_cauchy_closure {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    {x : X} (hx : x ∈ closure (accretiveGraphDomain G)) (t : ℝ≥0) :
    CauchySeq (fun n => accretiveEulerProduct G t n x) := by
  by_cases ht : (t : ℝ) = 0
  · have ht0 : t = 0 := NNReal.coe_eq_zero.mp ht
    subst ht0
    simp only [accretiveEulerProduct_zero]
    exact cauchySeq_const x
  · rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 3) (by linarith)
    obtain ⟨u, hu⟩ := hy
    have hdom := accretiveEulerProduct_cauchy_domain hG hu t
    rw [Metric.cauchySeq_iff] at hdom
    obtain ⟨N, hN⟩ := hdom (ε / 3) (by linarith)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hLip : ∀ k, dist (accretiveEulerProduct G t k x) (accretiveEulerProduct G t k y) ≤
        dist x y := by
      intro k
      simpa [NNReal.coe_one, one_mul] using
        (accretiveEulerProduct_lipschitz hG t k).dist_le_mul x y
    have hmid : dist (accretiveEulerProduct G t m y) (accretiveEulerProduct G t n y) < ε / 3 :=
      hN m hm n hn
    have hsum : dist (accretiveEulerProduct G t m x) (accretiveEulerProduct G t n x) < ε := by
      have htri1 := dist_triangle (accretiveEulerProduct G t m x) (accretiveEulerProduct G t m y)
        (accretiveEulerProduct G t n x)
      have htri2 := dist_triangle (accretiveEulerProduct G t m y) (accretiveEulerProduct G t n y)
        (accretiveEulerProduct G t n x)
      have h1 := hLip m
      have h2 : dist (accretiveEulerProduct G t n y) (accretiveEulerProduct G t n x) ≤
          dist x y := by simpa [dist_comm] using hLip n
      linarith [htri1, htri2, h1, h2, hxy, hmid]
    exact hsum

/-- Euler products converge to the semigroup on the closure of the domain. -/
private lemma accretiveSemigroup_tendsto_closure {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    {x : X} (hx : x ∈ closure (accretiveGraphDomain G)) (t : ℝ≥0) :
    Tendsto (fun n => accretiveEulerProduct G t n x) atTop
      (𝓝 (accretiveSemigroup G t x)) :=
  accretiveSemigroup_tendsto_of_cauchy G t x (accretiveEulerProduct_cauchy_closure hG hx t)

/-- Each semigroup operator is a contraction on the closure of the domain. -/
private lemma norm_accretiveSemigroup_le {G : Set (X × X)} (hG : IsMAccretiveGraph G) {x y : X}
    (hx : x ∈ closure (accretiveGraphDomain G)) (hy : y ∈ closure (accretiveGraphDomain G))
    (t : ℝ≥0) : ‖accretiveSemigroup G t x - accretiveSemigroup G t y‖ ≤ ‖x - y‖ := by
  have hdist : Tendsto (fun n =>
      ‖accretiveEulerProduct G t n x - accretiveEulerProduct G t n y‖) atTop
      (𝓝 ‖accretiveSemigroup G t x - accretiveSemigroup G t y‖) := by
    exact (continuous_norm.tendsto _).comp
      ((accretiveSemigroup_tendsto_closure hG hx t).sub
        (accretiveSemigroup_tendsto_closure hG hy t))
  refine le_of_tendsto_of_tendsto' hdist tendsto_const_nhds fun n => ?_
  simpa [dist_eq_norm, NNReal.coe_one, one_mul] using
    (accretiveEulerProduct_lipschitz hG t n).dist_le_mul x y

/-- The semigroup preserves the closure of the graph domain. -/
private lemma accretiveSemigroup_mem_closure {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    {x : X} (hx : x ∈ closure (accretiveGraphDomain G)) (t : ℝ≥0) :
    accretiveSemigroup G t x ∈ closure (accretiveGraphDomain G) := by
  have hmem : ∀ n, accretiveEulerProduct G t n x ∈ closure (accretiveGraphDomain G) := by
    intro n
    by_cases ht : (t : ℝ) = 0
    · rw [NNReal.coe_eq_zero.mp ht, accretiveEulerProduct_zero]
      exact hx
    · have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne (NNReal.coe_nonneg t) (Ne.symm ht)
      rw [Metric.mem_closure_iff] at hx ⊢
      intro ε hε
      obtain ⟨y, hy, hxy⟩ := hx ε hε
      refine ⟨accretiveEulerProduct G t n y, accretiveEulerProduct_mem_domain hG ht0 n y, ?_⟩
      have hLip := (accretiveEulerProduct_lipschitz hG t n).dist_le_mul x y
      exact lt_of_le_of_lt (by simpa [dist_eq_norm, NNReal.coe_one, one_mul] using hLip) hxy
  exact isClosed_closure.mem_of_tendsto (accretiveSemigroup_tendsto_closure hG hx t)
    (Eventually.of_forall hmem)

omit [NormedSpace ℝ X] [CompleteSpace X] in
/-- The norm of a three-term sum is at most the sum of the norms. -/
private lemma norm_three_le (a b c : X) :
    ‖a + (b + c)‖ ≤ ‖a‖ + (‖b‖ + ‖c‖) := by
  exact (norm_add_le a (b + c)).trans (add_le_add_right (norm_add_le b c) ‖a‖)

omit [NormedSpace ℝ X] [CompleteSpace X] in
/-- The norm of a five-term sum is at most the sum of the norms. -/
private lemma norm_five_le (a b c d e : X) :
    ‖a + (b + (c + (d + e)))‖ ≤ ‖a‖ + (‖b‖ + (‖c‖ + (‖d‖ + ‖e‖))) := by
  refine (norm_add_le a (b + (c + (d + e)))).trans (add_le_add_right ?_ ‖a‖)
  refine (norm_add_le b (c + (d + e))).trans (add_le_add_right ?_ ‖b‖)
  refine (norm_add_le c (d + e)).trans (add_le_add_right ?_ ‖c‖)
  exact norm_add_le d e

/-- Five times a square-root reciprocal is small once the squared threshold lies below it. -/
private lemma div_sqrt_lt_five {a N ε : ℝ} (ha : 0 ≤ a) (hN : 0 < N) (hε : 0 < ε)
    (h : (5 * a / ε) ^ 2 < N) : a / Real.sqrt N < ε / 5 := by
  have hnn : 0 ≤ 5 * a / ε := div_nonneg (mul_nonneg (by norm_num) ha) hε.le
  have hlt : 5 * a / ε < Real.sqrt N := by
    have hsq := Real.sqrt_lt_sqrt (sq_nonneg _) h
    simpa [Real.sqrt_sq hnn] using hsq
  have h5 : 5 * a < ε * Real.sqrt N := by
    rw [← mul_comm (Real.sqrt N) ε]
    exact (div_lt_iff₀ hε).mp hlt
  have hdiv : a * 5 < ε * Real.sqrt N := by
    rw [mul_comm a 5]
    exact h5
  have hlt' : a < (ε * Real.sqrt N) / 5 :=
    (lt_div_iff₀ (by norm_num : (0 : ℝ) < 5)).mpr hdiv
  rw [← div_mul_eq_mul_div] at hlt'
  exact (div_lt_iff₀ (Real.sqrt_pos.mpr hN)).mpr hlt'

/-- On a graph point the orbit is continuous, with modulus a graph slope. -/
private lemma continuous_accretiveSemigroup_domain {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    {x u : X} (hx : (x, u) ∈ G) : Continuous (fun t : ℝ≥0 => accretiveSemigroup G t x) := by
  refine Metric.continuous_iff.mpr fun t₀ ε hε => ?_
  refine ⟨ε / (‖u‖ + 1), by positivity, fun s hs => ?_⟩
  rw [NNReal.dist_eq] at hs
  rw [dist_eq_norm]
  have htime := norm_accretiveSemigroup_time hG hx s t₀
  have hC : 0 < ‖u‖ + 1 := by positivity
  have hmul : |(s : ℝ) - t₀| * ‖u‖ ≤ |(s : ℝ) - t₀| * (‖u‖ + 1) := by
    gcongr
    linarith
  have hstep : |(s : ℝ) - t₀| * (‖u‖ + 1) < ε := (lt_div_iff₀ hC).mp hs
  exact lt_of_le_of_lt (htime.trans hmul) hstep

/-- The semigroup orbit is continuous on the closure of the domain. -/
private lemma continuous_accretiveSemigroup {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    {x : X} (hx : x ∈ closure (accretiveGraphDomain G)) :
    Continuous (fun t : ℝ≥0 => accretiveSemigroup G t x) := by
  refine Metric.continuous_iff.mpr fun t₀ ε hε => ?_
  obtain ⟨y, hys, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 3) (by linarith)
  have hyCl : y ∈ closure (accretiveGraphDomain G) := subset_closure hys
  obtain ⟨u, hu⟩ := hys
  have hcont := continuous_accretiveSemigroup_domain hG hu
  rw [Metric.continuous_iff] at hcont
  obtain ⟨δ, hδ, hδs⟩ := hcont t₀ (ε / 3) (by positivity)
  refine ⟨δ, hδ, fun s hs => ?_⟩
  have hsy : ‖accretiveSemigroup G s y - accretiveSemigroup G t₀ y‖ < ε / 3 := by
    simpa [dist_eq_norm] using hδs s hs
  have h1 := norm_accretiveSemigroup_le hG hx hyCl s
  have h2 := norm_accretiveSemigroup_le hG hyCl hx t₀
  have hxyN : ‖x - y‖ < ε / 3 := by simpa [dist_eq_norm] using hxy
  have hyx : ‖y - x‖ < ε / 3 := by
    rw [norm_sub_rev]
    exact hxyN
  rw [dist_eq_norm]
  set P := accretiveSemigroup G s x
  set Q := accretiveSemigroup G s y
  set R := accretiveSemigroup G t₀ y
  set T := accretiveSemigroup G t₀ x
  have hsplit : P - T = (P - Q) + ((Q - R) + (R - T)) := by abel
  have hle : ‖P - T‖ ≤ ‖P - Q‖ + (‖Q - R‖ + ‖R - T‖) := by
    simpa [← hsplit] using norm_three_le (P - Q) (Q - R) (R - T)
  have h1lt : ‖P - Q‖ < ε / 3 := lt_of_le_of_lt h1 hxyN
  have h2lt : ‖R - T‖ < ε / 3 := lt_of_le_of_lt h2 hyx
  have hsum := add_lt_add h1lt (add_lt_add hsy h2lt)
  have hεeq : ε / 3 + (ε / 3 + ε / 3) = ε := by ring
  have hlt : ‖P - T‖ < ε := by
    have := hle.trans_lt hsum
    rwa [hεeq] at this
  exact hlt

/-- The semigroup law holds for an initial value in the graph. -/
private lemma accretiveSemigroup_add_domain {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    {x u : X} (hx : (x, u) ∈ G) (s t : ℝ≥0) :
    accretiveSemigroup G (s + t) x =
      accretiveSemigroup G s (accretiveSemigroup G t x) := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [accretiveSemigroup_zero, zero_add]
  rcases eq_or_ne t 0 with rfl | ht
  · simp [accretiveSemigroup_zero, add_zero]
  have hs0 : 0 < (s : ℝ) :=
    lt_of_le_of_ne (NNReal.coe_nonneg s) ((NNReal.coe_ne_zero.mpr hs).symm)
  have ht0 : 0 < (t : ℝ) :=
    lt_of_le_of_ne (NNReal.coe_nonneg t) ((NNReal.coe_ne_zero.mpr ht).symm)
  apply sub_eq_zero.mp
  apply norm_le_zero_iff.mp
  refine le_of_forall_pos_le_add fun ε hε => ?_
  let sr : ℝ := s
  let tr : ℝ := t
  let C : ℝ := ‖u‖ + 1
  have hC : 0 < C := by positivity
  have huC : ‖u‖ ≤ C := by
    simp only [C]
    exact le_add_of_nonneg_right zero_le_one
  let K1 : ℝ := 2 * tr / sr
  let K2 : ℝ := (5 * (sr + tr) * C / ε) ^ 2
  let K3 : ℝ := 2 * sr * tr * (5 * C / ε) ^ 2
  let K : ℝ := max 1 (max K1 (max K2 K3))
  obtain ⟨N, hN⟩ := exists_nat_gt K
  have hlt {z : ℝ} (hz : z ≤ K) : z < (N : ℝ) := lt_of_le_of_lt hz hN
  have h1lt : (1 : ℝ) < N := hlt (le_max_left 1 (max K1 (max K2 K3)))
  have hNge : 1 ≤ N := by exact_mod_cast h1lt.le
  have hNpos : 0 < N := by omega
  have hK1 : K1 < (N : ℝ) :=
    hlt ((le_max_left K1 (max K2 K3)).trans (le_max_right 1 (max K1 (max K2 K3))))
  have hK2 : K2 < (N : ℝ) :=
    hlt (((le_max_left K2 K3).trans (le_max_right K1 (max K2 K3))).trans
      (le_max_right 1 (max K1 (max K2 K3))))
  have hK3 : K3 < (N : ℝ) :=
    hlt (((le_max_right K2 K3).trans (le_max_right K1 (max K2 K3))).trans
      (le_max_right 1 (max K1 (max K2 K3))))
  let h : ℝ := tr / N
  have hh : 0 < h := div_pos ht0 (by exact_mod_cast hNpos)
  have hNh : (N : ℝ) * h = tr :=
    mul_div_cancel₀ tr (by exact_mod_cast hNpos.ne')
  have ha : sr / h = sr * (N : ℝ) / tr := by
    simpa [h] using div_div_eq_mul_div (a := sr) (b := tr) (c := (N : ℝ))
  have ha2 : (2 : ℝ) < sr / h := by
    rw [ha]
    have hmul : 2 * tr < (N : ℝ) * sr := (div_lt_iff₀ hs0).mp hK1
    rw [mul_comm (N : ℝ) sr] at hmul
    exact (lt_div_iff₀ ht0).mpr hmul
  have hmain : (sr + tr) * C / Real.sqrt (N : ℝ) < ε / 5 := by
    refine div_sqrt_lt_five ?_ (by exact_mod_cast hNpos) hε ?_
    · exact mul_nonneg (add_nonneg (NNReal.coe_nonneg s) (NNReal.coe_nonneg t)) hC.le
    · convert hK2 using 1
      simp only [K2]
      ring
  have hsqrtLe : Real.sqrt (N : ℝ) ≤ (N : ℝ) :=
    (Real.sqrt_le_left (by positivity)).2 (by nlinarith [h1lt.le])
  have hstepSmall : h * C < ε / 5 := by
    have hle : h * C ≤ tr * C / Real.sqrt (N : ℝ) := by
      calc h * C = tr / (N : ℝ) * C := rfl
        _ = tr * C / (N : ℝ) := by ring
        _ ≤ tr * C / Real.sqrt (N : ℝ) :=
            div_le_div_of_nonneg_left (mul_nonneg (NNReal.coe_nonneg t) hC.le)
              (Real.sqrt_pos.mpr (by exact_mod_cast hNpos)) hsqrtLe
    have hmono : tr * C / Real.sqrt (N : ℝ) ≤ (sr + tr) * C / Real.sqrt (N : ℝ) := by
      refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (NNReal.coe_nonneg s)) hC.le
    exact lt_of_le_of_lt (hle.trans hmono) hmain
  let M : ℕ := ⌊sr / h⌋₊
  have hMgt : (sr / h) / 2 < (M : ℝ) := by
    have hfloor : sr / h < (M : ℝ) + 1 := Nat.lt_floor_add_one (sr / h)
    have hhalfLt : (sr / h) / 2 < sr / h - 1 := by linarith [ha2]
    linarith
  have hM1 : (1 : ℝ) < M := by
    have hgt1 : (1 : ℝ) < (sr / h) / 2 := by linarith [ha2]
    exact hgt1.trans hMgt
  have hMpos : 0 < M := by
    have hMge : 1 ≤ M := by exact_mod_cast hM1.le
    omega
  have hhalf : (sr / h) / 2 = sr * (N : ℝ) / (2 * tr) := by
    calc (sr / h) / 2 = (sr * (N : ℝ) / tr) / 2 := by rw [ha]
      _ = sr * (N : ℝ) / (tr * 2) := div_div _ _ _
      _ = sr * (N : ℝ) / (2 * tr) := by rw [mul_comm tr 2]
  have hdenPos : 0 < sr * (N : ℝ) / (2 * tr) := by positivity
  have hMden : sr * (N : ℝ) / (2 * tr) < (M : ℝ) := by
    rw [← hhalf]
    exact hMgt
  have hcancel : sr / (2 * tr) * K3 = (5 * sr * C / ε) ^ 2 := by
    simp only [K3]
    set X : ℝ := (5 * C / ε) ^ 2
    have hre : 2 * sr * tr * X = (2 * tr) * (sr * X) := by ring
    have htr : 2 * tr ≠ 0 := (by positivity : (0 : ℝ) < 2 * tr).ne'
    calc sr / (2 * tr) * (2 * sr * tr * X)
        = sr / (2 * tr) * ((2 * tr) * (sr * X)) := by rw [hre]
      _ = (sr / (2 * tr) * (2 * tr)) * (sr * X) := by rw [← mul_assoc]
      _ = sr * (sr * X) := by rw [div_mul_cancel₀ _ htr]
      _ = (sr * sr) * X := by rw [← mul_assoc]
      _ = (sr * (5 * C / ε)) ^ 2 := by
          rw [show X = (5 * C / ε) ^ 2 from rfl, ← sq sr, ← mul_pow]
      _ = (5 * sr * C / ε) ^ 2 := by
          congr 1
          rw [← mul_div_assoc, mul_left_comm sr 5 C, mul_assoc]
  have hsqDen : (5 * sr * C / ε) ^ 2 < sr * (N : ℝ) / (2 * tr) := by
    have hcoef : 0 < sr / (2 * tr) := by positivity
    have hmul := mul_lt_mul_of_pos_left hK3 hcoef
    rwa [hcancel, div_mul_eq_mul_div] at hmul
  have hMbound : sr * C * Real.sqrt (1 / (M : ℝ)) < ε / 5 := by
    have hinv : (1 : ℝ) / M < 1 / (sr * (N : ℝ) / (2 * tr)) :=
      (one_div_lt_one_div (by exact_mod_cast hMpos) hdenPos).mpr hMden
    have hsq := Real.sqrt_lt_sqrt (by positivity) hinv
    have hform : Real.sqrt (1 / (sr * (N : ℝ) / (2 * tr))) =
        1 / Real.sqrt (sr * (N : ℝ) / (2 * tr)) := by
      rw [one_div, Real.sqrt_inv, ← one_div]
    rw [hform] at hsq
    have hmul := mul_lt_mul_of_pos_left hsq (mul_pos hs0 hC)
    have hrew : sr * C * (1 / Real.sqrt (sr * (N : ℝ) / (2 * tr))) =
        sr * C / Real.sqrt (sr * (N : ℝ) / (2 * tr)) := by ring
    rw [hrew] at hmul
    refine hmul.trans (div_sqrt_lt_five (mul_nonneg hs0.le hC.le) hdenPos hε ?_)
    convert hsqDen using 1
    ring
  let σr : ℝ := (M : ℝ) * h
  let τr : ℝ := σr + tr
  have hσnn : 0 ≤ σr := by positivity
  have hτnn : 0 ≤ τr := by positivity
  let σ : ℝ≥0 := ⟨σr, hσnn⟩
  let τ : ℝ≥0 := ⟨τr, hτnn⟩
  have hσle : σr ≤ sr := by
    have hfl : (M : ℝ) ≤ sr / h := Nat.floor_le (div_nonneg (NNReal.coe_nonneg s) hh.le)
    calc σr = (M : ℝ) * h := rfl
      _ ≤ (sr / h) * h := mul_le_mul_of_nonneg_right hfl hh.le
      _ = sr := by field_simp
  have hgap : sr - σr < h := by
    have hlt : sr / h < (M : ℝ) + 1 := Nat.lt_floor_add_one (sr / h)
    have hmul : sr < ((M : ℝ) + 1) * h := (div_lt_iff₀ hh).mp hlt
    have hσeq : σr = (M : ℝ) * h := rfl
    linarith
  have hτeq : ((M + N : ℕ) : ℝ) * h = τr := by
    rw [Nat.cast_add, add_mul, hNh]
  let J : ℝ → X → X := accretiveResolvent G
  let y : X := (J h)^[N] x
  have hEstep {z : X} (k : ℕ) (hk : 0 < k) (r : ℝ≥0) (hr : (r : ℝ) = (k : ℝ) * h) :
      accretiveEulerProduct G r (k - 1) z = (J h)^[k] z := by
    have h1 : 1 ≤ k := by omega
    have hcount : (k - 1) + 1 = k := Nat.sub_add_cancel h1
    have hden : (r : ℝ) / (↑(k - 1) + 1) = h := by
      have hc : (↑(k - 1) : ℝ) + 1 = (k : ℝ) := by
        rw [Nat.cast_sub h1, Nat.cast_one]
        ring
      rw [hc, hr]
      exact mul_div_cancel_left₀ h (by exact_mod_cast hk.ne')
    simp only [accretiveEulerProduct, J]
    rw [hden, hcount]
  have hyE : accretiveEulerProduct G t (N - 1) x = y := by
    simpa [y] using hEstep N hNpos t hNh.symm
  obtain ⟨v, hv, hvn, _⟩ := accretiveResolvent_iterate_slope hG hh hx hNpos
  have hv' : (y, v) ∈ G := by simpa [y, J] using hv
  have hvC : ‖v‖ ≤ C := hvn.trans huC
  have hyCl : y ∈ closure (accretiveGraphDomain G) := subset_closure ⟨v, hv'⟩
  have hcomp : (J h)^[M] y = (J h)^[M + N] x := by
    simpa [y] using (iterate_add_apply (J h) M N x).symm
  have hMt : 0 < M + N := by omega
  have hEτ : accretiveEulerProduct G τ (M + N - 1) x = (J h)^[M + N] x :=
    hEstep (M + N) hMt τ hτeq.symm
  have hEσ : accretiveEulerProduct G σ (M - 1) y = (J h)^[M] y :=
    hEstep M hMpos σ rfl
  let A : X := accretiveSemigroup G (s + t) x
  let B : X := accretiveSemigroup G τ x
  let Cstep : X := (J h)^[M] y
  let Dσ : X := accretiveSemigroup G σ y
  let Es : X := accretiveSemigroup G s y
  let F : X := accretiveSemigroup G s (accretiveSemigroup G t x)
  have hAB : ‖A - B‖ < ε / 5 := by
    have htime := norm_accretiveSemigroup_time hG hx (s + t) τ
    have hdiff : ((s + t : ℝ≥0) : ℝ) - (τ : ℝ) = sr - σr := by
      rw [NNReal.coe_add]
      have hτ : (τ : ℝ) = σr + tr := rfl
      rw [hτ]
      simp only [sr, tr]
      abel
    have habs : |((s + t : ℝ≥0) : ℝ) - (τ : ℝ)| < h := by
      rw [hdiff, abs_of_nonneg (sub_nonneg.mpr hσle)]
      exact hgap
    have hle : |((s + t : ℝ≥0) : ℝ) - (τ : ℝ)| * ‖u‖ ≤
        |((s + t : ℝ≥0) : ℝ) - (τ : ℝ)| * C := by
      gcongr
    have hstrict : |((s + t : ℝ≥0) : ℝ) - (τ : ℝ)| * C < h * C :=
      mul_lt_mul_of_pos_right habs hC
    exact lt_of_le_of_lt htime (lt_of_le_of_lt hle (hstrict.trans hstepSmall))
  have hBC : ‖B - Cstep‖ < ε / 5 := by
    have hrate := norm_accretiveEulerProduct_sub_semigroup hG hx (M + N - 1) τ
    rw [hEτ, ← hcomp, norm_sub_rev] at hrate
    have hden : ((M + N - 1 : ℕ) : ℝ) + 1 = ((M + N : ℕ) : ℝ) := by
      have hone : 1 ≤ M + N := by omega
      rw [Nat.cast_sub hone, Nat.cast_one]
      ring
    have hsqle : Real.sqrt (1 / (((M + N - 1 : ℕ) : ℝ) + 1)) ≤
        Real.sqrt (1 / (N : ℝ)) := by
      refine Real.sqrt_le_sqrt ?_
      have hnum : (N : ℝ) ≤ ((M + N - 1 : ℕ) : ℝ) + 1 := by
        rw [hden]
        exact_mod_cast Nat.le_add_left N M
      exact div_le_div_of_nonneg_left zero_le_one (by exact_mod_cast hNpos) hnum
    have hτle : τr ≤ sr + tr := by
      have hσ : σr ≤ sr := hσle
      simp only [τr]
      linarith
    have hle : (τ : ℝ) * ‖u‖ * Real.sqrt (1 / (((M + N - 1 : ℕ) : ℝ) + 1)) ≤
        (sr + tr) * C / Real.sqrt (N : ℝ) := by
      have h1 : (τ : ℝ) * ‖u‖ * Real.sqrt (1 / (((M + N - 1 : ℕ) : ℝ) + 1)) ≤
          τr * ‖u‖ * Real.sqrt (1 / (N : ℝ)) := by
        rw [show (τ : ℝ) = τr by rfl]
        exact mul_le_mul_of_nonneg_left hsqle (mul_nonneg hτnn (norm_nonneg u))
      have h2 : τr * ‖u‖ * Real.sqrt (1 / (N : ℝ)) ≤
          (sr + tr) * C * Real.sqrt (1 / (N : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        exact mul_le_mul hτle huC (norm_nonneg u)
          (add_nonneg (NNReal.coe_nonneg s) (NNReal.coe_nonneg t))
      have h3 : (sr + tr) * C * Real.sqrt (1 / (N : ℝ)) =
          (sr + tr) * C / Real.sqrt (N : ℝ) := by
        rw [Real.sqrt_div zero_le_one, Real.sqrt_one, mul_one_div]
      exact h1.trans (h2.trans_eq h3)
    simpa [B, Cstep] using lt_of_le_of_lt (hrate.trans hle) hmain
  have hCD : ‖Cstep - Dσ‖ < ε / 5 := by
    have hrate := norm_accretiveEulerProduct_sub_semigroup hG hv' (M - 1) σ
    rw [hEσ] at hrate
    have hdenM : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by
      have hone : 1 ≤ M := by omega
      rw [Nat.cast_sub hone, Nat.cast_one]
      ring
    have hle : (σ : ℝ) * ‖v‖ * Real.sqrt (1 / (((M - 1 : ℕ) : ℝ) + 1)) ≤
        sr * C * Real.sqrt (1 / (M : ℝ)) := by
      rw [show (σ : ℝ) = σr by rfl, hdenM]
      refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
      exact mul_le_mul hσle hvC (norm_nonneg v) (NNReal.coe_nonneg s)
    simpa [Cstep, Dσ] using lt_of_le_of_lt (hrate.trans hle) hMbound
  have hDE : ‖Dσ - Es‖ < ε / 5 := by
    have htime := norm_accretiveSemigroup_time hG hv' σ s
    have habs : |(σ : ℝ) - (s : ℝ)| < h := by
      rw [show (σ : ℝ) = σr by rfl, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hσle)]
      exact hgap
    have hle : |(σ : ℝ) - (s : ℝ)| * ‖v‖ ≤ |(σ : ℝ) - (s : ℝ)| * C := by
      gcongr
    have hstrict : |(σ : ℝ) - (s : ℝ)| * C < h * C := mul_lt_mul_of_pos_right habs hC
    simpa [Dσ, Es] using
      lt_of_le_of_lt htime (lt_of_le_of_lt hle (hstrict.trans hstepSmall))
  have hEF : ‖Es - F‖ < ε / 5 := by
    have hyS : accretiveSemigroup G t x ∈ closure (accretiveGraphDomain G) :=
      accretiveSemigroup_mem_closure hG (subset_closure ⟨u, hx⟩) t
    have hcont := norm_accretiveSemigroup_le hG hyCl hyS s
    have hrate := norm_accretiveEulerProduct_sub_semigroup hG hx (N - 1) t
    rw [hyE] at hrate
    have hdenN : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
      rw [Nat.cast_sub hNge, Nat.cast_one]
      ring
    have hle : (t : ℝ) * ‖u‖ * Real.sqrt (1 / (((N - 1 : ℕ) : ℝ) + 1)) ≤
        (sr + tr) * C / Real.sqrt (N : ℝ) := by
      rw [hdenN, show (t : ℝ) = tr by rfl]
      have h1 : tr * ‖u‖ ≤ tr * C :=
        mul_le_mul_of_nonneg_left huC (NNReal.coe_nonneg t)
      have h2 : tr * ‖u‖ * Real.sqrt (1 / (N : ℝ)) ≤
          tr * C * Real.sqrt (1 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
      have h3 : tr * C * Real.sqrt (1 / (N : ℝ)) ≤
          (sr + tr) * C * Real.sqrt (1 / (N : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (NNReal.coe_nonneg s)) hC.le
      have h4 : (sr + tr) * C * Real.sqrt (1 / (N : ℝ)) =
          (sr + tr) * C / Real.sqrt (N : ℝ) := by
        rw [Real.sqrt_div zero_le_one, Real.sqrt_one, mul_one_div]
      exact h2.trans (h3.trans_eq h4)
    simpa [Es, F] using lt_of_le_of_lt (hcont.trans (hrate.trans hle)) hmain
  have hsplit : A - F =
      (A - B) + ((B - Cstep) + ((Cstep - Dσ) + ((Dσ - Es) + (Es - F)))) := by abel
  have hle : ‖A - F‖ ≤
      ‖A - B‖ + (‖B - Cstep‖ + (‖Cstep - Dσ‖ + (‖Dσ - Es‖ + ‖Es - F‖))) := by
    simpa [← hsplit] using norm_five_le (A - B) (B - Cstep) (Cstep - Dσ) (Dσ - Es) (Es - F)
  have hsum := add_lt_add hAB (add_lt_add hBC (add_lt_add hCD (add_lt_add hDE hEF)))
  have hεeq : ε / 5 + (ε / 5 + (ε / 5 + (ε / 5 + ε / 5))) = ε := by ring
  have hlt : ‖A - F‖ < ε := by
    have := hle.trans_lt hsum
    rwa [hεeq] at this
  simpa [A, F, zero_add] using hlt.le

/-- The semigroup law extends from the graph domain to its closure. -/
private lemma accretiveSemigroup_add_closure {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    {x : X} (hx : x ∈ closure (accretiveGraphDomain G)) (s t : ℝ≥0) :
    accretiveSemigroup G (s + t) x =
      accretiveSemigroup G s (accretiveSemigroup G t x) := by
  apply sub_eq_zero.mp
  apply norm_le_zero_iff.mp
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨y, hys, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (by linarith)
  have hyCl : y ∈ closure (accretiveGraphDomain G) := subset_closure hys
  obtain ⟨u, hu⟩ := hys
  have hdom := accretiveSemigroup_add_domain hG hu s t
  have hSty := accretiveSemigroup_mem_closure hG hyCl t
  have hStx := accretiveSemigroup_mem_closure hG hx t
  have hAB := norm_accretiveSemigroup_le hG hx hyCl (s + t)
  have hCD := (norm_accretiveSemigroup_le hG hSty hStx s).trans
    (norm_accretiveSemigroup_le hG hyCl hx t)
  have hxyN : ‖x - y‖ < ε / 2 := by simpa [dist_eq_norm] using hxy
  have hyx : ‖y - x‖ < ε / 2 := by
    rw [norm_sub_rev]
    exact hxyN
  set A := accretiveSemigroup G (s + t) x
  set B := accretiveSemigroup G (s + t) y
  set D := accretiveSemigroup G s (accretiveSemigroup G t x)
  have hmid : B = accretiveSemigroup G s (accretiveSemigroup G t y) := hdom
  have hsplit : A - D =
      (A - B) + (accretiveSemigroup G s (accretiveSemigroup G t y) - D) := by
    rw [← hmid]
    abel
  have hle : ‖A - D‖ ≤ ‖A - B‖ +
      ‖accretiveSemigroup G s (accretiveSemigroup G t y) - D‖ := by
    simpa [← hsplit] using norm_add_le (A - B)
      (accretiveSemigroup G s (accretiveSemigroup G t y) - D)
  have hABlt : ‖A - B‖ < ε / 2 := lt_of_le_of_lt hAB hxyN
  have hCDlt : ‖accretiveSemigroup G s (accretiveSemigroup G t y) - D‖ < ε / 2 :=
    lt_of_le_of_lt hCD hyx
  have hsum := add_lt_add hABlt hCDlt
  have hεeq : ε / 2 + ε / 2 = ε := by ring
  have hlt : ‖A - D‖ < ε := by
    have := hle.trans_lt hsum
    rwa [hεeq] at this
  simpa [A, D, zero_add] using hlt.le

/-- Euler products converge to the semigroup uniformly for bounded time on the domain. -/
private lemma accretiveEulerProduct_uniform {G : Set (X × X)} (hG : IsMAccretiveGraph G)
    {x u : X} (hx : (x, u) ∈ G) (R : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ R →
      ‖accretiveEulerProduct G t n x - accretiveSemigroup G t x‖ < ε := by
  have hlim : Tendsto (fun n : ℕ => (R : ℝ) * ‖u‖ * Real.sqrt (1 / ((n : ℝ) + 1))) atTop
      (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hsq : Tendsto (fun n : ℕ => Real.sqrt (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa [Function.comp_def, Real.sqrt_zero] using
        (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hinv
    simpa [mul_zero] using (tendsto_const_nhds (x := (R : ℝ) * ‖u‖)).mul hsq
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N, hN⟩ := hlim ε hε
  refine (eventually_ge_atTop N).mono fun n hn t ht => ?_
  have hrate := norm_accretiveEulerProduct_sub_semigroup hG hx n t
  have hle : (t : ℝ) * ‖u‖ * Real.sqrt (1 / ((n : ℝ) + 1)) ≤
      (R : ℝ) * ‖u‖ * Real.sqrt (1 / ((n : ℝ) + 1)) := by
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    exact mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr ht) (norm_nonneg u)
  have hsmall := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hsmall
  exact lt_of_le_of_lt (hrate.trans hle) hsmall

/-- **24.52**, Crandall–Liggett: implicit Euler products generate a nonlinear contraction
semigroup on the closure of the graph domain. Uniform time convergence is asserted on the domain,
and pointwise convergence is asserted for every initial value in its closure. -/
theorem crandall_liggett {G : Set (X × X)} (hG : IsMAccretiveGraph G) :
    ∃ S : ℝ≥0 → X → X,
      (∀ t, Set.MapsTo (S t) (closure (accretiveGraphDomain G)) (closure (accretiveGraphDomain G)))
        ∧
      (∀ x ∈ closure (accretiveGraphDomain G), S 0 x = x) ∧
      (∀ s t x, x ∈ closure (accretiveGraphDomain G) → S (s + t) x = S s (S t x)) ∧
      (∀ t x y, x ∈ closure (accretiveGraphDomain G) → y ∈ closure (accretiveGraphDomain G) →
        ‖S t x - S t y‖ ≤ ‖x - y‖) ∧
      (∀ x ∈ closure (accretiveGraphDomain G), Continuous (fun t ↦ S t x)) ∧
      (∀ x ∈ closure (accretiveGraphDomain G), ∀ t, Tendsto
        (fun n ↦ accretiveEulerProduct G t n x) atTop (𝓝 (S t x))) ∧
      ∀ x ∈ accretiveGraphDomain G, ∀ R : ℝ≥0, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ R → ‖accretiveEulerProduct G t n x - S t x‖ < ε := by
  refine ⟨accretiveSemigroup G, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t x hx
    exact accretiveSemigroup_mem_closure hG hx t
  · intro x _
    exact accretiveSemigroup_zero G x
  · intro s t x hx
    exact accretiveSemigroup_add_closure hG hx s t
  · intro t x y hx hy
    exact norm_accretiveSemigroup_le hG hx hy t
  · intro x hx
    exact continuous_accretiveSemigroup hG hx
  · intro x hx t
    exact accretiveSemigroup_tendsto_closure hG hx t
  · intro x hx R ε hε
    obtain ⟨u, hu⟩ := hx
    exact accretiveEulerProduct_uniform hG hu R hε

end CKMA
