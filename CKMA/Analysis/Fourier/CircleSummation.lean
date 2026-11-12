/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Data.Int.Interval
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Fourier summation on the probability circle

Symmetric Fourier partial sums, Fejer means and the Fejer kernel use Mathlib's
circle characters, Fourier coefficients and normalized Haar measure. Convergence of
those means is proved in `CKMA.Analysis.Fourier.CircleConvergence`. The
Carleson–Hunt interface combines maximal control with almost-everywhere convergence
of ordinary partial sums for `p > 1`.

Sources: GAPS 27.17 and 27.22.
-/

@[expose] public section

noncomputable section

namespace CKMA

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal Real ComplexConjugate

local instance : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩

local notation "𝕋" => AddCircle (1 : ℝ)

local notation "haar" => AddCircle.haarAddCircle (T := 1)

/-- Symmetric Fourier partial sums on the probability circle. -/
def fourierPartialSum (f : AddCircle (1 : ℝ) → ℂ) (N : ℕ)
    (x : AddCircle (1 : ℝ)) : ℂ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff f k * fourier k x

/-- Fejer's Cesaro averages of the symmetric partial sums. -/
def fejerMean (f : AddCircle (1 : ℝ) → ℂ) (N : ℕ) (x : AddCircle (1 : ℝ)) : ℂ :=
  (N + 1 : ℂ)⁻¹ * ∑ n ∈ Finset.range (N + 1), fourierPartialSum f n x

/-- The positive Carleson maximal function, retaining infinite suprema. -/
def carlesonMaximalFunction (f : AddCircle (1 : ℝ) → ℂ) (x : AddCircle (1 : ℝ)) : ℝ≥0∞ :=
  ⨆ N : ℕ, ENNReal.ofReal ‖fourierPartialSum f N x‖

/-- A Lebesgue point on the circle, defined through local lifted averages. -/
def IsCircleLebesguePoint (f : AddCircle (1 : ℝ) → ℂ) (x : AddCircle (1 : ℝ)) : Prop :=
  Tendsto (fun r : ℝ ↦ (2 * r)⁻¹ * ∫ t in (-r)..r,
    ‖f (x + (t : AddCircle (1 : ℝ))) - f x‖) (𝓝[>] 0) (𝓝 0)

/-- The zero function has zero symmetric Fourier partial sums. -/
@[simp]
theorem fourierPartialSum_zero (N : ℕ) : fourierPartialSum (fun _ ↦ 0) N = 0 := by
  funext x
  simp [fourierPartialSum, fourierCoeff]

/-! ### Characters, Cesaro weights and the Fejer kernel -/

/-- Membership in the symmetric integer interval is a bound on the absolute value. -/
private lemma mem_Icc_iff_natAbs_le (n : ℕ) (k : ℤ) :
    k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) ↔ k.natAbs ≤ n := by
  rw [Finset.mem_Icc, ← abs_le, ← Int.natCast_natAbs, Nat.cast_le]

/-- A symmetric partial sum is the central window of a longer symmetric sum. -/
private lemma sum_Icc_eq_filter (N n : ℕ) (hn : n ≤ N) (c : ℤ → ℂ) :
    ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), c k =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), if k.natAbs ≤ n then c k else 0 := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_subset ?_ ?_
  · intro k hk
    rw [Finset.mem_filter, mem_Icc_iff_natAbs_le]
    exact ⟨(mem_Icc_iff_natAbs_le n k).1 hk |>.trans hn, (mem_Icc_iff_natAbs_le n k).1 hk⟩
  · intro k hk hk'
    rw [Finset.mem_filter] at hk
    exact absurd ((mem_Icc_iff_natAbs_le n k).2 hk.2) hk'

/-- Cesaro summation counts how many symmetric windows contain each frequency. -/
private lemma sum_cesaro (N : ℕ) (c : ℤ → ℂ) :
    ∑ n ∈ Finset.range (N + 1), ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), c k =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ((N + 1 - k.natAbs : ℕ) : ℂ) * c k := by
  classical
  rw [Finset.sum_congr rfl fun n hn =>
    sum_Icc_eq_filter N n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)) c]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← Finset.sum_filter]
  have hfilt : Finset.filter (fun n => k.natAbs ≤ n) (Finset.range (N + 1)) =
      Finset.Icc k.natAbs N := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    exact ⟨fun h => ⟨h.2, Nat.lt_succ_iff.mp h.1⟩, fun h => ⟨Nat.lt_succ_iff.mpr h.2, h.1⟩⟩
  rw [hfilt, Finset.sum_const, nsmul_eq_mul]
  congr 1
  rw [Nat.card_Icc]

/-- The normalized window count is the Fejer weight `1 - |k|/(N+1)`. -/
private lemma weight_div (N m : ℕ) (hm : m ≤ N) :
    ((N + 1 - m : ℕ) : ℂ) / (N + 1) = 1 - (m : ℂ) / (N + 1) := by
  have hm' : m ≤ N + 1 := hm.trans (Nat.le_succ N)
  have hN : (N + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  rw [Nat.cast_sub hm', Nat.cast_add, Nat.cast_one, sub_div, div_self hN]

/-- Fejer means are the symmetric trigonometric sums with weights `1 - |k|/(N+1)`. -/
lemma fejerMean_eq_weighted (f : 𝕋 → ℂ) (N : ℕ) (x : 𝕋) :
    fejerMean f N x =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (1 - (k.natAbs : ℂ) / (N + 1)) * fourierCoeff f k * fourier k x := by
  unfold fejerMean fourierPartialSum
  rw [sum_cesaro, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkN : k.natAbs ≤ N := (mem_Icc_iff_natAbs_le N k).1 hk
  have hN : (N + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  rw [← mul_assoc, ← div_eq_inv_mul, weight_div N k.natAbs hkN, mul_assoc]

/-- Characters multiply when their arguments are added. -/
private lemma fourier_add_right (k : ℤ) (x y : 𝕋) :
    fourier k (x + y) = fourier k x * fourier k y := by
  rw [fourier_apply, fourier_apply, fourier_apply, zsmul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

/-- Negating the argument negates the frequency. -/
private lemma fourier_neg_right (k : ℤ) (t : 𝕋) :
    fourier k (-t) = fourier (-k) t := by
  rw [fourier_apply, fourier_apply, smul_neg, neg_zsmul]

/-- A character of a difference factors through the two summands. -/
private lemma fourier_sub_right (k : ℤ) (x t : 𝕋) :
    fourier k (x - t) = fourier k x * fourier (-k) t := by
  rw [sub_eq_add_neg, fourier_add_right, fourier_neg_right]

/-- Integer powers of the fundamental character are the integer frequencies. -/
private lemma fourier_coe_pow (j : ℕ) (t : ℝ) :
    fourier (j : ℤ) (t : 𝕋) = Complex.exp (2 * π * Complex.I * t) ^ j := by
  rw [fourier_coe_apply (T := 1), Complex.ofReal_one, div_one, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `sin(πt)` vanishes exactly at the integers. -/
private lemma sin_pi_eq_zero_iff_int (t : ℝ) :
    Real.sin (π * t) = 0 ↔ ∃ n : ℤ, t = n := by
  rw [Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, mul_right_cancel₀ Real.pi_ne_zero (by linarith)⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩

/-- The fundamental character is trivial exactly on the integers. -/
private lemma exp_two_pi_eq_one_iff (t : ℝ) :
    Complex.exp (2 * π * Complex.I * t) = 1 ↔ ∃ n : ℤ, t = n := by
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hc : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hmul : (2 * π * Complex.I) * (t : ℂ) = (2 * π * Complex.I) * (n : ℂ) := by
      calc
        (2 * π * Complex.I) * (t : ℂ) = 2 * π * Complex.I * (t : ℂ) := by ring
        _ = n * (2 * π * Complex.I) := hn
        _ = (2 * π * Complex.I) * (n : ℂ) := by ring
    exact ⟨n, by exact_mod_cast mul_left_cancel₀ hc hmul⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

/-- Pairs in `0..N` with a fixed difference `k` are counted by `N + 1 - |k|`. -/
private lemma card_sub_fiber (N : ℕ) {k : ℤ} (hk : k.natAbs ≤ N) :
    ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
        fun p : ℕ × ℕ => Int.subNatNat p.1 p.2 = k).card = N + 1 - k.natAbs := by
  classical
  let a := k.natAbs
  let dom := Finset.range (N + 1 - a)
  rcases le_or_gt 0 k with hk0 | hk0
  · have hkcast : (a : ℤ) = k := Int.natAbs_of_nonneg hk0
    let ι : ℕ → ℕ × ℕ := fun m => (m + a, m)
    have hinj : Set.InjOn ι dom := fun _ _ _ _ h => congrArg Prod.snd h
    have him : dom.image ι =
        (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
          fun p : ℕ × ℕ => Int.subNatNat p.1 p.2 = k := by
      ext ⟨j, m⟩
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range, ι, dom]
      constructor
      · rintro ⟨m', hm', heq⟩
        obtain ⟨hja, hmm⟩ := Prod.ext_iff.mp heq
        subst hja
        subst hmm
        exact ⟨⟨by omega, by omega⟩, by
          rw [Int.subNatNat_eq_coe, Nat.cast_add, hkcast]; ring⟩
      · rintro ⟨⟨hj, hm⟩, hsub⟩
        rw [Int.subNatNat_eq_coe] at hsub
        have hjN : j = m + a := by
          rw [← hkcast] at hsub
          exact_mod_cast (sub_eq_iff_eq_add.mp hsub).trans (add_comm (a : ℤ) _)
        refine ⟨m, ?_, Prod.ext hjN.symm rfl⟩
        omega
    rw [← him, Finset.card_image_of_injOn hinj, Finset.card_range]
  · have hkcast : (a : ℤ) = -k := by
      have hnat : a = (-k).natAbs := (Int.natAbs_neg k).symm
      rw [hnat]
      exact Int.natAbs_of_nonneg (neg_nonneg.mpr hk0.le)
    let ι : ℕ → ℕ × ℕ := fun m => (m, m + a)
    have hinj : Set.InjOn ι dom := fun _ _ _ _ h => congrArg Prod.fst h
    have him : dom.image ι =
        (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
          fun p : ℕ × ℕ => Int.subNatNat p.1 p.2 = k := by
      ext ⟨j, m⟩
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range, ι, dom]
      constructor
      · rintro ⟨j', hj', heq⟩
        obtain ⟨hjj, hma⟩ := Prod.ext_iff.mp heq
        subst hjj
        subst hma
        exact ⟨⟨by omega, by omega⟩, by
          rw [Int.subNatNat_eq_coe, Nat.cast_add, hkcast]; ring⟩
      · rintro ⟨⟨hj, hm⟩, hsub⟩
        rw [Int.subNatNat_eq_coe] at hsub
        have hmN : m = j + a := by
          have hneg : (m : ℤ) - (j : ℤ) = a := by
            rw [← neg_sub (j : ℤ) (m : ℤ), hsub]
            exact hkcast.symm
          exact_mod_cast (sub_eq_iff_eq_add.mp hneg).trans (add_comm (a : ℤ) _)
        refine ⟨j, ?_, Prod.ext rfl hmN.symm⟩
        omega
    rw [← him, Finset.card_image_of_injOn hinj, Finset.card_range]

/-- The square of a partial character sum expands into Fejer weights. -/
private lemma normSq_fourierSum (N : ℕ) (x : 𝕋) :
    (‖∑ j ∈ Finset.range (N + 1), fourier (j : ℤ) x‖ ^ 2 : ℂ) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ((N + 1 - k.natAbs : ℕ) : ℂ) * fourier k x := by
  classical
  set s := Finset.range (N + 1)
  set z := ∑ j ∈ s, fourier (j : ℤ) x
  rw [← Complex.mul_conj']
  have hconj : conj z = ∑ m ∈ s, fourier (-(m : ℤ)) x := by
    simp only [z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact (fourier_neg).symm
  rw [hconj, Finset.sum_mul_sum]
  have hterm : ∀ j m : ℕ, fourier (j : ℤ) x * fourier (-(m : ℤ)) x =
      fourier ((j : ℤ) - (m : ℤ)) x := fun j m =>
    ((fourier_add (m := (j : ℤ)) (n := -(m : ℤ)) (x := x)).symm).trans
      (congr_arg (fun n : ℤ => fourier n x) (sub_eq_add_neg (j : ℤ) (m : ℤ)).symm)
  simp_rw [hterm]
  rw [← Finset.sum_product']
  have hmap : ∀ p ∈ s ×ˢ s, (p.1 : ℤ) - (p.2 : ℤ) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro p hp
    simp only [s, Finset.mem_product, Finset.mem_range] at hp
    rw [mem_Icc_iff_natAbs_le, ← Nat.cast_le (α := ℤ), Int.natCast_natAbs, abs_le]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to' hmap fun k => fourier k x]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  norm_cast
  exact card_sub_fiber N ((mem_Icc_iff_natAbs_le N k).1 hk)

/-- The Fejer kernel on the probability circle, as a normalized square of characters. -/
def fejerKernel (N : ℕ) (x : 𝕋) : ℝ :=
  (N + 1 : ℝ)⁻¹ * ‖∑ j ∈ Finset.range (N + 1), fourier (j : ℤ) x‖ ^ 2

/-- The Fejer kernel is a weighted sum of characters. -/
private lemma fejerKernel_eq_sum (N : ℕ) (x : 𝕋) :
    (fejerKernel N x : ℂ) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (1 - (k.natAbs : ℂ) / (N + 1)) * fourier k x := by
  unfold fejerKernel
  rw [Complex.ofReal_mul, Complex.ofReal_pow, normSq_fourierSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkN : k.natAbs ≤ N := (mem_Icc_iff_natAbs_le N k).1 hk
  rw [Complex.ofReal_inv, ← mul_assoc]
  push_cast
  rw [← div_eq_inv_mul, weight_div N k.natAbs hkN]

/-- The Fejer kernel is nonnegative. -/
lemma fejerKernel_nonneg (N : ℕ) (x : 𝕋) : 0 ≤ fejerKernel N x := by
  unfold fejerKernel
  positivity

/-- The Fejer kernel is continuous. -/
lemma continuous_fejerKernel (N : ℕ) : Continuous (fejerKernel N) := by
  unfold fejerKernel
  refine continuous_const.mul ?_
  exact (continuous_pow 2).comp
    ((continuous_finsetSum (Finset.range (N + 1))
      (fun j _ => map_continuous (fourier (j : ℤ)))).norm)

/-- The Fejer kernel is even. -/
lemma fejerKernel_neg (N : ℕ) (x : 𝕋) : fejerKernel N (-x) = fejerKernel N x := by
  unfold fejerKernel
  congr 1
  have hsum : ∑ j ∈ Finset.range (N + 1), fourier (j : ℤ) (-x) =
      conj (∑ j ∈ Finset.range (N + 1), fourier (j : ℤ) x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [fourier_neg_right, ← fourier_neg]
  rw [hsum, Complex.norm_conj]

/-- The Fejer kernel is bounded by its central value `N + 1`. -/
lemma fejerKernel_le_succ (N : ℕ) (x : 𝕋) : fejerKernel N x ≤ (N + 1 : ℝ) := by
  unfold fejerKernel
  have hsum : ‖∑ j ∈ Finset.range (N + 1), fourier (j : ℤ) x‖ ≤ (N + 1 : ℝ) := by
    calc
      ‖∑ j ∈ Finset.range (N + 1), fourier (j : ℤ) x‖
          ≤ ∑ j ∈ Finset.range (N + 1), ‖fourier (j : ℤ) x‖ := norm_sum_le _ _
      _ = ∑ _ ∈ Finset.range (N + 1), (1 : ℝ) := by simp [fourier_apply]
      _ = (N + 1 : ℝ) := by simp [Finset.sum_const, Finset.card_range]
  have hsq : ‖∑ j ∈ Finset.range (N + 1), fourier (j : ℤ) x‖ ^ 2 ≤ (N + 1 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hsum 2
  calc
    (N + 1 : ℝ)⁻¹ * ‖∑ j ∈ Finset.range (N + 1), fourier (j : ℤ) x‖ ^ 2
        ≤ (N + 1 : ℝ)⁻¹ * (N + 1 : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr (by positivity))
    _ = (N + 1 : ℝ) := by field_simp

/-- Every circle point has a representative in `[-1/2, 1/2]` of the same norm. -/
private lemma exists_coe_norm (x : 𝕋) :
    ∃ u : ℝ, |u| ≤ 1 / 2 ∧ (u : 𝕋) = x ∧ ‖x‖ = |u| := by
  refine QuotientAddGroup.induction_on x ?_
  intro t
  let u := t - round t
  have hu : |u| ≤ 1 / 2 := abs_sub_round t
  have hcoe : (u : 𝕋) = (t : 𝕋) := by
    rw [AddCircle.coe_sub]
    have h0 : (((round t : ℤ) : ℝ) : 𝕋) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨round t, by simp⟩
    simp [h0]
  have hhalf : |u| ≤ |1| / 2 := by simpa [abs_one] using hu
  have hnorm : ‖(t : 𝕋)‖ = |u| := by
    rw [← hcoe]
    exact (AddCircle.norm_coe_eq_abs_iff (p := 1) one_ne_zero).2 hhalf
  exact ⟨u, hu, hcoe, hnorm⟩

/-- The classical sine-square formula of the Fejer kernel, with value `N+1` at integers. -/
def fejerKernelReal (N : ℕ) (t : ℝ) : ℝ :=
  if Real.sin (π * t) = 0 then (N + 1 : ℝ)
  else (N + 1 : ℝ)⁻¹ * (Real.sin (π * (N + 1) * t) / Real.sin (π * t)) ^ 2

/-- On the line, the character square agrees with the sine-square formula. -/
lemma fejerKernelReal_eq (N : ℕ) (t : ℝ) :
    fejerKernelReal N t = fejerKernel N (t : 𝕋) := by
  unfold fejerKernelReal fejerKernel
  by_cases hsin : Real.sin (π * t) = 0
  · rw [ite_eq_left hsin]
    rcases (sin_pi_eq_zero_iff_int t).1 hsin with ⟨n, rfl⟩
    have ht0 : ((n : ℝ) : 𝕋) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨n, by simp⟩
    simp only [ht0, fourier_eval_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one, Complex.norm_natCast]
    field_simp
    push_cast
    ring
  · rw [ite_eq_right hsin]
    set w : ℂ := Complex.exp (2 * π * Complex.I * t)
    have hwne : w ≠ 1 := by
      intro hw
      exact hsin ((sin_pi_eq_zero_iff_int t).2 ((exp_two_pi_eq_one_iff t).1 hw))
    have hpow : ∀ j : ℕ, fourier (j : ℤ) (t : 𝕋) = w ^ j := fun j => fourier_coe_pow j t
    have hgeom : ∑ j ∈ Finset.range (N + 1), w ^ j = (w ^ (N + 1) - 1) / (w - 1) :=
      geom_sum_eq hwne (N + 1)
    have hsum : ∑ j ∈ Finset.range (N + 1), fourier (j : ℤ) (t : 𝕋) =
        (w ^ (N + 1) - 1) / (w - 1) := by
      simp_rw [hpow, hgeom]
    have hwI : w = Complex.exp (Complex.I * ↑(2 * π * t)) := by
      unfold w
      congr 1
      push_cast
      ring
    have hden : ‖w - 1‖ = 2 * |Real.sin (π * t)| := by
      rw [hwI, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    have hwpow : w ^ (N + 1) =
        Complex.exp (Complex.I * ↑(2 * π * (N + 1) * t)) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hnum : ‖w ^ (N + 1) - 1‖ = 2 * |Real.sin (π * (N + 1) * t)| := by
      rw [hwpow, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    have hnorm : ‖∑ j ∈ Finset.range (N + 1), fourier (j : ℤ) (t : 𝕋)‖ =
        |Real.sin (π * (N + 1) * t)| / |Real.sin (π * t)| := by
      rw [hsum, norm_div, hnum, hden]
      have hsin' : |Real.sin (π * t)| ≠ 0 := by
        simp [hsin, abs_eq_zero]
      field_simp
    rw [hnorm]
    have hsq : (|Real.sin (π * (N + 1) * t)| / |Real.sin (π * t)|) ^ 2 =
        (Real.sin (π * (N + 1) * t) / Real.sin (π * t)) ^ 2 := by
      rw [div_pow, div_pow, sq_abs, sq_abs]
    rw [hsq]

/-- The real Fejer kernel is nonnegative. -/
lemma fejerKernelReal_nonneg (N : ℕ) (t : ℝ) : 0 ≤ fejerKernelReal N t := by
  rw [fejerKernelReal_eq]
  exact fejerKernel_nonneg N _

/-- The real Fejer kernel is continuous. -/
lemma continuous_fejerKernelReal (N : ℕ) : Continuous (fejerKernelReal N) := by
  have hfun : fejerKernelReal N = (fun t : ℝ => fejerKernel N (t : 𝕋)) := by
    ext t
    exact fejerKernelReal_eq N t
  rw [hfun]
  exact (continuous_fejerKernel N).comp continuous_quotient_mk'

/-- The real Fejer kernel is even. -/
lemma fejerKernelReal_neg (N : ℕ) (t : ℝ) :
    fejerKernelReal N (-t) = fejerKernelReal N t := by
  rw [fejerKernelReal_eq, fejerKernelReal_eq, AddCircle.coe_neg, fejerKernel_neg]

/-- The real Fejer kernel is at most `N + 1`. -/
lemma fejerKernelReal_le_succ (N : ℕ) (t : ℝ) :
    fejerKernelReal N t ≤ N + 1 := by
  rw [fejerKernelReal_eq]
  exact fejerKernel_le_succ N _

/-- On `[-1/2, 1/2]`, `|sin(πt)|` is at least `2|t|`. -/
private lemma abs_sin_pi_ge_two_mul {t : ℝ} (ht : |t| ≤ 1 / 2) :
    2 * |t| ≤ |Real.sin (π * t)| := by
  have habs : |π * t| ≤ π := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos, ht, abs_nonneg t]
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi habs, abs_mul, abs_of_pos Real.pi_pos]
  have h0 : 0 ≤ π * |t| := by positivity
  have hle : π * |t| ≤ π / 2 := by nlinarith [Real.pi_pos, ht]
  have hmul := Real.mul_le_sin h0 hle
  have hcalc : 2 / π * (π * |t|) = 2 * |t| := by field_simp
  linarith

/-- Off the integers, the Fejer kernel is bounded by `1/(4(N+1)t²)`. -/
lemma fejerKernelReal_le_inv_sq {N : ℕ} {t : ℝ} (ht0 : t ≠ 0) (ht : |t| ≤ 1 / 2) :
    fejerKernelReal N t ≤ 1 / (4 * (N + 1) * t ^ 2) := by
  have hsin : Real.sin (π * t) ≠ 0 := by
    intro h
    rcases (sin_pi_eq_zero_iff_int t).1 h with ⟨n, rfl⟩
    have habs : |(n : ℝ)| ≤ 1 / 2 := ht
    have hn : n = 0 := by
      rcases lt_trichotomy n 0 with hn | rfl | hn
      · have hle : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hn
        linarith [abs_le.mp habs]
      · rfl
      · have hle : (1 : ℝ) ≤ n := by exact_mod_cast Int.add_one_le_of_lt hn
        linarith [abs_le.mp habs]
    exact ht0 (by simp [hn])
  unfold fejerKernelReal
  rw [ite_eq_right hsin]
  have hden : 2 * |t| ≤ |Real.sin (π * t)| := abs_sin_pi_ge_two_mul ht
  have hden0 : 0 < |Real.sin (π * t)| := lt_of_lt_of_le (by positivity : 0 < 2 * |t|) hden
  have hnum : |Real.sin (π * (N + 1) * t)| ≤ 1 :=
    Real.abs_sin_le_one (π * (N + 1) * t)
  have hratio : |Real.sin (π * (N + 1) * t)| / |Real.sin (π * t)| ≤ 1 / (2 * |t|) := by
    rw [div_le_div_iff₀ hden0 (by positivity)]
    calc
      |Real.sin (π * (N + 1) * t)| * (2 * |t|) ≤ 1 * (2 * |t|) :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
      _ = 2 * |t| := by ring
      _ ≤ |Real.sin (π * t)| := hden
      _ = 1 * |Real.sin (π * t)| := by ring
  have hsq : (Real.sin (π * (N + 1) * t) / Real.sin (π * t)) ^ 2 ≤
      (1 / (2 * |t|)) ^ 2 := by
    have hpow := pow_le_pow_left₀ (by positivity) hratio 2
    simpa [div_pow, sq_abs] using hpow
  calc
    (N + 1 : ℝ)⁻¹ * (Real.sin (π * (N + 1) * t) / Real.sin (π * t)) ^ 2
        ≤ (N + 1 : ℝ)⁻¹ * (1 / (2 * |t|)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr (by positivity))
    _ = 1 / (4 * (N + 1) * t ^ 2) := by
      rw [div_pow, one_pow, mul_pow, sq_abs]
      field_simp
      ring

/-- A continuous scalar function on the circle is integrable for probability Haar measure. -/
lemma integrable_of_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : 𝕋 → E} (hg : Continuous g) : Integrable g haar :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)

/-- Each character is integrable. -/
private lemma integrable_fourier (k : ℤ) : Integrable (fun x : 𝕋 => fourier k x) haar :=
  integrable_of_continuous (map_continuous (fourier k))

/-- Character integrals vanish except for the constant character, which has mass one. -/
private lemma integral_fourier (k : ℤ) :
    ∫ x : 𝕋, fourier k x ∂haar = if k = 0 then (1 : ℂ) else 0 := by
  split_ifs with hk
  · simp [hk, integral_const, Measure.real, measure_univ]
  · exact integral_eq_zero_of_add_right_eq_neg (μ := haar)
      (fun x => fourier_add_half_inv_index hk one_pos x)

/-- The Fejer kernel has integral one. -/
lemma integral_fejerKernel (N : ℕ) : ∫ x, fejerKernel N x ∂haar = 1 := by
  have hint : ∀ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      Integrable (fun x : 𝕋 =>
        (1 - (k.natAbs : ℂ) / (N + 1)) * fourier k x) haar :=
    fun k _ => (integrable_fourier k).const_mul _
  have hcomp : ∫ x, (fejerKernel N x : ℂ) ∂haar = 1 := by
    simp_rw [fejerKernel_eq_sum, integral_finsetSum _ hint, integral_const_mul, integral_fourier]
    rw [Finset.sum_eq_single (0 : ℤ)]
    · simp
    · intro k hk hk0
      simp [hk0]
    · intro h0
      exact absurd (by simp : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) N) h0
  rw [integral_complex_ofReal] at hcomp
  exact_mod_cast hcomp

/-- The Fejer kernel is integrable. -/
lemma integrable_fejerKernel (N : ℕ) : Integrable (fejerKernel N) haar :=
  (continuous_fejerKernel N).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Lebesgue integral of the nonnegative kernel is one. -/
lemma lintegral_fejerKernel (N : ℕ) :
    ∫⁻ x, ENNReal.ofReal (fejerKernel N x) ∂haar = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_fejerKernel N)
      (ae_of_all _ (fejerKernel_nonneg N)), integral_fejerKernel]
  simp

/-- Outside a neighbourhood of zero, the Fejer kernel concentrates to mass zero. -/
lemma tendsto_fejerKernel_tail {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => ∫ y in {y : 𝕋 | δ ≤ ‖y‖}, fejerKernel N y ∂haar) atTop (𝓝 0) := by
  by_cases hhalf : 1 / 2 < δ
  · have hempty : {y : 𝕋 | δ ≤ ‖y‖} = ∅ := by
      ext y
      simp only [Set.mem_ofPred, Set.mem_empty_iff_false, iff_false, not_le]
      have hy : ‖y‖ ≤ 1 / 2 := by
        simpa [abs_one] using
          AddCircle.norm_le_half_period (p := 1) (x := y) one_ne_zero
      exact hy.trans_lt hhalf
    simp [hempty]
  · push Not at hhalf
    let s : Set 𝕋 := {y | δ ≤ ‖y‖}
    have hs : MeasurableSet s :=
      measurableSet_le measurable_const (continuous_norm.measurable)
    have hle : ∀ N, ∫ y in s, fejerKernel N y ∂haar ≤
        (1 / (4 * δ ^ 2)) * ((N : ℝ) + 1)⁻¹ := by
      intro N
      have hpt : ∀ y ∈ s, fejerKernel N y ≤ 1 / (4 * (N + 1) * δ ^ 2) := by
        intro y hy
        obtain ⟨u, hu, rfl, hnorm⟩ := exists_coe_norm y
        have hδu : δ ≤ |u| := by
          rw [← hnorm]
          simpa [s, Set.mem_ofPred] using hy
        have hu0 : u ≠ 0 := by
          intro hu0
          rw [hu0, abs_zero] at hδu
          exact lt_irrefl (0 : ℝ) (hδ.trans_le hδu)
        have hsqδ : δ ^ 2 ≤ u ^ 2 := (sq_le_sq).2 (by rwa [abs_of_pos hδ])
        rw [← fejerKernelReal_eq]
        calc
          fejerKernelReal N u ≤ 1 / (4 * (N + 1) * u ^ 2) :=
            fejerKernelReal_le_inv_sq hu0 hu
          _ ≤ 1 / (4 * (N + 1) * δ ^ 2) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hsqδ (by positivity)) zero_le_one
      have hintC : IntegrableOn (fun _ : 𝕋 => 1 / (4 * (N + 1) * δ ^ 2)) s haar :=
        integrableOn_const (by finiteness) (by finiteness)
      have hsle : (haar).real s ≤ 1 := by
        calc
          (haar).real s ≤ (haar).real Set.univ := measureReal_mono (Set.subset_univ s)
          _ = 1 := by simp [Measure.real, measure_univ]
      calc
        ∫ y in s, fejerKernel N y ∂haar
            ≤ ∫ y in s, 1 / (4 * (N + 1) * δ ^ 2) ∂haar :=
          setIntegral_mono_on (integrable_fejerKernel N).integrableOn hintC hs hpt
        _ = (haar).real s * (1 / (4 * (N + 1) * δ ^ 2)) := by
          rw [setIntegral_const, smul_eq_mul]
        _ ≤ 1 * (1 / (4 * (N + 1) * δ ^ 2)) :=
          mul_le_mul_of_nonneg_right hsle (by positivity)
        _ = 1 / (4 * (N + 1) * δ ^ 2) := by ring
        _ = (1 / (4 * δ ^ 2)) * ((N : ℝ) + 1)⁻¹ := by field_simp
    refine squeeze_zero (fun N => setIntegral_nonneg hs fun y _ => fejerKernel_nonneg N y) hle ?_
    have hinv : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    have hc : Tendsto (fun _ : ℕ => 1 / (4 * δ ^ 2)) atTop (𝓝 (1 / (4 * δ ^ 2))) :=
      tendsto_const_nhds
    simpa [mul_zero] using hc.mul hinv

set_option backward.isDefEq.respectTransparency true in
/-- A character of a difference factors out of a pointwise product. -/
private lemma fourier_sub_mul (k : ℤ) (x t : 𝕋) (z : ℂ) :
    fourier k (x - t) * z = fourier k x * (fourier (-k) t * z) :=
  (congr_arg (fun w : ℂ => w * z) (fourier_sub_right k x t)).trans
    (mul_assoc (fourier k x) (fourier (-k) t) z)

set_option backward.isDefEq.respectTransparency true in
/-- An integrable function has Fejer means given by convolution against the kernel. -/
lemma fejerMean_eq_conv {f : 𝕋 → ℂ} (hf : Integrable f haar) (N : ℕ) (x : 𝕋) :
    fejerMean f N x = ∫ t, (fejerKernel N t : ℂ) * f (x - t) ∂haar := by
  have hint : ∀ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      Integrable (fun t : 𝕋 => (1 - (k.natAbs : ℂ) / (N + 1)) *
        (fourier k x * (fourier (-k) t * f t))) haar := by
    intro k _
    simpa [smul_eq_mul] using
      ((hf.fourier_smul (-k)).const_mul (fourier k x)).const_mul _
  have hpt : ∀ t, (fejerKernel N (x - t) : ℂ) * f t =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (1 - (k.natAbs : ℂ) / (N + 1)) *
          (fourier k x * (fourier (-k) t * f t)) := by
    intro t
    rw [fejerKernel_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, fourier_sub_mul]
  have hshift : ∫ t, (fejerKernel N (x - t) : ℂ) * f t ∂haar =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (1 - (k.natAbs : ℂ) / (N + 1)) * fourierCoeff f k * fourier k x := by
    rw [integral_congr_ae (ae_of_all _ hpt), integral_finsetSum _ hint]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, integral_const_mul]
    have hcoeff : ∫ t, fourier (-k) t * f t ∂haar = fourierCoeff f k := by
      simp only [fourierCoeff, smul_eq_mul]
    rw [hcoeff, ← mul_assoc, mul_right_comm]
  rw [fejerMean_eq_weighted, ← hshift]
  let g : 𝕋 → ℂ := fun u => (fejerKernel N u : ℂ) * f (x - u)
  have hfun : (fun t => (fejerKernel N (x - t) : ℂ) * f t) = fun t => g (x - t) := by
    funext t
    simp only [g]
    rw [sub_sub_cancel]
  rw [hfun]
  exact integral_sub_left_eq_self g haar x

set_option backward.isDefEq.respectTransparency true in
/-- Subtracting the value leaves a convolution against the kernel of mass one. -/
lemma fejerMean_sub_eq_conv {f : 𝕋 → ℂ} (hf : Integrable f haar) (N : ℕ) (x : 𝕋) :
    fejerMean f N x - f x = ∫ t, (fejerKernel N t : ℂ) * (f (x - t) - f x) ∂haar := by
  have hone : ∫ t, (fejerKernel N t : ℂ) ∂haar = 1 := by
    rw [integral_complex_ofReal]
    exact_mod_cast integral_fejerKernel N
  have hconst : ∫ t, (fejerKernel N t : ℂ) * f x ∂haar = f x := by
    rw [integral_mul_const, hone, one_mul]
  have hshift : Integrable (fun t : 𝕋 => f (x - t)) haar := hf.comp_sub_left x
  have hker : AEStronglyMeasurable (fun t : 𝕋 => (fejerKernel N t : ℂ)) haar :=
    (Complex.continuous_ofReal.comp (continuous_fejerKernel N)).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂haar, ‖(fejerKernel N t : ℂ)‖ ≤ (N + 1 : ℝ) :=
    ae_of_all _ fun t => by
      rw [Complex.norm_real, Real.norm_of_nonneg (fejerKernel_nonneg N t)]
      exact fejerKernel_le_succ N t
  have hint1 : Integrable (fun t => (fejerKernel N t : ℂ) * f (x - t)) haar :=
    hshift.bdd_mul hker hbound
  have hint2 : Integrable (fun t => (fejerKernel N t : ℂ) * f x) haar :=
    (integrable_of_continuous
      (Complex.continuous_ofReal.comp (continuous_fejerKernel N))).mul_const (f x)
  rw [fejerMean_eq_conv hf N x]
  conv_lhs =>
    arg 2
    rw [← hconst]
  rw [← integral_sub hint1 hint2]
  simp_rw [mul_sub]

/-! ### Carleson–Hunt -/

/-- **27.22**: Carleson–Hunt maximal control and almost-everywhere ordinary Fourier convergence. -/
theorem carleson_hunt {p : ℝ} (hp : 1 < p) : ∃ C : ℝ≥0∞, C ≠ ∞ ∧
    ∀ f : AddCircle (1 : ℝ) → ℂ, MemLp f (ENNReal.ofReal p) AddCircle.haarAddCircle →
      (∫⁻ x, (carlesonMaximalFunction f x) ^ p ∂AddCircle.haarAddCircle) ≤
        C * (eLpNorm f (ENNReal.ofReal p) AddCircle.haarAddCircle) ^ p ∧
      ∀ᵐ x ∂AddCircle.haarAddCircle, Tendsto (fun N ↦ fourierPartialSum f N x) atTop (𝓝 (f x)) := by
  sorry

end CKMA
