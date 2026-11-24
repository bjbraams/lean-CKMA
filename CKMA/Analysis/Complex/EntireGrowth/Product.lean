/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Complex.EntireGrowth.Elementary
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import TauCeti.Analysis.Analytic.Order

import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Convergence of a fixed-genus canonical product

An `Option`-valued list of nonzero slopes, with summable reciprocal powers of order `p + 1`,
determines an entire canonical product of genus `p`. The product converges uniformly on compact
sets, and its analytic order at a point is the number of listed slopes equal to that point.
The genus-one case is in TauCeti; the argument here keeps an arbitrary genus and an explicit
`ℕ`-enumeration, padding a finite zero list by `none`.
-/

public section

noncomputable section

namespace CKMA

open Complex Filter Finset Metric Set Topology
open scoped BigOperators

variable {ι : Type*}

/-- Reciprocal power `‖w‖ ^ (-(p + 1))` of one listed slope. A padding entry contributes `0`.
A zero slope has weight `0`, because `Real.rpow` of `0` to a negative power is `0`. -/
@[expose]
def slopeWeight (p : ℕ) (a : ι → Option ℂ) (i : ι) : ℝ :=
  match a i with
  | none => 0
  | some w => ‖w‖ ^ (-((p : ℝ) + 1))

/-- A padding entry has weight zero. -/
theorem slopeWeight_none {p : ℕ} {a : ι → Option ℂ} {i : ι} (ha : a i = none) :
    slopeWeight p a i = 0 := by
  simp [slopeWeight, ha]

/-- A listed slope of modulus `‖w‖` has weight `‖w‖ ^ (-(p + 1))`. -/
theorem slopeWeight_some {p : ℕ} {a : ι → Option ℂ} {i : ι} {w : ℂ} (ha : a i = some w) :
    slopeWeight p a i = ‖w‖ ^ (-((p : ℝ) + 1)) := by
  simp [slopeWeight, ha]

/-- A genus-`p` factor on an arbitrary index. On `ℕ` it agrees with `optionFactor`.
A zero slope makes `z / w = 0`, and the elementary factor at `0` equals `1`. -/
@[expose]
def genusFactor (p : ℕ) (a : ι → Option ℂ) (i : ι) (z : ℂ) : ℂ :=
  match a i with
  | none => 1
  | some w => weierstrassFactor p (z / w)

/-- On `ℕ`, the general factor is the factor used by the elementary estimates. -/
theorem genusFactor_eq_optionFactor (p : ℕ) (a : ℕ → Option ℂ) (n : ℕ) (z : ℂ) :
    genusFactor p a n z = optionFactor p a n z := by
  rfl

/-- A missing slope contributes the constant factor one. -/
theorem genusFactor_none {p : ℕ} {a : ι → Option ℂ} {i : ι} {z : ℂ} (ha : a i = none) :
    genusFactor p a i z = 1 := by
  simp [genusFactor, ha]

/-- A listed slope contributes the elementary factor of `z / w`. -/
theorem genusFactor_some {p : ℕ} {a : ι → Option ℂ} {i : ι} {z w : ℂ} (ha : a i = some w) :
    genusFactor p a i z = weierstrassFactor p (z / w) := by
  simp [genusFactor, ha]

/-- Each factor is an entire function of `z`. -/
theorem differentiable_genusFactor (p : ℕ) (a : ι → Option ℂ) (i : ι) :
    Differentiable ℂ (genusFactor p a i) := by
  unfold genusFactor
  split
  · exact differentiable_const _
  · exact (differentiable_weierstrassFactor p).comp (differentiable_id.div_const _)

/-- The factor is normalized to one at the origin, whether or not a slope is listed. -/
theorem genusFactor_zero (p : ℕ) (a : ι → Option ℂ) (i : ι) : genusFactor p a i 0 = 1 := by
  unfold genusFactor
  split
  · rfl
  · simp [weierstrassFactor_zero]

/-- The factor vanishes only at its listed slope. -/
theorem genusFactor_eq_zero_iff {p : ℕ} {a : ι → Option ℂ} {i : ι} {z : ℂ}
    (hne : ∀ w, a i = some w → w ≠ 0) :
    genusFactor p a i z = 0 ↔ a i = some z := by
  cases ha : a i with
  | none =>
    constructor
    · intro h
      simp [genusFactor_none ha] at h
    · intro h
      simp at h
  | some w =>
    have hw0 : w ≠ 0 := hne w ha
    rw [genusFactor_some ha]
    constructor
    · intro h
      have hzw : z / w = 1 := weierstrassFactor_eq_zero_iff.mp h
      rw [div_eq_iff hw0, one_mul] at hzw
      rw [← hzw]
    · intro hz
      have hwz : w = z := Option.some.inj hz
      rw [weierstrassFactor_eq_zero_iff, hwz]
      exact div_self (hwz ▸ hw0)

variable (p : ℕ) (a : ι → Option ℂ)
  (hsum : Summable (slopeWeight p a))
  (hne : ∀ i w, a i = some w → w ≠ 0)

include hsum

/-- Listed slopes tend to infinity along the cofinite filter. -/
theorem eventually_slopeWeight_lt {c : ℝ} (hc : 0 < c) :
    ∀ᶠ i in cofinite, slopeWeight p a i < c :=
  hsum.tendsto_cofinite_zero.eventually (gt_mem_nhds hc)

include hne

/-- On a disk of radius `R`, all but finitely many factors are `1 + O((R / ‖w‖) ^ (p + 1))`. -/
theorem eventually_norm_genusFactor_sub_one_le {R : ℝ} (hR : 0 < R) :
    ∀ᶠ i in cofinite, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖genusFactor p a i z - 1‖ ≤ 4 * R ^ (p + 1) * slopeWeight p a i := by
  have hq : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hthresh : 0 < (2 * R) ^ (-((p : ℝ) + 1)) := Real.rpow_pos_of_pos (by linarith) _
  filter_upwards [eventually_slopeWeight_lt p a hsum hthresh] with i hi z hz
  cases ha : a i with
  | none =>
    rw [genusFactor_none ha, slopeWeight_none ha]
    simp
  | some w =>
    have hw0 : w ≠ 0 := hne i w ha
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hwlarge : 2 * R < ‖w‖ := by
      by_contra hle
      have hle' : ‖w‖ ≤ 2 * R := le_of_not_gt hle
      have hpow : (2 * R) ^ (-((p : ℝ) + 1)) ≤ ‖w‖ ^ (-((p : ℝ) + 1)) :=
        Real.rpow_le_rpow_of_nonpos hwpos hle' (by linarith)
      rw [slopeWeight_some ha] at hi
      linarith
    have hdiv : (R / ‖w‖) ^ (p + 1) = R ^ (p + 1) * ‖w‖ ^ (-((p : ℝ) + 1)) := by
      have hnat := (Real.rpow_natCast ‖w‖ (p + 1)).symm
      have hneg := (Real.rpow_neg (norm_nonneg w) ((p + 1 : ℕ) : ℝ)).symm
      have hcast : ((p + 1 : ℕ) : ℝ) = (p : ℝ) + 1 := by simp [Nat.cast_add, Nat.cast_one]
      rw [div_pow, div_eq_mul_inv, hnat, hneg, hcast]
    have hfac := norm_optionFactor_sub_one_of_large (p := p)
      (a := fun _ : ℕ => a i) (n := 0) (z := z) (w := w) (R := R) (by simp [ha]) hR hz
      hwlarge.le
    calc
      ‖genusFactor p a i z - 1‖ = ‖weierstrassFactor p (z / w) - 1‖ := by
        rw [genusFactor_some ha]
      _ ≤ 4 * (R / ‖w‖) ^ (p + 1) := by
        rw [optionFactor_some (show (fun _ : ℕ => a i) 0 = some w from ha)] at hfac
        exact hfac
      _ = 4 * (R ^ (p + 1) * ‖w‖ ^ (-((p : ℝ) + 1))) := by rw [hdiv]
      _ = 4 * R ^ (p + 1) * slopeWeight p a i := by
        rw [slopeWeight_some ha]
        ring

/-- The deviations from one are absolutely summable at each point. -/
theorem summable_norm_genusFactor_sub_one (z : ℂ) :
    Summable fun i ↦ ‖genusFactor p a i z - 1‖ := by
  have hR : 0 < ‖z‖ + 1 := by positivity
  have hu : Summable fun i ↦ 4 * (‖z‖ + 1) ^ (p + 1) * slopeWeight p a i :=
    hsum.mul_left _
  refine hu.of_norm_bounded_eventually ?_
  filter_upwards [eventually_norm_genusFactor_sub_one_le p a hsum hne hR] with i hi
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hi z (by linarith)

/-- The canonical product converges at every point. -/
theorem multipliable_genusFactor (z : ℂ) : Multipliable fun i ↦ genusFactor p a i z := by
  simpa [sub_add_cancel] using
    multipliable_one_add_of_summable (summable_norm_genusFactor_sub_one p a hsum hne z)

/-- The product vanishes at `z` exactly when some factor does. -/
theorem tprod_genusFactor_eq_zero_iff (z : ℂ) :
    (∏' i, genusFactor p a i z) = 0 ↔ ∃ i, genusFactor p a i z = 0 := by
  constructor
  · intro hzero
    by_contra hn
    push Not at hn
    have hp := tprod_one_add_ne_zero_of_summable
      (f := fun i ↦ genusFactor p a i z - 1)
      (fun i h ↦ hn i (by simpa [sub_eq_zero] using h))
      (summable_norm_genusFactor_sub_one p a hsum hne z)
    exact hp (by simpa [sub_add_cancel] using hzero)
  · rintro ⟨i, hi⟩
    exact tprod_of_exists_eq_zero ⟨i, hi⟩

/-- The product of the factors converges uniformly on every compact set. -/
theorem hasProdUniformlyOn_genusFactor {K : Set ℂ} (hK : IsCompact K) :
    HasProdUniformlyOn (fun i z ↦ genusFactor p a i z)
      (fun z ↦ ∏' i, genusFactor p a i z) K := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  let R : ℝ := max M 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hu : Summable fun i ↦ 4 * R ^ (p + 1) * slopeWeight p a i := hsum.mul_left _
  have hbound : ∀ᶠ i in cofinite, ∀ z ∈ K, ‖genusFactor p a i z - 1‖ ≤
      4 * R ^ (p + 1) * slopeWeight p a i := by
    filter_upwards [eventually_norm_genusFactor_sub_one_le p a hsum hne hR] with i hi z hz
    exact hi z ((hM z hz).trans (le_max_left _ _))
  have hcts : ∀ i, ContinuousOn (fun z ↦ genusFactor p a i z - 1) K := by
    intro i
    exact ((differentiable_genusFactor p a i).continuous.sub continuous_const).continuousOn
  have h := Summable.hasProdUniformlyOn_one_add hK hu hbound hcts
  refine (h.congr ?_).congr_right ?_
  · refine Eventually.of_forall fun t ↦ ?_
    intro z hz
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    ring
  · intro z hz
    exact tprod_congr fun i ↦ by ring

/-- The canonical product converges locally uniformly on the plane. -/
theorem hasProdLocallyUniformlyOn_genusFactor :
    HasProdLocallyUniformlyOn (fun i z ↦ genusFactor p a i z)
      (fun z ↦ ∏' i, genusFactor p a i z) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  exact hasProdUniformlyOn_genusFactor p a hsum hne hK

/-- A canonical product of genus `p` is entire. -/
theorem differentiable_tprod_genusFactor :
    Differentiable ℂ (fun z ↦ ∏' i, genusFactor p a i z) := by
  rw [← differentiableOn_univ]
  refine (hasProdLocallyUniformlyOn_genusFactor p a hsum hne).differentiableOn ?_ isOpen_univ
  apply Eventually.of_forall
  intro s
  refine Differentiable.differentiableOn ?_
  classical
  induction s using Finset.induction with
  | empty =>
    simp
  | insert i t hi ih =>
    have hfun : (fun z ↦ ∏ j ∈ insert i t, genusFactor p a j z) =
        fun z ↦ genusFactor p a i z * ∏ j ∈ t, genusFactor p a j z := by
      ext z
      rw [Finset.prod_insert hi]
    exact hfun ▸ (differentiable_genusFactor p a i).mul ih

omit hsum hne

/-- The value at the origin is one. -/
theorem tprod_genusFactor_zero : (∏' i, genusFactor p a i 0) = 1 := by
  rw [tprod_congr (fun i ↦ genusFactor_zero p a i), tprod_one]

include hne

/-- No factor vanishes at a point outside the listed slopes. -/
theorem genusFactor_ne_zero_of_ne {z : ℂ} (hz : ∀ i, a i ≠ some z) (i : ι) :
    genusFactor p a i z ≠ 0 := by
  intro hzero
  exact hz i ((genusFactor_eq_zero_iff (fun w hw ↦ hne i w hw)).mp hzero)

include hsum

/-- Only finitely many factors vanish at a given point. -/
theorem finite_genusFactor_roots (z : ℂ) : {i | a i = some z}.Finite := by
  by_cases hz : z = 0
  · have hempty : {i | a i = some z} = ∅ := by
      ext i
      simp only [mem_ofPred, Set.mem_empty_iff_false, iff_false]
      intro hi
      exact hne i z hi hz
    simp [hempty]
  · have hpos : 0 < ‖z‖ ^ (-((p : ℝ) + 1)) :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) _
    have hev := eventually_slopeWeight_lt p a hsum hpos
    rw [eventually_cofinite] at hev
    refine hev.subset ?_
    intro i hi
    have hi' : a i = some z := by simpa [mem_ofPred] using hi
    rw [mem_ofPred, slopeWeight_some hi']
    exact lt_irrefl _

omit hsum hne

/-- A listed slope is a simple zero of its factor. -/
theorem analyticOrderAt_genusFactor_of_some {i : ι} {z : ℂ}
    (hne : ∀ w, a i = some w → w ≠ 0) (hi : a i = some z) :
    analyticOrderAt (genusFactor p a i) z = 1 := by
  have hz0 : z ≠ 0 := hne z hi
  have hfun : genusFactor p a i = fun w ↦ weierstrassFactor p (w / z) := by
    ext w
    rw [genusFactor_some hi]
  rw [hfun]
  exact analyticOrderAt_weierstrassFactor_div hz0 rfl

include hne

/-- The order of a finite product of factors that all vanish at `z` is the number of factors. -/
private theorem analyticOrderAt_finsetProd_genusFactor {z : ℂ} (s : Finset ι)
    (hs : ∀ i ∈ s, a i = some z) :
    analyticOrderAt (fun w ↦ ∏ i ∈ s, genusFactor p a i w) z = s.card := by
  have heq : (fun w ↦ ∏ i ∈ s, genusFactor p a i w) =
      ∏ i ∈ s, genusFactor p a i := by
    ext w
    simp
  rw [heq, TauCeti.analyticOrderAt_prod (fun i _ ↦ (differentiable_genusFactor p a i).analyticAt z)]
  calc
    _ = ∑ _i ∈ s, (1 : ℕ∞) := Finset.sum_congr rfl fun i hi ↦
      analyticOrderAt_genusFactor_of_some p a (fun w hw ↦ hne i w hw) (hs i hi)
    _ = _ := by simp

include hsum

/-- The product order is the cardinality of any finite set containing exactly its vanishing
factors. -/
theorem analyticOrderAt_tprod_genusFactor_of_finset {z : ℂ} (s : Finset ι)
    (hs : ∀ i, a i = some z ↔ i ∈ s) :
    analyticOrderAt (fun w ↦ ∏' i, genusFactor p a i w) z = s.card := by
  classical
  have hprodDiff : Differentiable ℂ (fun w ↦ ∏ i ∈ s, genusFactor p a i w) := by
    clear hs
    induction s using Finset.induction with
    | empty =>
      rw [show (fun w : ℂ ↦ ∏ i ∈ (∅ : Finset ι), genusFactor p a i w) = fun _ ↦ 1 by
        ext w; simp]
      exact differentiable_const _
    | insert i t hi ih =>
      have hfun : (fun w ↦ ∏ j ∈ insert i t, genusFactor p a j w) =
          fun w ↦ genusFactor p a i w * ∏ j ∈ t, genusFactor p a j w := by
        ext w
        rw [Finset.prod_insert hi]
      exact hfun ▸ (differentiable_genusFactor p a i).mul ih
  let sc : Set ι := (s : Set ι)ᶜ
  let aTail : sc → Option ℂ := fun i ↦ a i
  have hsumTail : Summable (slopeWeight p aTail) :=
    (hsum.subtype (fun i ↦ i ∈ sc)).congr fun i ↦ by simp [slopeWeight, aTail]
  have hneTail : ∀ i w, aTail i = some w → w ≠ 0 := fun i w hw ↦ hne i w hw
  have htail := differentiable_tprod_genusFactor p aTail hsumTail hneTail
  have htailFun : (fun w ↦ ∏' i, genusFactor p aTail i w) =
      fun w ↦ ∏' i : sc, genusFactor p a i w := by
    ext w
    refine tprod_congr fun i ↦ ?_
    simp [aTail, genusFactor]
  have htailAnalytic : AnalyticAt ℂ (fun w ↦ ∏' i : sc, genusFactor p a i w) z := by
    rw [← htailFun]
    exact htail.analyticAt z
  have htailNe : (∏' i : sc, genusFactor p a i z) ≠ 0 := by
    rw [← congrFun htailFun z, ne_eq,
      tprod_genusFactor_eq_zero_iff p aTail hsumTail hneTail z]
    rintro ⟨i, hi⟩
    have hfac : aTail i = some z :=
      (genusFactor_eq_zero_iff (fun w hw ↦ hneTail i w hw)).mp hi
    exact i.property ((hs i).mp (by simpa [aTail] using hfac))
  have hprodAnalytic : AnalyticAt ℂ (fun w ↦ ∏ i ∈ s, genusFactor p a i w) z :=
    hprodDiff.analyticAt z
  have heq : (fun w ↦ ∏' i, genusFactor p a i w) =
      (fun w ↦ ∏ i ∈ s, genusFactor p a i w) *
        fun w ↦ ∏' i : sc, genusFactor p a i w := by
    funext w
    have htailProd : Multipliable (fun i : sc ↦ genusFactor p a i w) := by
      have hm := multipliable_genusFactor p aTail hsumTail hneTail w
      simpa [aTail, genusFactor] using hm
    have hsplit := Multipliable.tprod_mul_tprod_compl
      (s := (s : Set ι)) (f := fun i ↦ genusFactor p a i w) Multipliable.of_finite htailProd
    rw [s.tprod_subtype' (fun i ↦ genusFactor p a i w)] at hsplit
    exact hsplit.symm
  rw [heq, analyticOrderAt_mul hprodAnalytic htailAnalytic,
    analyticOrderAt_finsetProd_genusFactor p a hne s (fun i hi ↦ (hs i).mpr hi),
    htailAnalytic.analyticOrderAt_eq_zero.mpr htailNe, add_zero]

/-- The order of the product counts the listed copies of that point. -/
theorem analyticOrderAt_tprod_genusFactor (z : ℂ) :
    analyticOrderAt (fun w ↦ ∏' i, genusFactor p a i w) z =
      ({i | a i = some z}.ncard : ℕ∞) := by
  have hf := finite_genusFactor_roots p a hsum hne z
  rw [Set.ncard_eq_toFinset_card _ hf]
  exact analyticOrderAt_tprod_genusFactor_of_finset p a hsum hne hf.toFinset
    (fun i ↦ hf.mem_toFinset.symm)

omit hsum hne

/-- Partial products over `Finset.range` converge uniformly on compact sets. -/
theorem tendstoUniformlyOn_genusFactor_range {a : ℕ → Option ℂ}
    (hsum : Summable (slopeWeight p a)) (hne : ∀ n w, a n = some w → w ≠ 0)
    {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun N z ↦ ∏ n ∈ range N, genusFactor p a n z)
      (fun z ↦ ∏' n, genusFactor p a n z) atTop K :=
  (hasProdUniformlyOn_genusFactor p a hsum hne hK).tendstoUniformlyOn_finsetRange

end CKMA
