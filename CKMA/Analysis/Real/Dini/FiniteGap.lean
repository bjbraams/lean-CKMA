/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Real.Dini.Infinite
public import Mathlib.MeasureTheory.Covering.Differentiation
public import Mathlib.MeasureTheory.Covering.OneDim
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Tactic

/-!
# Finite gaps between opposite Dini derivatives

On a short interval whose endpoints lie in a set of uniformly bounded slopes, a direct Vitali
packing and the same packing for the reflected function force the outer measure to be a definite
fraction of the length. Lebesgue density points then make each such set null, and a countable
union absorbs every point at which the lower left derivative is finite, strictly below the upper
right derivative, and the upper right derivative is finite. Source: GAPS 05.10.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Set Filter Topology MeasureTheory IsUnifLocDoublingMeasure
open scoped ENNReal

/-- A left increment flatter than `s` exists at every negative scale below the liminf. -/
lemma exists_left_slope_lt (f : ℝ → ℝ) (x s ε : ℝ)
    (hs : lowerLeftDiniDerivative f x < (s : EReal)) (hε : ε < 0) :
    ∃ h, ε < h ∧ h < 0 ∧ (f (x + h) - f x) / h < s := by
  have hfreq : ∃ᶠ h in 𝓝[<] (0 : ℝ), extendedDifferenceQuotient f x h < (s : EReal) :=
    frequently_lt_of_liminf_lt (hu := isCobounded_ge_of_top) hs
  have hmem : Ioo ε (0 : ℝ) ∈ 𝓝[<] 0 := by
    rw [mem_nhdsLT_iff_exists_Ioo_subset]
    exact ⟨ε, hε, subset_rfl⟩
  have hsmall : ∀ᶠ h in 𝓝[<] (0 : ℝ), ε < h ∧ h < 0 :=
    eventually_of_mem hmem fun h hh => ⟨hh.1, hh.2⟩
  obtain ⟨h, hhE, hh⟩ := (hfreq.and_eventually hsmall).exists
  refine ⟨h, hh.1, hh.2, ?_⟩
  unfold extendedDifferenceQuotient at hhE
  exact (EReal.coe_lt_coe_iff).1 hhE

/-- Reflection through a point preserves Lebesgue outer measure. -/
lemma volume_preimage_reflect (c : ℝ) (s : Set ℝ) :
    volume ((fun x => c - x) ⁻¹' s) = volume s := by
  have hcomp : (fun x : ℝ => c - x) = (fun x => c + x) ∘ Neg.neg := by
    ext x
    simp [Function.comp, sub_eq_add_neg]
  rw [hcomp, preimage_comp, Measure.measure_preimage_neg, measure_preimage_add]

/-- An open interval is invariant under reflection through its centre. -/
lemma preimage_reflect_Ioo (a b : ℝ) :
    (fun x => a + b - x) ⁻¹' Ioo a b = Ioo a b := by
  ext x
  simp only [mem_preimage, mem_Ioo]
  constructor <;> intro hx <;> constructor <;> linarith

/-- Reflection through the centre preserves the outer measure of a set inside `(a, b)`. -/
lemma volume_reflect_inter {E : Set ℝ} {a b : ℝ} :
    volume ({x | a + b - x ∈ E} ∩ Ioo a b) = volume (E ∩ Ioo a b) := by
  have hpre : (fun x => a + b - x) ⁻¹' (E ∩ Ioo a b) =
      {x | a + b - x ∈ E} ∩ Ioo a b := by
    ext x
    simp only [mem_preimage, mem_inter_iff, mem_Ioo, mem_ofPred_eq]
    constructor
    · intro hx
      exact ⟨hx.1, by linarith [hx.2.1, hx.2.2], by linarith [hx.2.1, hx.2.2]⟩
    · intro hx
      exact ⟨hx.1, by linarith [hx.2.1, hx.2.2], by linarith [hx.2.1, hx.2.2]⟩
  rw [← hpre]
  exact volume_preimage_reflect (a + b) (E ∩ Ioo a b)

/-- Points with uniform slope bounds and a finite gap between the lower left and upper right
derivatives. `n` fixes the scale `1 / (n + 1)`. -/
def finiteGap (f : ℝ → ℝ) (p r s q : ℚ) (n : ℕ) : Set ℝ :=
  {x |
    (∀ h, 0 < h → h ≤ (1 : ℝ) / (n + 1) → (f (x + h) - f x) / h < (p : ℝ)) ∧
    (∀ h, -(1 : ℝ) / (n + 1) ≤ h → h < 0 → (q : ℝ) < (f (x + h) - f x) / h) ∧
    ((r : ℝ) : EReal) < upperRightDiniDerivative f x ∧
    lowerLeftDiniDerivative f x < ((s : ℝ) : EReal)}

/-- Both endpoints in `finiteGap` give an outer-measure bound by the gap ratio. -/
lemma finiteGap_volume_le (f : ℝ → ℝ) {p r s q : ℚ} {n : ℕ} {a b : ℝ}
    (hqr : (q : ℝ) < r) (hsp : (s : ℝ) < p)
    (hab : a < b) (hlen : b - a < (1 : ℝ) / (n + 1))
    (ha : a ∈ finiteGap f p r s q n) (hb : b ∈ finiteGap f p r s q n) :
    (volume (finiteGap f p r s q n ∩ Ioo a b)).toReal ≤
      ((p - q) / ((p - q) + (r - s))) * (b - a) := by
  set E := finiteGap f p r s q n
  set δ : ℝ := (1 : ℝ) / (n + 1)
  let g : ℝ → ℝ := fun t => f (a + b - t)
  let E' : Set ℝ := {t | a + b - t ∈ E}
  have hleft : ∀ x ∈ E, ∀ u, x - δ < u → u < x →
      (q : ℝ) < (f x - f u) / (x - u) := by
    intro x hx u hu hux
    have hge : -(1 : ℝ) / (n + 1) ≤ u - x := by
      have hsub : -((1 : ℝ) / (n + 1)) < u - x := by linarith
      rw [← neg_div ((n : ℝ) + 1) (1 : ℝ)] at hsub
      exact hsub.le
    have hs := hx.2.1 (u - x) hge (by linarith)
    have hadd : x + (u - x) = u := by
      rw [add_comm]
      exact sub_add_cancel u x
    rw [hadd, ← differenceQuotient_rev f x u] at hs
    exact hs
  have hfine : ∀ x ∈ E ∩ Ioo a b, ∀ ε > 0, ∃ y, x < y ∧ y ≤ b ∧ y - x < ε ∧
      (r : ℝ) < (f y - f x) / (y - x) := by
    intro x hx ε hε
    have hxlt : x < b := hx.2.2
    have htop : ((r : ℝ) : EReal) < upperRightDiniDerivative f x := hx.1.2.2.1
    have hε' : 0 < min ε (b - x) := lt_min hε (sub_pos.2 hxlt)
    obtain ⟨h, hh0, hhε, hhs⟩ :=
      exists_right_slope_gt f x r (min ε (b - x)) htop hε'
    have hh : x + h - x = h := by ring
    refine ⟨x + h, by linarith, ?_, ?_, ?_⟩
    · have : h < b - x := lt_of_lt_of_le hhε (min_le_right _ _)
      linarith
    · rw [hh]
      exact lt_of_lt_of_le hhε (min_le_left _ _)
    · rw [hh]
      exact hhs
  have hpack := slopePacking_volume_le f E hqr hab hlen hb hleft hfine
  have hleft' : ∀ x ∈ E', ∀ u, x - δ < u → u < x →
      -(p : ℝ) < (g x - g u) / (x - u) := by
    intro x hx u hu hux
    have hyE : a + b - x ∈ E := hx
    have hs := hyE.1 (x - u) (by linarith) (by linarith)
    have hadd : (a + b - x) + (x - u) = a + b - u := by ring
    rw [hadd] at hs
    have hid : (g x - g u) / (x - u) =
        -((f (a + b - u) - f (a + b - x)) / (x - u)) := by
      have hg : g x - g u = f (a + b - x) - f (a + b - u) := by simp [g]
      rw [hg, ← neg_sub (f (a + b - u)) (f (a + b - x)), neg_div]
    rw [hid]
    exact neg_lt_neg hs
  have hfine' : ∀ x ∈ E' ∩ Ioo a b, ∀ ε > 0, ∃ y, x < y ∧ y ≤ b ∧ y - x < ε ∧
      -(s : ℝ) < (g y - g x) / (y - x) := by
    intro x hx ε hε
    have hyE : a + b - x ∈ E := hx.1
    have hyx : x < b := hx.2.2
    have hLL : lowerLeftDiniDerivative f (a + b - x) < ((s : ℝ) : EReal) :=
      hyE.2.2.2
    set ε' : ℝ := -min ε (b - x)
    have hε' : ε' < 0 := neg_lt_zero.2 (lt_min hε (sub_pos.2 hyx))
    obtain ⟨h, hhε, hh0, hhs⟩ :=
      exists_left_slope_lt f (a + b - x) (s : ℝ) ε' hLL hε'
    have hden : (x - h) - x = -h := by ring
    refine ⟨x - h, by linarith, ?_, ?_, ?_⟩
    · have : -h < b - x := by
        have : -h < min ε (b - x) := by linarith [hhε]
        exact this.trans_le (min_le_right _ _)
      linarith
    · rw [hden]
      have : -h < ε := by
        have : -h < min ε (b - x) := by linarith [hhε]
        exact this.trans_le (min_le_left _ _)
      linarith
    · have hquot : (g (x - h) - g x) / ((x - h) - x) =
          -((f ((a + b - x) + h) - f (a + b - x)) / h) := by
        rw [hden]
        simp only [g]
        have harg : a + b - (x - h) = (a + b - x) + h := by ring
        rw [harg, div_neg]
      rw [hquot]
      exact neg_lt_neg hhs
  have hb' : b ∈ E' := by
    change a + b - b ∈ E
    simpa using ha
  have hkc : -(p : ℝ) < -(s : ℝ) := neg_lt_neg hsp
  have hpack' := slopePacking_volume_le g E' hkc hab hlen hb' hleft' hfine'
  have hvol := volume_reflect_inter (E := E) (a := a) (b := b)
  set σ : ℝ := (volume (E ∩ Ioo a b)).toReal
  have hσ : (volume (E' ∩ Ioo a b)).toReal = σ := by
    rw [hvol]
  rw [hσ] at hpack'
  have hsum : ((r : ℝ) - q + (p - s)) * σ ≤ (p - q) * (b - a) := by
    have hg : g b - g a = f a - f b := by simp [g]
    rw [hg] at hpack'
    nlinarith [hpack, hpack']
  have hden : 0 < (p - q) + ((r : ℝ) - s) := by linarith
  have hcoef : (r : ℝ) - q + (p - s) = (p - q) + (r - s) := by ring
  rw [hcoef] at hsum
  have hsum' : σ * ((p - q) + ((r : ℝ) - s)) ≤ (p - q) * (b - a) := by
    rw [mul_comm]
    exact hsum
  have hdiv : σ ≤ (p - q) * (b - a) / ((p - q) + (r - s)) :=
    (le_div_iff₀ hden).2 hsum'
  have hmul : (p - q) * (b - a) / ((p - q) + (r - s)) =
      ((p - q) / ((p - q) + (r - s))) * (b - a) := by
    ring
  rw [hmul] at hdiv
  exact hdiv

/-- Short intervals with an endpoint ratio bound have small outer measure up to the right end. -/
lemma volume_Icc_le_of_endpoint_ratio {E : Set ℝ} {δ ρ y x : ℝ}
    (hρ : 0 ≤ ρ) (hyx : y < x) (hlen : x - y < δ) (hx : x ∈ E)
    (hbound : ∀ a b, a ∈ E → b ∈ E → a < b → b - a < δ →
      (volume (E ∩ Ioo a b)).toReal ≤ ρ * (b - a)) :
    volume (E ∩ Icc y x) ≤ ENNReal.ofReal (ρ * (x - y)) := by
  have hpair : volume ({y, x} : Set ℝ) = 0 := by
    refine le_antisymm ?_ bot_le
    calc volume ({y, x} : Set ℝ)
        ≤ volume (({y} : Set ℝ) ∪ {x}) := measure_mono fun z hz => by
          simp only [mem_insert_iff, mem_singleton_iff] at hz
          rcases hz with rfl | rfl <;> simp
      _ ≤ volume ({y} : Set ℝ) + volume ({x} : Set ℝ) := measure_union_le _ _
      _ = 0 := by simp [measure_singleton]
  have hsub : E ∩ Icc y x ⊆ (E ∩ Ioo y x) ∪ {y, x} := by
    intro z hz
    rcases lt_trichotomy y z with hlt | rfl | hgt
    · rcases lt_trichotomy z x with hzx | rfl | hxz
      · exact Or.inl ⟨hz.1, hlt, hzx⟩
      · exact Or.inr (by simp)
      · linarith [hz.2.2]
    · exact Or.inr (by simp)
    · linarith [hz.2.1]
  have hle : volume (E ∩ Icc y x) ≤ volume (E ∩ Ioo y x) :=
    calc volume (E ∩ Icc y x)
        ≤ volume ((E ∩ Ioo y x) ∪ {y, x}) := measure_mono hsub
      _ ≤ volume (E ∩ Ioo y x) + volume ({y, x} : Set ℝ) := measure_union_le _ _
      _ = volume (E ∩ Ioo y x) := by rw [hpair, add_zero]
  set S := E ∩ Ioo y x
  by_cases hS : S.Nonempty
  · have hBdd : BddBelow S := ⟨y, fun z hz => hz.2.1.le⟩
    set α := sInf S
    have hαy : y ≤ α := le_csInf hS fun z hz => hz.2.1.le
    have hαx : α < x := by
      obtain ⟨z, hz⟩ := hS
      exact lt_of_le_of_lt (csInf_le hBdd hz) hz.2.2
    choose a ha using fun n : ℕ =>
      exists_lt_of_csInf_lt hS
        (lt_add_of_pos_right α (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)))
    let c : ℕ → ℝ := fun n => Nat.recOn n (a 0) fun k prev => min prev (a (k + 1))
    have hc0 : c 0 = a 0 := rfl
    have hsucc : ∀ n, c (n + 1) = min (c n) (a (n + 1)) := fun _ => rfl
    have hcS : ∀ n, c n ∈ S := by
      intro n
      induction n with
      | zero =>
        rw [hc0]
        exact (ha 0).1
      | succ n ih =>
        rw [hsucc]
        rcases le_total (c n) (a (n + 1)) with hle' | hle'
        · rw [min_eq_left hle']; exact ih
        · rw [min_eq_right hle']; exact (ha (n + 1)).1
    have hαc : ∀ n, α ≤ c n := by
      intro n
      induction n with
      | zero =>
        rw [hc0]
        exact csInf_le hBdd (ha 0).1
      | succ n ih =>
        rw [hsucc]
        exact le_min ih (csInf_le hBdd (ha (n + 1)).1)
    have hcle : ∀ n, c n ≤ a n := by
      intro n
      induction n with
      | zero => rw [hc0]
      | succ n _ =>
        rw [hsucc]
        exact min_le_right _ _
    have hmono : Monotone fun n => E ∩ Ioo (c n) x := by
      refine monotone_nat_of_le_succ fun n z hz => ?_
      have hc : c (n + 1) ≤ c n := by
        rw [hsucc]
        exact min_le_left _ _
      exact ⟨hz.1, lt_of_le_of_lt hc hz.2.1, hz.2.2⟩
    have hcover : ⋃ n, E ∩ Ioo (c n) x = E ∩ Ioo α x := by
      apply Subset.antisymm
      · intro z hz
        simp only [mem_iUnion] at hz
        obtain ⟨n, hz⟩ := hz
        exact ⟨hz.1, lt_of_le_of_lt (hαc n) hz.2.1, hz.2.2⟩
      · intro z hz
        have hpos : 0 < z - α := sub_pos.2 hz.2.1
        obtain ⟨n, hn⟩ := exists_nat_gt (1 / (z - α))
        have hn0 : (0 : ℝ) < n := (one_div_pos.2 hpos).trans hn
        have hfrac : (1 : ℝ) / (n + 1) < z - α := by
          have h1 : (1 : ℝ) / (n + 1) < 1 / n := by
            rw [one_div_lt_one_div (by linarith) hn0]
            linarith
          exact h1.trans ((one_div_lt hpos hn0).1 hn)
        have hcn : c n < z := by
          have han : a n < α + 1 / ((n : ℝ) + 1) := (ha n).2
          have : c n ≤ a n := hcle n
          linarith
        exact mem_iUnion.2 ⟨n, hz.1, hcn, hz.2.2⟩
    have hslice : ∀ n, volume (E ∩ Ioo (c n) x) ≤ ENNReal.ofReal (ρ * (x - α)) := by
      intro n
      have hcx : c n < x := (hcS n).2.2
      have hlenn : x - c n < δ := by
        have : y < c n := (hcS n).2.1
        linarith
      have htr := hbound (c n) x (hcS n).1 hx hcx hlenn
      have hfin : volume (E ∩ Ioo (c n) x) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top
          ((measure_mono (inter_subset_right : E ∩ Ioo (c n) x ⊆ Ioo (c n) x)).trans_eq
            Real.volume_Ioo)
      have hvol : volume (E ∩ Ioo (c n) x) ≤ ENNReal.ofReal (ρ * (x - c n)) := by
        rw [← ENNReal.ofReal_toReal hfin]
        exact ENNReal.ofReal_le_ofReal htr
      exact hvol.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (by linarith [hαc n]) hρ))
    have hU : volume (E ∩ Ioo α x) ≤ ENNReal.ofReal (ρ * (x - α)) := by
      rw [← hcover, hmono.measure_iUnion]
      exact iSup_le hslice
    have hSsub : S ⊆ (E ∩ Ioo α x) ∪ {α} := by
      intro z hz
      rcases eq_or_lt_of_le (csInf_le hBdd hz) with rfl | hlt
      · exact Or.inr rfl
      · exact Or.inl ⟨hz.1, hlt, hz.2.2⟩
    have hSvol : volume S ≤ ENNReal.ofReal (ρ * (x - α)) := by
      calc volume S
          ≤ volume ((E ∩ Ioo α x) ∪ {α}) := measure_mono hSsub
        _ ≤ volume (E ∩ Ioo α x) + volume ({α} : Set ℝ) := measure_union_le _ _
        _ ≤ ENNReal.ofReal (ρ * (x - α)) := by simp [hU, measure_singleton]
    exact hle.trans (hSvol.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (by linarith [hαy]) hρ)))
  · have hempty : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    have hzero : volume (E ∩ Icc y x) = 0 := by simpa [S, hempty] using hle
    exact hzero.trans_le bot_le

/-- A uniform positive-density failure on the left forces the outer measure to vanish. -/
lemma volume_eq_zero_of_short_ratio {E : Set ℝ} {δ ρ : ℝ}
    (hδ : 0 < δ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hbound : ∀ a b, a ∈ E → b ∈ E → a < b → b - a < δ →
      (volume (E ∩ Ioo a b)).toReal ≤ ρ * (b - a)) :
    volume E = 0 := by
  let v := vitaliFamily (volume : Measure ℝ) 1
  have hden := v.ae_tendsto_measure_inter_div E
  have hfail : ∀ x ∈ E, ¬ Tendsto (fun a => volume (E ∩ a) / volume a)
      (v.filterAt x) (𝓝 1) := by
    intro x hx htend
    have hcomp := htend.comp (Real.tendsto_Icc_vitaliFamily_left x)
    obtain ⟨θ, hθρ, hθ1⟩ := exists_between hρ1
    have hclose : ∀ᶠ y in 𝓝[<] x,
        ENNReal.ofReal θ < volume (E ∩ Icc y x) / volume (Icc y x) :=
      (tendsto_order.1 hcomp).1 _ ((ENNReal.ofReal_lt_one).2 hθ1)
    rw [eventually_iff] at hclose
    obtain ⟨ε, hε, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset (a := x)).1 hclose
    have hmax : max ε (x - δ) < x := max_lt hε (sub_lt_self x hδ)
    set y := (max ε (x - δ) + x) / 2
    have hyL : max ε (x - δ) < y := by
      unfold y
      linarith [hmax]
    have hyU : y < x := by
      unfold y
      linarith [hmax]
    have hyθ := hsub ⟨lt_of_le_of_lt (le_max_left _ _) hyL, hyU⟩
    have hpos : 0 < x - y := sub_pos.2 hyU
    have hlen : x - y < δ := by
      unfold y
      nlinarith [le_max_right ε (x - δ), hδ]
    have hvolI : volume (Icc y x) = ENNReal.ofReal (x - y) := Real.volume_Icc
    have hne0 : volume (Icc y x) ≠ 0 := by
      rw [hvolI, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hpos
    have hnetop : volume (Icc y x) ≠ ⊤ := by
      rw [hvolI]
      exact ENNReal.ofReal_ne_top
    have hgt : ENNReal.ofReal (θ * (x - y)) < volume (E ∩ Icc y x) := by
      have hmul := (ENNReal.lt_div_iff_mul_lt (Or.inl hne0) (Or.inl hnetop)).1 hyθ
      rw [hvolI, ← ENNReal.ofReal_mul (lt_of_le_of_lt hρ hθρ).le] at hmul
      exact hmul
    have hupper := volume_Icc_le_of_endpoint_ratio hρ hyU hlen hx hbound
    have hcmp : ENNReal.ofReal (ρ * (x - y)) < ENNReal.ofReal (θ * (x - y)) :=
      (ENNReal.ofReal_lt_ofReal_iff (mul_pos (lt_of_le_of_lt hρ hθρ) hpos)).2
        (mul_lt_mul_of_pos_right hθρ hpos)
    exact lt_irrefl _ (lt_trans (lt_of_lt_of_le hgt hupper) hcmp)
  have hnull : (volume.restrict E) {x | ¬ Tendsto (fun a => volume (E ∩ a) / volume a)
      (v.filterAt x) (𝓝 1)} = 0 := (ae_iff).1 hden
  have hsub : E ⊆ {x | ¬ Tendsto (fun a => volume (E ∩ a) / volume a)
      (v.filterAt x) (𝓝 1)} := fun x hx => hfail x hx
  have hle : volume E ≤ 0 := by
    rw [← Measure.restrict_apply_self]
    exact (measure_mono hsub).trans_eq hnull
  exact le_antisymm hle bot_le

/-- Each uniformly gapped set with `q < s < r < p` is null. -/
theorem volume_finiteGap_eq_zero (f : ℝ → ℝ) {p r s q : ℚ} {n : ℕ}
    (hqs : (q : ℝ) < s) (hsr : (s : ℝ) < r) (hrp : (r : ℝ) < p) :
    volume (finiteGap f p r s q n) = 0 := by
  set ρ : ℝ := (p - q) / ((p - q) + (r - s))
  have hρ : 0 ≤ ρ := div_nonneg (by linarith) (by linarith)
  have hρ1 : ρ < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  refine volume_eq_zero_of_short_ratio (δ := (1 : ℝ) / (n + 1)) (by positivity) hρ hρ1 ?_
  intro a b ha hb hab hlen
  exact finiteGap_volume_le f (by linarith) (by linarith) hab hlen ha hb

/-- Points at which a finite lower left derivative lies strictly below a finite upper right
derivative, witnessed by rational bounds. -/
def finiteStrict (f : ℝ → ℝ) : Set ℝ :=
  ⋃ p : ℚ, ⋃ r : ℚ, ⋃ s : ℚ, ⋃ q : ℚ, ⋃ n : ℕ,
    {x | (q : ℝ) < s ∧ (s : ℝ) < r ∧ (r : ℝ) < p ∧ x ∈ finiteGap f p r s q n}

/-- The finite strict gap between the lower left and upper right derivatives is null. -/
theorem volume_finiteStrict (f : ℝ → ℝ) : volume (finiteStrict f) = 0 := by
  rw [finiteStrict, measure_iUnion_null_iff]
  intro p
  rw [measure_iUnion_null_iff]
  intro r
  rw [measure_iUnion_null_iff]
  intro s
  rw [measure_iUnion_null_iff]
  intro q
  rw [measure_iUnion_null_iff]
  intro n
  by_cases h : (q : ℝ) < s ∧ (s : ℝ) < r ∧ (r : ℝ) < p
  · exact measure_mono_null (fun x hx => hx.2.2.2)
      (volume_finiteGap_eq_zero f h.1 h.2.1 h.2.2)
  · refine measure_mono_null ?_ (by simp : volume (∅ : Set ℝ) = 0)
    intro x hx
    exact absurd ⟨hx.1, hx.2.1, hx.2.2.1⟩ h

/-- A finite strict inequality `lowerLeft < upperRight` lies in `finiteStrict`. -/
lemma mem_finiteStrict_of_lt {f : ℝ → ℝ} {x : ℝ}
    (hURtop : upperRightDiniDerivative f x ≠ ⊤)
    (hURbot : upperRightDiniDerivative f x ≠ ⊥)
    (hLLtop : lowerLeftDiniDerivative f x ≠ ⊤)
    (hLLbot : lowerLeftDiniDerivative f x ≠ ⊥)
    (hlt : lowerLeftDiniDerivative f x < upperRightDiniDerivative f x) :
    x ∈ finiteStrict f := by
  have hUR : ((upperRightDiniDerivative f x).toReal : EReal) =
      upperRightDiniDerivative f x := EReal.coe_toReal hURtop hURbot
  have hLL : ((lowerLeftDiniDerivative f x).toReal : EReal) =
      lowerLeftDiniDerivative f x := EReal.coe_toReal hLLtop hLLbot
  have hltR : (lowerLeftDiniDerivative f x).toReal <
      (upperRightDiniDerivative f x).toReal := by
    rw [← EReal.coe_lt_coe_iff, hLL, hUR]
    exact hlt
  obtain ⟨q, hqL⟩ := exists_rat_lt (lowerLeftDiniDerivative f x).toReal
  obtain ⟨s, hsL, hsU⟩ := exists_rat_btwn hltR
  obtain ⟨r, hrL, hrU⟩ := exists_rat_btwn hsU
  obtain ⟨p, hpU⟩ := exists_rat_gt (upperRightDiniDerivative f x).toReal
  have hURlt : upperRightDiniDerivative f x < (p : ℝ) := by
    rw [← hUR]
    exact EReal.coe_lt_coe_iff.2 hpU
  have hLLgt : ((q : ℝ) : EReal) < lowerLeftDiniDerivative f x := by
    rw [← hLL]
    exact EReal.coe_lt_coe_iff.2 hqL
  have hR : ∀ᶠ h in 𝓝[>] (0 : ℝ), extendedDifferenceQuotient f x h < (p : ℝ) :=
    eventually_lt_of_limsup_lt hURlt (diniQuotient_bddAbove f x _)
  have hL : ∀ᶠ h in 𝓝[<] (0 : ℝ), (q : ℝ) < extendedDifferenceQuotient f x h :=
    eventually_lt_of_lt_liminf hLLgt (diniQuotient_bddBelow f x _)
  rw [eventually_iff] at hR hL
  obtain ⟨εR, hεR, hsubR⟩ := (mem_nhdsGT_iff_exists_Ioo_subset (a := (0 : ℝ))).1 hR
  obtain ⟨εL, hεL, hsubL⟩ := (mem_nhdsLT_iff_exists_Ioo_subset (a := (0 : ℝ))).1 hL
  have hmin : 0 < min εR (-εL) := lt_min hεR (neg_pos.2 hεL)
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / min εR (-εL))
  have hn0 : 0 < (n : ℝ) := (one_div_pos.2 hmin).trans hn
  have hδ : (1 : ℝ) / (n + 1) < min εR (-εL) := by
    have hstep : (1 : ℝ) / (n + 1) < 1 / n := by
      rw [one_div_lt_one_div (by linarith : (0 : ℝ) < (n : ℝ) + 1) hn0]
      linarith
    exact hstep.trans ((one_div_lt hmin hn0).1 hn)
  have hxGap : x ∈ finiteGap f p r s q n := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h hh0 hhδ
      have hmem : h ∈ Ioo (0 : ℝ) εR :=
        ⟨hh0, lt_of_le_of_lt hhδ (hδ.trans_le (min_le_left _ _))⟩
      have hquot := hsubR hmem
      unfold extendedDifferenceQuotient at hquot
      exact (EReal.coe_lt_coe_iff).1 hquot
    · intro h hhδ hh0
      have hδL : (1 : ℝ) / (n + 1) < -εL := hδ.trans_le (min_le_right _ _)
      have hge : εL < h := by
        have hε : εL < -((1 : ℝ) / (n + 1)) := by simpa using neg_lt_neg hδL
        have hlow : -((1 : ℝ) / (n + 1)) ≤ h := by
          rw [neg_div ((n : ℝ) + 1) (1 : ℝ)] at hhδ
          exact hhδ
        exact lt_of_lt_of_le hε hlow
      have hquot := hsubL ⟨hge, hh0⟩
      unfold extendedDifferenceQuotient at hquot
      exact (EReal.coe_lt_coe_iff).1 hquot
    · rw [← hUR]
      exact EReal.coe_lt_coe_iff.2 hrU
    · rw [← hLL]
      exact EReal.coe_lt_coe_iff.2 hsL
  have hqs : (q : ℝ) < s := hqL.trans hsL
  have hsr : (s : ℝ) < r := hrL
  have hrp : (r : ℝ) < p := hrU.trans hpU
  refine mem_iUnion.2 ⟨p, mem_iUnion.2 ⟨r, mem_iUnion.2 ⟨s, mem_iUnion.2 ⟨q,
    mem_iUnion.2 ⟨n, ⟨hqs, hsr, hrp, hxGap⟩⟩⟩⟩⟩⟩

end CKMA
