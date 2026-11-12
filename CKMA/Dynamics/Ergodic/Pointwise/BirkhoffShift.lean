/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Order.Filter.AtTopBot.Basic

import Mathlib.Tactic

/-!
# Shift invariance of extended Birkhoff limsups

The identity `Aₙ₊₁(Tω) = ((n+2)/(n+1)) Aₙ₊₂(ω) - f(ω)/(n+1)` implies that the extended
limsup and liminf of the Birkhoff averages are strictly invariant.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology

variable {Ω : Type*}

/-- Shifting the index by one does not change the filter `atTop` on `ℕ`. -/
lemma map_add_one_atTop_eq_atTop : map (fun n : ℕ => n + 1) atTop = atTop := by
  refine map_atTop_eq_of_gc (fun m => m - 1) 1 (fun _ _ hab => Nat.add_le_add_right hab 1) ?_ ?_
  · intro a c hc
    constructor
    · intro h
      exact Nat.le_sub_of_add_le h
    · intro h
      exact Nat.add_le_of_le_sub hc h
  · intro c hc
    simp [Nat.sub_add_cancel hc]

/-- Every extended-real sequence is cobounded above. -/
lemma ereal_isCoboundedUnder_le {ι : Type*} (l : Filter ι) (u : ι → EReal) :
    l.IsCoboundedUnder (· ≤ ·) u := by
  unfold Filter.IsCoboundedUnder
  exact isCobounded_le_of_bot

/-- Every extended-real sequence is bounded above. -/
lemma ereal_isBoundedUnder_le {ι : Type*} (l : Filter ι) (u : ι → EReal) :
    l.IsBoundedUnder (· ≤ ·) u := by
  unfold Filter.IsBoundedUnder
  exact isBounded_le_of_top

/-- Every extended-real sequence is bounded below. -/
lemma ereal_isBoundedUnder_ge {ι : Type*} (l : Filter ι) (u : ι → EReal) :
    l.IsBoundedUnder (· ≥ ·) u := by
  unfold Filter.IsBoundedUnder
  exact isBounded_ge_of_bot

/-- The extended limsup is unchanged by discarding the first term. -/
lemma limsup_add_one {u : ℕ → EReal} :
    limsup (fun n => u (n + 1)) atTop = limsup u atTop := by
  have hcomp : (fun n => u (n + 1)) = u ∘ fun n => n + 1 := rfl
  simp only [Filter.limsup, hcomp]
  rw [← Filter.map_map, map_add_one_atTop_eq_atTop]

/-- The extended liminf is unchanged by discarding the first term. -/
lemma liminf_add_one {u : ℕ → EReal} :
    liminf (fun n => u (n + 1)) atTop = liminf u atTop := by
  have hcomp : (fun n => u (n + 1)) = u ∘ fun n => n + 1 := rfl
  simp only [Filter.liminf, hcomp]
  rw [← Filter.map_map, map_add_one_atTop_eq_atTop]

/-- Adding a real null sequence does not change the extended limsup of a real sequence. -/
lemma limsup_add_tendsto_zero {u z : ℕ → ℝ} (hz : Tendsto z atTop (𝓝 0)) :
    limsup (fun n => ((u n + z n : ℝ) : EReal)) atTop =
      limsup (fun n => (u n : EReal)) atTop := by
  have hzE : Tendsto (fun n => (z n : EReal)) atTop (𝓝 (0 : EReal)) :=
    (continuous_coe_real_ereal.tendsto 0).comp hz
  have hsup : limsup (fun n => (z n : EReal)) atTop = 0 := hzE.limsup_eq
  have hinf : liminf (fun n => (z n : EReal)) atTop = 0 := hzE.liminf_eq
  have hadd : (fun n => ((u n + z n : ℝ) : EReal)) =
      (fun n => (u n : EReal)) + fun n => (z n : EReal) := by
    ext n
    simp [EReal.coe_add]
  rw [hadd]
  apply le_antisymm
  · have hle := EReal.limsup_add_le (u := fun n => (u n : EReal))
        (v := fun n => (z n : EReal)) (f := atTop)
        (Or.inr (by simp [hsup])) (Or.inr (by simp [hsup]))
    simpa [hsup] using hle
  · have hge := EReal.le_limsup_add (u := fun n => (u n : EReal))
        (v := fun n => (z n : EReal)) (f := atTop)
    simpa [hinf] using hge

/-- If `1 ≤ cₙ → 1`, multiplication by `c` preserves the extended limsup of a real sequence. -/
lemma limsup_mul_tendsto_one {c u : ℕ → ℝ} (hc_ge : ∀ n, 1 ≤ c n)
    (hc : Tendsto c atTop (𝓝 1)) :
    limsup (fun n => ((c n * u n : ℝ) : EReal)) atTop =
      limsup (fun n => (u n : EReal)) atTop := by
  have hc_pos : ∀ n, 0 < c n := fun n => lt_of_lt_of_le zero_lt_one (hc_ge n)
  set U : ℕ → EReal := fun n => u n
  set V : ℕ → EReal := fun n => c n * u n
  apply le_antisymm
  · rw [limsup_le_iff]
    intro y hy
    cases y with
    | bot => exact (not_lt_bot hy).elim
    | top =>
      filter_upwards with n
      exact EReal.coe_lt_top _
    | coe q =>
      obtain ⟨b, hbU, hbq⟩ : ∃ b : ℝ, limsup U atTop < b ∧ b < q := by
        cases hL : limsup U atTop with
        | bot =>
          exact ⟨q - 1, by simpa [hL] using EReal.bot_lt_coe (q - 1), by linarith⟩
        | top => exact (not_top_lt (hL ▸ hy)).elim
        | coe a =>
          have haq : a < q := by
            have : (a : EReal) < q := by simpa [hL] using hy
            exact EReal.coe_lt_coe_iff.mp this
          obtain ⟨b, hab, hbq⟩ := exists_between haq
          exact ⟨b, by simpa [hL] using (EReal.coe_lt_coe hab), hbq⟩
      have hult : ∀ᶠ n in atTop, u n < b := by
        have hb : limsup U atTop < (b : EReal) := hbU
        filter_upwards [eventually_lt_of_limsup_lt hb] with n hn
        exact EReal.coe_lt_coe_iff.mp hn
      by_cases hb0 : b ≤ 0
      · filter_upwards [hult] with n hn
        have hu0 : u n < 0 := lt_of_lt_of_le hn hb0
        have hcu : c n * u n ≤ u n := by
          have hnonpos : (c n - 1) * u n ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hc_ge n)) hu0.le
          linarith
        have : ((c n * u n : ℝ) : EReal) < q := by
          exact EReal.coe_lt_coe (lt_of_le_of_lt hcu (hn.trans hbq))
        simpa [V] using this
      · have hbpos : 0 < b := lt_of_not_ge hb0
        have hcb : Tendsto (fun n => c n * b) atTop (𝓝 b) := by
          simpa using hc.mul tendsto_const_nhds
        have hcb_lt : ∀ᶠ n in atTop, c n * b < q :=
          hcb.eventually (Iio_mem_nhds hbq)
        filter_upwards [hult, hcb_lt] with n hn hcbn
        by_cases hu : u n ≤ 0
        · have hcu : c n * u n ≤ u n := by
            have hnonpos : (c n - 1) * u n ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hc_ge n)) hu
            linarith
          have : ((c n * u n : ℝ) : EReal) < q :=
            EReal.coe_lt_coe (lt_of_le_of_lt hcu (hn.trans hbq))
          simpa [V] using this
        · have hupos : 0 < u n := lt_of_not_ge hu
          have hmul : c n * u n < c n * b := mul_lt_mul_of_pos_left hn (hc_pos n)
          have : ((c n * u n : ℝ) : EReal) < q := EReal.coe_lt_coe (hmul.trans hcbn)
          simpa [V] using this
  · rw [le_limsup_iff]
    intro y hy
    cases hL : limsup U atTop with
    | bot => exact (not_lt_bot (hL ▸ hy)).elim
    | top =>
      cases y with
      | bot =>
        exact (Eventually.of_forall fun n => EReal.bot_lt_coe (c n * u n)).frequently
      | top => exact (not_top_lt (hL ▸ hy)).elim
      | coe q =>
        have hlt : ((max q 0 + 1 : ℝ) : EReal) < limsup U atTop := by
          simpa [hL] using EReal.coe_lt_top (max q 0 + 1 : ℝ)
        have hfreq : ∃ᶠ n in atTop, ((max q 0 + 1 : ℝ) : EReal) < U n :=
          frequently_lt_of_lt_limsup (hu := ereal_isCoboundedUnder_le _ _) hlt
        refine hfreq.mono fun n hn => ?_
        have hu : max q 0 + 1 < u n := EReal.coe_lt_coe_iff.mp hn
        have hpos : 0 < u n := by
          have h1 : (1 : ℝ) ≤ max q 0 + 1 := by
            have : (0 : ℝ) ≤ max q 0 := le_max_right _ _
            linarith
          linarith
        have hcu : u n ≤ c n * u n := by
          nlinarith [hc_ge n, hpos]
        have hq : q < c n * u n := by
          have hqle : q ≤ max q 0 := le_max_left _ _
          linarith
        simpa [V] using (EReal.coe_lt_coe hq)
    | coe a =>
      cases y with
      | bot =>
        exact (Eventually.of_forall fun n => EReal.bot_lt_coe (c n * u n)).frequently
      | top => exact (not_top_lt (hL ▸ hy)).elim
      | coe q =>
        have hqa : q < a := by
          have : (q : EReal) < a := by simpa [hL] using hy
          exact EReal.coe_lt_coe_iff.mp this
        obtain ⟨z, hqz, hza⟩ := exists_between hqa
        have hfreq : ∃ᶠ n in atTop, (z : EReal) < U n := by
          have : (z : EReal) < limsup U atTop := by simpa [hL] using EReal.coe_lt_coe hza
          exact frequently_lt_of_lt_limsup (hu := ereal_isCoboundedUnder_le _ _) this
        have hcz : Tendsto (fun n => c n * z) atTop (𝓝 z) := by
          simpa using hc.mul tendsto_const_nhds
        have hev : ∀ᶠ n in atTop, q < c n * z := hcz.eventually (Ioi_mem_nhds hqz)
        refine (hfreq.and_eventually hev).mono fun n hn => ?_
        have huz : z < u n := EReal.coe_lt_coe_iff.mp hn.1
        have hmul : c n * z < c n * u n := mul_lt_mul_of_pos_left huz (hc_pos n)
        simpa [V] using (EReal.coe_lt_coe (lt_trans hn.2 hmul))

section Pointwise

variable {T : Ω → Ω} {f : Ω → ℝ}

/-- The one-step relation between a Birkhoff average and its image. -/
lemma birkhoffAverage_succ_comp (n : ℕ) (ω : Ω) :
    birkhoffAverage ℝ T f (n + 1) (T ω) =
      ((n + 2 : ℝ) / (n + 1)) * birkhoffAverage ℝ T f (n + 2) ω - f ω / (n + 1) := by
  have hS : birkhoffSum T f (n + 2) ω = f ω + birkhoffSum T f (n + 1) (T ω) :=
    birkhoffSum_succ_apply' T f (n + 1) ω
  unfold birkhoffAverage
  simp only [smul_eq_mul]
  push_cast
  set a : ℝ := (n : ℝ) + 1
  set b : ℝ := (n : ℝ) + 2
  set s : ℝ := birkhoffSum T f (n + 1) (T ω)
  set t : ℝ := birkhoffSum T f (n + 2) ω
  have hn : a ≠ 0 := by
    have : (0 : ℝ) < a := by positivity
    exact this.ne'
  have hn2 : b ≠ 0 := by
    have : (0 : ℝ) < b := by positivity
    exact this.ne'
  have hs : s = t - f ω := by
    have ht : t = f ω + s := hS
    linarith
  rw [hs, mul_sub, div_eq_mul_inv, div_eq_mul_inv]
  have hcoeff : (b * a⁻¹) * (b⁻¹ * t) = a⁻¹ * t := by
    calc
      (b * a⁻¹) * (b⁻¹ * t) = b * (a⁻¹ * (b⁻¹ * t)) := mul_assoc _ _ _
      _ = b * ((a⁻¹ * b⁻¹) * t) :=
        congr_arg (fun x => b * x) (mul_assoc a⁻¹ b⁻¹ t).symm
      _ = b * ((b⁻¹ * a⁻¹) * t) :=
        congr_arg (fun x => b * (x * t)) (mul_comm _ _)
      _ = b * (b⁻¹ * (a⁻¹ * t)) :=
        congr_arg (fun x => b * x) (mul_assoc b⁻¹ a⁻¹ t)
      _ = (b * b⁻¹) * (a⁻¹ * t) := (mul_assoc b b⁻¹ (a⁻¹ * t)).symm
      _ = 1 * (a⁻¹ * t) := congr_arg (fun x => x * (a⁻¹ * t)) (mul_inv_cancel₀ hn2)
      _ = a⁻¹ * t := one_mul _
  rw [hcoeff, mul_comm (f ω) a⁻¹]

/-- The coefficient relating a Birkhoff average to the average at the image point. -/
def birkhoffCoeff (n : ℕ) : ℝ := (n + 2 : ℝ) / (n + 1)

/-- The coefficient `(n+2)/(n+1)` stays at least `1`. -/
lemma one_le_birkhoffCoeff (n : ℕ) : 1 ≤ birkhoffCoeff n := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [birkhoffCoeff, le_div_iff₀ hn]
  linarith

/-- The coefficient `(n+2)/(n+1)` tends to `1`. -/
lemma tendsto_birkhoffCoeff : Tendsto birkhoffCoeff atTop (𝓝 1) := by
  have hnat : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hreal : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
    have heq : (fun n : ℕ => (n + 1 : ℝ)) = fun n => ((n + 1 : ℕ) : ℝ) := by
      ext n
      simp
    simpa [heq] using hnat
  have hinv : Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hreal
  have hform : birkhoffCoeff = fun n : ℕ => 1 + (n + 1 : ℝ)⁻¹ := by
    ext n
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    unfold birkhoffCoeff
    field_simp [hn]
    ring
  rw [hform]
  have hsum := (tendsto_const_nhds (x := (1 : ℝ))).add hinv
  simpa [add_zero] using hsum

/-- Extended limsup of the Birkhoff averages at `ω`. -/
def birkhoffLimsup (T : Ω → Ω) (f : Ω → ℝ) (ω : Ω) : EReal :=
  limsup (fun n => Real.toEReal (birkhoffAverage ℝ T f n ω)) atTop

/-- Extended liminf of the Birkhoff averages at `ω`. -/
def birkhoffLiminf (T : Ω → Ω) (f : Ω → ℝ) (ω : Ω) : EReal :=
  liminf (fun n => Real.toEReal (birkhoffAverage ℝ T f n ω)) atTop

/-- The extended limsup of the averages is unchanged by one application of `T`. -/
lemma birkhoffLimsup_comp (ω : Ω) : birkhoffLimsup T f (T ω) = birkhoffLimsup T f ω := by
  unfold birkhoffLimsup
  rw [← limsup_add_one (u := fun n => Real.toEReal (birkhoffAverage ℝ T f n (T ω)))]
  have hnat : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hreal : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
    have heq : (fun n : ℕ => (n + 1 : ℝ)) = fun n => ((n + 1 : ℕ) : ℝ) := by
      ext n
      simp
    simpa [heq] using hnat
  have herr : Tendsto (fun n : ℕ => -(f ω) / (n + 1 : ℝ)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hreal
    have hmul := (tendsto_const_nhds (x := -(f ω))).mul hinv
    simpa [div_eq_mul_inv, mul_zero] using hmul
  have hshift : limsup (fun n => Real.toEReal (birkhoffAverage ℝ T f (n + 1) (T ω))) atTop =
      limsup (fun n => Real.toEReal (birkhoffAverage ℝ T f (n + 2) ω)) atTop := by
    have hfun : (fun n => Real.toEReal (birkhoffAverage ℝ T f (n + 1) (T ω))) =
        fun n => Real.toEReal (birkhoffCoeff n * birkhoffAverage ℝ T f (n + 2) ω +
          -(f ω) / (n + 1)) := by
      ext n
      have havg := birkhoffAverage_succ_comp (T := T) (f := f) n ω
      have hcoeff : (n + 2 : ℝ) / (n + 1) = birkhoffCoeff n := rfl
      rw [havg, hcoeff]
      congr 1
      ring
    rw [hfun, limsup_add_tendsto_zero herr]
    exact limsup_mul_tendsto_one (u := fun n => birkhoffAverage ℝ T f (n + 2) ω)
      one_le_birkhoffCoeff tendsto_birkhoffCoeff
  rw [hshift]
  exact (limsup_add_one (u := fun n => Real.toEReal (birkhoffAverage ℝ T f (n + 1) ω))).trans
    (limsup_add_one (u := fun n => Real.toEReal (birkhoffAverage ℝ T f n ω)))

/-- Negating the observable negates the extended liminf into an extended limsup. -/
lemma birkhoffLiminf_neg (ω : Ω) :
    birkhoffLiminf T f ω = -birkhoffLimsup T (-f) ω := by
  unfold birkhoffLiminf birkhoffLimsup
  have hfun : (fun n => Real.toEReal (birkhoffAverage ℝ T f n ω)) =
      fun n => -Real.toEReal (birkhoffAverage ℝ T (-f) n ω) := by
    ext n
    rw [birkhoffAverage_neg_apply, EReal.coe_neg]
    exact (neg_neg _).symm
  rw [hfun]
  exact EReal.liminf_neg (v := fun n => Real.toEReal (birkhoffAverage ℝ T (-f) n ω))
    (f := atTop)

/-- The extended liminf of the averages is unchanged by one application of `T`. -/
lemma birkhoffLiminf_comp (ω : Ω) : birkhoffLiminf T f (T ω) = birkhoffLiminf T f ω := by
  rw [birkhoffLiminf_neg, birkhoffLiminf_neg, birkhoffLimsup_comp]

end Pointwise

end CKMA
