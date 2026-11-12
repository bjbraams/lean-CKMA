/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.Sequences

/-!
# Riesz rising sun lemma

On a compact interval, a continuous real function attains a rightmost maximum on every
right-hand subinterval. A strict rise stops at the first point where that maximum value
is attained, and the function stays strictly below the maximum on the intervening segment.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Set Filter Topology

/-- A rightmost maximum of `f` on `[x, b]`. -/
structure RightmostMaximum (f : ℝ → ℝ) (x b : ℝ) where
  /-- The location of the maximum. -/
  point : ℝ
  /-- The maximizer lies in the interval. -/
  mem : point ∈ Icc x b
  /-- No point of the interval has a larger value. -/
  isMax : IsMaxOn f (Icc x b) point
  /-- Every other maximizer lies at most as far to the right. -/
  rightmost : ∀ z ∈ Icc x b, IsMaxOn f (Icc x b) z → z ≤ point

/-- A continuous function on a compact interval has a rightmost maximum on `[x, b]`. -/
theorem exists_rightmostMaximum {f : ℝ → ℝ} {a b x : ℝ} (hf : ContinuousOn f (Icc a b))
    (hx : x ∈ Icc a b) : Nonempty (RightmostMaximum f x b) := by
  have hxb : x ≤ b := hx.2
  have hcompact : IsCompact (Icc x b) := isCompact_Icc
  have hcont : ContinuousOn f (Icc x b) := hf.mono (Icc_subset_Icc_left hx.1)
  obtain ⟨m, hm, hmax⟩ := hcompact.exists_isMaxOn (nonempty_Icc.2 hxb) hcont
  let M : Set ℝ := {z ∈ Icc x b | IsMaxOn f (Icc x b) z}
  have hMsub : M ⊆ Icc x b := fun _ hz => hz.1
  have hMne : M.Nonempty := ⟨m, hm, hmax⟩
  have hMclosed : IsClosed M := by
    refine IsSeqClosed.isClosed ?_
    intro u z hu htend
    have huz : ∀ n, u n ∈ Icc x b := fun n => (hu n).1
    have hzI : z ∈ Icc x b :=
      isClosed_Icc.mem_of_tendsto htend (Eventually.of_forall huz)
    have hfu : Tendsto (fun n => f (u n)) atTop (𝓝 (f z)) :=
      (hcont z hzI).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨htend, Eventually.of_forall huz⟩)
    have heq : ∀ n, f (u n) = f m := fun n =>
      le_antisymm (hmax (hu n).1) ((hu n).2 hm)
    have hfum : Tendsto (fun n => f (u n)) atTop (𝓝 (f m)) := by
      have hconst : (fun n => f (u n)) = fun _ => f m := funext heq
      simp [hconst]
    have hfz : f z = f m := tendsto_nhds_unique hfu hfum
    refine ⟨hzI, ?_⟩
    intro w hw
    exact (hmax hw).trans_eq hfz.symm
  have hMcomp : IsCompact M := hcompact.of_isClosed_subset hMclosed hMsub
  obtain ⟨y, hyM, hyright⟩ := hMcomp.exists_isMaxOn hMne continuous_id.continuousOn
  exact ⟨{
    point := y
    mem := hyM.1
    isMax := hyM.2
    rightmost := fun z hz hmaxz => hyright ⟨hz, hmaxz⟩
  }⟩

/-- **Rising sun lemma.** A strict rise of a continuous function on `[a, b]` ends at the first
point where the rightmost maximum value is attained. On the open segment before that point the
function stays strictly below the maximum, and nothing to the right exceeds it. -/
theorem risingSun_rightmost {f : ℝ → ℝ} {a b x : ℝ} (hf : ContinuousOn f (Icc a b))
    (hx : x ∈ Ico a b) (hrise : ∃ y ∈ Ioc x b, f x < f y) :
    ∃ d ∈ Ioc x b, f x < f d ∧ (∀ z ∈ Icc x b, f z ≤ f d) ∧
      (∀ z ∈ Ioo x d, f z < f d) ∧ (∀ w ∈ Ioc d b, f w ≤ f d) := by
  have hxI : x ∈ Icc a b := ⟨hx.1, hx.2.le⟩
  obtain ⟨R⟩ := exists_rightmostMaximum hf hxI
  have hlt : f x < f R.point := by
    obtain ⟨y, hy, hfy⟩ := hrise
    exact hfy.trans_le (R.isMax ⟨hy.1.le, hy.2⟩)
  have hxd : x < R.point := by
    refine lt_of_le_of_ne R.mem.1 ?_
    intro hxr
    exact absurd hlt (by simp [hxr])
  let S : Set ℝ := {z ∈ Icc x R.point | f z = f R.point}
  have hSne : S.Nonempty := ⟨R.point, right_mem_Icc.2 hxd.le, rfl⟩
  have hSclosed : IsClosed S := by
    refine IsSeqClosed.isClosed ?_
    intro u z hu htend
    have huz : ∀ n, u n ∈ Icc x R.point := fun n => (hu n).1
    have hzI : z ∈ Icc x R.point :=
      isClosed_Icc.mem_of_tendsto htend (Eventually.of_forall huz)
    have hcont : ContinuousOn f (Icc x R.point) :=
      hf.mono (Icc_subset_Icc hx.1 R.mem.2)
    have hfu : Tendsto (fun n => f (u n)) atTop (𝓝 (f z)) :=
      (hcont z hzI).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨htend, Eventually.of_forall huz⟩)
    have heq : ∀ n, f (u n) = f R.point := fun n => (hu n).2
    have hconst : Tendsto (fun n => f (u n)) atTop (𝓝 (f R.point)) := by
      have hfun : (fun n => f (u n)) = fun _ => f R.point := funext heq
      simp [hfun]
    exact ⟨hzI, tendsto_nhds_unique hfu hconst⟩
  have hSbdd : BddBelow S := ⟨x, fun _ hz => hz.1.1⟩
  have hdmem : sInf S ∈ S := hSclosed.csInf_mem hSne hSbdd
  refine ⟨sInf S, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨(lt_of_le_of_ne hdmem.1.1 (fun h => by
      have : f x = f R.point := by simpa [h] using hdmem.2
      exact lt_irrefl _ (this ▸ hlt))), hdmem.1.2.trans R.mem.2⟩
  · simpa [hdmem.2] using hlt
  · intro z hz
    exact (R.isMax hz).trans_eq hdmem.2.symm
  · intro z hz
    have hzI : z ∈ Icc x R.point := ⟨hz.1.le, hz.2.le.trans hdmem.1.2⟩
    have hle : f z ≤ f (sInf S) :=
      (R.isMax ⟨hzI.1, hzI.2.trans R.mem.2⟩).trans_eq hdmem.2.symm
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hzS : z ∈ S := ⟨hzI, heq.trans hdmem.2⟩
    exact not_lt_of_ge (csInf_le hSbdd hzS) hz.2
  · intro w hw
    have hwI : w ∈ Icc x b := ⟨hdmem.1.1.trans hw.1.le, hw.2⟩
    exact (R.isMax hwI).trans_eq hdmem.2.symm

end CKMA
