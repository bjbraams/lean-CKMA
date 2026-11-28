/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Order.Filter.Extr
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Riesz's rising sun lemma

Let `f` be continuous on `[c, b]`. Call a point `x` *shadowed* if some `y ∈ (x, b]` has
`f x < f y`. If every point of `(c, d)` is shadowed while no point of `(d, b]` rises above `f d`,
then `f` attains its maximum over `[c, d]` at `d`; in particular `f c ≤ f d`. This is the step of
F. Riesz's rising sun lemma that bounds `f` on each component interval of the shadowed set.

## Main results

* `CKMA.exists_first_isMaxOn_of_lt`: if `f x < f y` for some `y ∈ (x, b]`, then `f` has a
  leftmost maximizer `d` on `[x, b]`, with `x < d` and `f < f d` on `[x, d)`.
* `CKMA.risingSun_isMaxOn`: the rising sun inequality `f ≤ f d` on `[c, d]`.
-/

public section

namespace CKMA

open Set Filter Topology

/-- If some point of `(x, b]` rises above `f x`, then the continuous function `f` has a leftmost
maximizer `d` on `[x, b]`: it lies in `(x, b]`, rises above `f x`, and `f` stays strictly below
`f d` on `(x, d)`. -/
theorem exists_first_isMaxOn_of_lt {f : ℝ → ℝ} {b x : ℝ} (hf : ContinuousOn f (Icc x b))
    (hrise : ∃ y ∈ Ioc x b, f x < f y) :
    ∃ d ∈ Ioc x b, f x < f d ∧ IsMaxOn f (Icc x b) d ∧ ∀ z ∈ Ioo x d, f z < f d := by
  obtain ⟨y, hy, hfy⟩ := hrise
  obtain ⟨m, hm, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (hy.1.le.trans hy.2)) hf
  have hlt : f x < f m := hfy.trans_le (hmax ⟨hy.1.le, hy.2⟩)
  -- The leftmost point of `[x, m]` where the maximum value is attained.
  set S := Icc x m ∩ f ⁻¹' {f m}
  have hSclosed : IsClosed S :=
    (hf.mono (Icc_subset_Icc_right hm.2)).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_singleton
  have hSbdd : BddBelow S := ⟨x, fun _ hz => hz.1.1⟩
  have hdS : sInf S ∈ S := hSclosed.csInf_mem ⟨m, ⟨hm.1, le_rfl⟩, rfl⟩ hSbdd
  have hfd : f (sInf S) = f m := hdS.2
  have hxd : x < sInf S := lt_of_le_of_ne hdS.1.1 fun h => by
    rw [← h] at hfd
    exact hlt.ne hfd
  refine ⟨sInf S, ⟨hxd, hdS.1.2.trans hm.2⟩, hfd ▸ hlt, fun z hz => (hmax hz).trans_eq hfd.symm,
    fun z hz => ?_⟩
  have hzI : z ∈ Icc x m := ⟨hz.1.le, hz.2.le.trans hdS.1.2⟩
  refine ((hmax ⟨hzI.1, hzI.2.trans hm.2⟩).trans_eq hfd.symm).lt_of_ne fun heq => ?_
  exact (csInf_le hSbdd ⟨hzI, heq.trans hfd⟩).not_gt hz.2

/-- **Rising sun lemma.** Let `f` be continuous on `[c, b]` and `c < d ≤ b`. If every point of
`(c, d)` has a point of `(x, b]` with a larger value, and no point of `(d, b]` has a value larger
than `f d`, then `f ≤ f d` on `[c, d]`. -/
theorem risingSun_isMaxOn {f : ℝ → ℝ} {b c d : ℝ} (hf : ContinuousOn f (Icc c b))
    (hcd : c < d) (hdb : d ≤ b) (hU : ∀ x ∈ Ioo c d, ∃ y ∈ Ioc x b, f x < f y)
    (hd : ∀ y ∈ Ioc d b, f y ≤ f d) :
    IsMaxOn f (Icc c d) d := by
  have hopen : ∀ x ∈ Ioo c d, f x ≤ f d := by
    intro x hx
    obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (nonempty_Icc.2 (hx.2.le.trans hdb)) (hf.mono (Icc_subset_Icc_left hx.1.le))
    rcases lt_or_ge m d with hmd | hdm
    · -- A maximizer inside `(c, d)` would itself be shadowed.
      obtain ⟨y, hy, hfy⟩ := hU m ⟨hx.1.trans_le hm.1, hmd⟩
      exact absurd (hmax ⟨hm.1.trans hy.1.le, hy.2⟩) (not_le_of_gt hfy)
    · have hfm : f x ≤ f m := hmax ⟨le_rfl, hx.2.le.trans hdb⟩
      rcases hdm.eq_or_lt with rfl | hdm'
      · exact hfm
      · exact hfm.trans (hd m ⟨hdm', hm.2⟩)
  have hclosed : IsClosed (Icc c d ∩ f ⁻¹' Iic (f d)) :=
    (hf.mono (Icc_subset_Icc_right hdb)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hsub : Ioo c d ⊆ Icc c d ∩ f ⁻¹' Iic (f d) := fun x hx =>
    ⟨Ioo_subset_Icc_self hx, hopen x hx⟩
  intro x hx
  have hcl := closure_minimal hsub hclosed
  rw [closure_Ioo hcd.ne] at hcl
  exact (hcl hx).2

end CKMA
