/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.Flow
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Dynamics.OmegaLimit
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Order.Filter.AtTopBot.Group
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Lyapunov stability and LaSalle invariance (31.24, 31.26)

The derivative `lyapunovDerivative` is evaluated along an explicit generator of an
existing global flow. The local positive-definite criteria imply metric stability and,
for a strictly decreasing function, local attraction. Finite dimension supplies the
compactness needed for these local criteria.

LaSalle's principle uses a compact positively invariant set and the largest full-flow
invariant subset of the zero-derivative locus. It makes no finiteness assumption on the
rest set. Common flow, stability and invariant-subset definitions are in `CKMA.Dynamics.Flow`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Metric Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Derivative of `V` along the vector field. -/
def lyapunovDerivative (F : E → E) (V : E → ℝ) (x : E) : ℝ := fderiv ℝ V x (F x)

/-- Chain rule for `V` along an orbit while the state lies in the ball of differentiability. -/
private theorem hasDerivAt_comp_lyapunov_ball {ϕ : Flow ℝ E} {F : E → E} {V : E → ℝ} {x₀ x : E}
    {r t : ℝ} (hflow : FlowHasGenerator ϕ F) (hV : ContDiffOn ℝ 1 V (ball x₀ r))
    (ht : ϕ t x ∈ ball x₀ r) :
    HasDerivAt (fun s ↦ V (ϕ s x)) (lyapunovDerivative F V (ϕ t x)) t := by
  have hFd : HasFDerivAt V (fderiv ℝ V (ϕ t x)) (ϕ t x) :=
    hV.differentiableOn_one.hasFDerivAt (isOpen_ball.mem_nhds ht)
  exact hFd.comp_hasDerivAt t (hflow x t)

/-- Chain rule for `V` along an orbit when `V` is continuously differentiable on the whole space. -/
private theorem hasDerivAt_comp_lyapunov {ϕ : Flow ℝ E} {F : E → E} {V : E → ℝ} {x : E} {t : ℝ}
    (hflow : FlowHasGenerator ϕ F) (hV : ContDiff ℝ 1 V) :
    HasDerivAt (fun s ↦ V (ϕ s x)) (lyapunovDerivative F V (ϕ t x)) t := by
  have hFd : HasFDerivAt V (fderiv ℝ V (ϕ t x)) (ϕ t x) :=
    hV.differentiable_one.differentiableAt.hasFDerivAt
  exact hFd.comp_hasDerivAt t (hflow x t)

omit [NormedSpace ℝ E] in
/-- A positive-definite function vanishing at the centre is nonnegative on the ball. -/
private theorem lyapunov_nonneg_on_ball {V : E → ℝ} {x₀ : E} {r : ℝ} (hV₀ : V x₀ = 0)
    (hpos : ∀ x ∈ ball x₀ r, x ≠ x₀ → 0 < V x) {x : E} (hx : x ∈ ball x₀ r) : 0 ≤ V x := by
  rcases eq_or_ne x x₀ with rfl | hx0
  · simp [hV₀]
  · exact (hpos x hx hx0).le

/-- The Lyapunov derivative vanishes at an equilibrium interior to the ball of differentiability. -/
private theorem lyapunovDerivative_eq_zero_of_fixed {ϕ : Flow ℝ E} {F : E → E} {V : E → ℝ}
    {x₀ : E} {r : ℝ} (hflow : FlowHasGenerator ϕ F) (heq : ∀ t, ϕ t x₀ = x₀)
    (hV : ContDiffOn ℝ 1 V (ball x₀ r)) (hr : 0 < r) : lyapunovDerivative F V x₀ = 0 := by
  have hx₀ : x₀ ∈ ball x₀ r := mem_ball_self hr
  have hder := hasDerivAt_comp_lyapunov_ball (x := x₀) (t := 0) hflow hV
    (by simpa [heq 0] using hx₀)
  have hconst : HasDerivAt (fun t ↦ V (ϕ t x₀)) 0 0 := by
    have hfun : (fun t ↦ V (ϕ t x₀)) = fun _ ↦ V x₀ := by
      funext t
      rw [heq t]
    rw [hfun]
    exact hasDerivAt_const 0 (V x₀)
  simpa [heq 0] using hder.unique hconst

/-- On times whose orbit segment stays in the ball, nonpositive derivative makes `V` antitone. -/
private theorem antitoneOn_comp_lyapunov_ball {ϕ : Flow ℝ E} {F : E → E} {V : E → ℝ} {x₀ x : E}
    {r : ℝ} (hflow : FlowHasGenerator ϕ F) (hV : ContDiffOn ℝ 1 V (ball x₀ r))
    (hdec : ∀ y ∈ ball x₀ r, lyapunovDerivative F V y ≤ 0) {D : Set ℝ} (hD : Convex ℝ D)
    (hstay : ∀ t ∈ D, ϕ t x ∈ ball x₀ r) : AntitoneOn (fun t ↦ V (ϕ t x)) D := by
  refine antitoneOn_of_deriv_nonpos hD ?_ ?_ ?_
  · exact hV.continuousOn.comp (ϕ.continuous continuous_id continuous_const).continuousOn hstay
  · intro t ht
    exact (hasDerivAt_comp_lyapunov_ball hflow hV
      (hstay t (interior_subset ht))).differentiableAt.differentiableWithinAt
  · intro t ht
    have hmem : ϕ t x ∈ ball x₀ r := hstay t (interior_subset ht)
    rw [(hasDerivAt_comp_lyapunov_ball hflow hV hmem).deriv]
    exact hdec _ hmem

/-- Global nonpositive Lyapunov derivative makes `V` antitone on any convex set of times. -/
private theorem antitoneOn_comp_lyapunov {ϕ : Flow ℝ E} {F : E → E} {V : E → ℝ} {x : E}
    (hflow : FlowHasGenerator ϕ F) (hV : ContDiff ℝ 1 V) {D : Set ℝ} (hD : Convex ℝ D)
    (hdec : ∀ t ∈ interior D, lyapunovDerivative F V (ϕ t x) ≤ 0) :
    AntitoneOn (fun t ↦ V (ϕ t x)) D := by
  refine antitoneOn_of_deriv_nonpos hD ?_ ?_ ?_
  · exact (hV.continuous.comp (ϕ.continuous continuous_id continuous_const)).continuousOn
  · intro _ _
    exact (hasDerivAt_comp_lyapunov hflow hV).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hasDerivAt_comp_lyapunov hflow hV).deriv]
    exact hdec t ht

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- An antitone function on the nonnegative reals, bounded below there, converges at infinity. -/
private theorem tendsto_atTop_of_antitoneOn_Ici {f : ℝ → ℝ} (hf : AntitoneOn f (Ici 0))
    (hbdd : BddBelow (f '' Ici 0)) :
    ∃ c, Tendsto f atTop (nhds c) ∧ ∀ t, 0 ≤ t → c ≤ f t := by
  classical
  let g : ℝ → ℝ := fun t ↦ if 0 ≤ t then f t else f 0
  have hg_anti : Antitone g := by
    intro a b hab
    by_cases hb : 0 ≤ b
    · by_cases ha : 0 ≤ a
      · rw [show g b = f b from ite_eq_left hb, show g a = f a from ite_eq_left ha]
        exact hf ha hb hab
      · rw [show g b = f b from ite_eq_left hb, show g a = f 0 from ite_eq_right ha]
        exact hf (show (0 : ℝ) ∈ Ici 0 from le_rfl) hb hb
    · have ha : ¬0 ≤ a := fun ha ↦ hb (ha.trans hab)
      rw [show g b = f 0 from ite_eq_right hb, show g a = f 0 from ite_eq_right ha]
  obtain ⟨c₀, hc₀⟩ := hbdd
  have hg_bdd : BddBelow (range g) := by
    refine ⟨c₀, ?_⟩
    rintro _ ⟨t, rfl⟩
    by_cases ht : 0 ≤ t
    · dsimp only [g]
      rw [ite_eq_left ht]
      exact hc₀ ⟨t, ht, rfl⟩
    · dsimp only [g]
      rw [ite_eq_right ht]
      exact hc₀ ⟨0, le_rfl, rfl⟩
  have htend_g : Tendsto g atTop (nhds (⨅ t, g t)) := tendsto_atTop_ciInf hg_anti hg_bdd
  refine ⟨⨅ t, g t, ?_, ?_⟩
  · refine htend_g.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact ite_eq_left ht
  · intro t ht
    have hineq : (⨅ s, g s) ≤ g t := ciInf_le hg_bdd t
    rwa [show g t = f t from ite_eq_left ht] at hineq

/-- **31.24**: the non-strict Lyapunov criterion, stated for an existing flow.
Local ODE construction and continuation are not conclusions of this interface. -/
theorem isLyapunovStable_of_lyapunov [FiniteDimensional ℝ E]
    (ϕ : Flow ℝ E) (F : E → E) (V : E → ℝ) (x₀ : E)
    (hflow : FlowHasGenerator ϕ F)
    (_heq : ∀ t, ϕ t x₀ = x₀) {r : ℝ} (hr : 0 < r)
    (hV : ContDiffOn ℝ 1 V (Metric.ball x₀ r)) (hV₀ : V x₀ = 0)
    (hpos : ∀ x ∈ Metric.ball x₀ r, x ≠ x₀ → 0 < V x)
    (hdec : ∀ x ∈ Metric.ball x₀ r, lyapunovDerivative F V x ≤ 0) :
    IsLyapunovStable ϕ x₀ := by
  intro ε hε
  by_cases hnt : Nontrivial E
  · let eps : ℝ := min ε (r / 2)
    have heps_pos : 0 < eps := lt_min hε (half_pos hr)
    have heps_lt : eps < r := (min_le_right ε (r / 2)).trans_lt (half_lt_self hr)
    have heps_le : eps ≤ ε := min_le_left _ _
    have hshell_ne : (sphere x₀ eps).Nonempty := by
      obtain ⟨v, hv⟩ := @exists_ne E hnt (0 : E)
      have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
      refine ⟨x₀ + (eps / ‖v‖) • v, ?_⟩
      rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg (div_nonneg heps_pos.le (norm_nonneg v)),
        div_mul_cancel₀ _ (ne_of_gt hv_pos)]
    have hshell_sub : sphere x₀ eps ⊆ ball x₀ r := by
      intro y hy
      rw [mem_ball, mem_sphere.mp hy]
      exact heps_lt
    obtain ⟨yMin, hyMin, hmin⟩ :=
      (isCompact_sphere x₀ eps).exists_isMinOn hshell_ne (hV.continuousOn.mono hshell_sub)
    set m : ℝ := V yMin
    have hm_pos : 0 < m := by
      refine hpos yMin (hshell_sub hyMin) ?_
      intro hy
      rw [mem_sphere, hy, dist_self] at hyMin
      linarith
    have hcont₀ : ContinuousAt V x₀ :=
      hV.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))
    obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := Metric.continuousAt_iff.mp hcont₀ m hm_pos
    refine ⟨min δ₀ eps, lt_min hδ₀_pos heps_pos, ?_⟩
    intro x hx t ht
    have hxδ₀ : dist x x₀ < δ₀ := lt_of_lt_of_le hx (min_le_left _ _)
    have hxeps : dist x x₀ < eps := lt_of_lt_of_le hx (min_le_right _ _)
    have hVx : V x < m := by
      have hdistV : dist (V x) (V x₀) < m := hδ₀ hxδ₀
      rw [hV₀, dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_lt] at hdistV
      exact hdistV.2
    suffices hclose : dist (ϕ t x) x₀ < eps from lt_of_lt_of_le hclose heps_le
    by_contra hge
    have hge : eps ≤ dist (ϕ t x) x₀ := le_of_not_gt hge
    let g : ℝ → ℝ := fun s ↦ dist (ϕ s x) x₀
    have hgcont : Continuous g :=
      (ϕ.continuous continuous_id continuous_const).dist continuous_const
    let escape : Set ℝ := Icc 0 t ∩ g ⁻¹' Ici eps
    have hesc_closed : IsClosed escape :=
      isClosed_Icc.inter (isClosed_Ici.preimage hgcont)
    have hesc_ne : escape.Nonempty := ⟨t, ⟨ht, le_rfl⟩, hge⟩
    obtain ⟨T, hT, hTmin⟩ :=
      (isCompact_Icc.of_isClosed_subset hesc_closed inter_subset_left).exists_isMinOn hesc_ne
        continuous_id.continuousOn
    have hT0 : 0 ≤ T := hT.1.1
    have hTt : T ≤ t := hT.1.2
    have hTg : eps ≤ g T := hT.2
    have hTpos : 0 < T := by
      by_contra hle
      have hTeq : T = 0 := le_antisymm (le_of_not_gt hle) hT0
      have hge0 : eps ≤ dist x x₀ := by
        have : eps ≤ g 0 := by simpa [hTeq, g, ϕ.map_zero_apply] using hTg
        simpa [g, ϕ.map_zero_apply] using this
      exact lt_irrefl _ (hxeps.trans_le hge0)
    have hgT_le : g T ≤ eps := by
      by_contra hgt
      have hgt : eps < g T := lt_of_not_ge hgt
      obtain ⟨η, hη_pos, hη⟩ :=
        Metric.continuousAt_iff.mp hgcont.continuousAt (g T - eps) (sub_pos.mpr hgt)
      set d : ℝ := min (η / 2) (T / 2)
      have hd_pos : 0 < d := lt_min (half_pos hη_pos) (half_pos hTpos)
      set s : ℝ := T - d
      have hs_lt : s < T := sub_lt_self _ hd_pos
      have hs0 : 0 ≤ s := by
        have hd_le : d ≤ T / 2 := min_le_right _ _
        linarith
      have hs_dist : dist s T < η := by
        rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hs_lt)]
        have hd_lt : d ≤ η / 2 := min_le_left _ _
        linarith [half_lt_self hη_pos]
      have hgs : eps < g s := by
        have hclose_g : dist (g s) (g T) < g T - eps := hη hs_dist
        rw [Real.dist_eq, abs_lt] at hclose_g
        linarith
      have hs_mem : s ∈ escape := ⟨⟨hs0, hs_lt.le.trans hTt⟩, hgs.le⟩
      have hTle : T ≤ s := hTmin hs_mem
      exact lt_irrefl _ (hs_lt.trans_le hTle)
    have hgT_eq : g T = eps := le_antisymm hgT_le hTg
    have hgle : ∀ s ∈ Icc 0 T, g s ≤ eps := by
      intro s hs
      by_contra hgt
      have hgt : eps < g s := lt_of_not_ge hgt
      have hs_mem : s ∈ escape := ⟨⟨hs.1, hs.2.trans hTt⟩, hgt.le⟩
      have hsT : s = T := le_antisymm hs.2 (hTmin hs_mem)
      rw [hsT, hgT_eq] at hgt
      exact lt_irrefl _ hgt
    have hstay : ∀ s ∈ Icc 0 T, ϕ s x ∈ ball x₀ r := by
      intro s hs
      rw [mem_ball]
      exact (hgle s hs).trans_lt heps_lt
    have hanti : AntitoneOn (fun s ↦ V (ϕ s x)) (Icc 0 T) :=
      antitoneOn_comp_lyapunov_ball hflow hV hdec (convex_Icc 0 T) hstay
    have hVle : V (ϕ T x) ≤ V x := by
      simpa [ϕ.map_zero_apply] using hanti ⟨le_rfl, hT0⟩ ⟨hT0, le_rfl⟩ hT0
    have hVge : m ≤ V (ϕ T x) := hmin (mem_sphere.mpr hgT_eq)
    linarith
  · have hsub : Subsingleton E := not_nontrivial_iff_subsingleton.mp hnt
    refine ⟨1, one_pos, ?_⟩
    intro x _hx t _ht
    have hϕ : ϕ t x = x₀ := hsub.elim _ _
    rw [hϕ, dist_self]
    exact hε

/-- The strict Lyapunov criterion implies local asymptotic stability. -/
theorem isLocallyAttracting_of_strict_lyapunov [FiniteDimensional ℝ E]
    (ϕ : Flow ℝ E) (F : E → E) (V : E → ℝ) (x₀ : E)
    (hflow : FlowHasGenerator ϕ F)
    (heq : ∀ t, ϕ t x₀ = x₀) {r : ℝ} (hr : 0 < r)
    (hF : ContinuousOn F (Metric.ball x₀ r))
    (hV : ContDiffOn ℝ 1 V (Metric.ball x₀ r)) (hV₀ : V x₀ = 0)
    (hpos : ∀ x ∈ Metric.ball x₀ r, x ≠ x₀ → 0 < V x)
    (hdec : ∀ x ∈ Metric.ball x₀ r, x ≠ x₀ → lyapunovDerivative F V x < 0) :
    IsLyapunovStable ϕ x₀ ∧ IsLocallyAttracting ϕ x₀ := by
  have hzero : lyapunovDerivative F V x₀ = 0 :=
    lyapunovDerivative_eq_zero_of_fixed hflow heq hV hr
  have hdec_le : ∀ y ∈ ball x₀ r, lyapunovDerivative F V y ≤ 0 := by
    intro y hy
    rcases eq_or_ne y x₀ with rfl | hy0
    · exact le_of_eq hzero
    · exact (hdec y hy hy0).le
  have hstable : IsLyapunovStable ϕ x₀ :=
    isLyapunovStable_of_lyapunov ϕ F V x₀ hflow heq hr hV hV₀ hpos hdec_le
  refine ⟨hstable, ?_⟩
  obtain ⟨δ, hδ_pos, hδ⟩ := hstable (r / 2) (half_pos hr)
  refine ⟨δ, hδ_pos, ?_⟩
  intro x hx
  set ρ : ℝ := r / 2
  have hρ_pos : 0 < ρ := half_pos hr
  have hρ_lt : ρ < r := half_lt_self hr
  have hforward : ∀ t, 0 ≤ t → ϕ t x ∈ ball x₀ r := by
    intro t ht
    rw [mem_ball]
    exact (hδ x hx t ht).trans hρ_lt
  have hanti : AntitoneOn (fun t ↦ V (ϕ t x)) (Ici 0) :=
    antitoneOn_comp_lyapunov_ball hflow hV hdec_le (convex_Ici 0) hforward
  have hbdd : BddBelow ((fun t ↦ V (ϕ t x)) '' Ici 0) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact lyapunov_nonneg_on_ball hV₀ hpos (hforward t ht)
  obtain ⟨c, htendV, hVge⟩ := tendsto_atTop_of_antitoneOn_Ici hanti hbdd
  have hc_nonneg : 0 ≤ c := by
    have hconst : Tendsto (fun _ : ℝ ↦ (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
    have hle : (fun _ : ℝ ↦ (0 : ℝ)) ≤ᶠ[atTop] fun t ↦ V (ϕ t x) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact lyapunov_nonneg_on_ball hV₀ hpos (hforward t ht)
    exact le_of_tendsto_of_tendsto hconst htendV hle
  have hc_zero : c = 0 := by
    by_contra hc_ne
    have hc_pos : 0 < c := lt_of_le_of_ne hc_nonneg (Ne.symm hc_ne)
    let annulus : Set E := closedBall x₀ ρ ∩ V ⁻¹' Ici c
    have hann_sub : annulus ⊆ ball x₀ r := fun y hy ↦ closedBall_subset_ball hρ_lt hy.1
    have hann_closed : IsClosed annulus :=
      (hV.continuousOn.mono (closedBall_subset_ball hρ_lt)).preimage_isClosed_of_isClosed
        isClosed_closedBall isClosed_Ici
    have hann_compact : IsCompact annulus :=
      (isCompact_closedBall x₀ ρ).of_isClosed_subset hann_closed inter_subset_left
    have hann_ne : annulus.Nonempty := by
      refine ⟨x, ?_, ?_⟩
      · rw [mem_closedBall]
        simpa [ϕ.map_zero_apply] using (hδ x hx 0 le_rfl).le
      · simpa [ϕ.map_zero_apply] using hVge 0 le_rfl
    have hLyap_cont : ContinuousOn (lyapunovDerivative F V) annulus := by
      have hfd : ContinuousOn (fderiv ℝ V) (ball x₀ r) :=
        hV.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
      exact (hfd.clm_apply hF).mono hann_sub
    have hneg : ∀ y ∈ annulus, lyapunovDerivative F V y < 0 := by
      intro y hy
      have hy_ne : y ≠ x₀ := by
        intro hy_eq
        have hc_le : c ≤ V x₀ := by simpa [hy_eq] using hy.2
        rw [hV₀] at hc_le
        linarith
      exact hdec y (hann_sub hy) hy_ne
    obtain ⟨yM, hyM, hmax⟩ := hann_compact.exists_isMaxOn hann_ne hLyap_cont
    have hη_neg : lyapunovDerivative F V yM < 0 := hneg yM hyM
    set η : ℝ := -lyapunovDerivative F V yM
    have hη_pos : 0 < η := by simpa [η] using neg_pos.mpr hη_neg
    have hLyap_le : ∀ y ∈ annulus, lyapunovDerivative F V y ≤ -η := by
      intro y hy
      have hle : lyapunovDerivative F V y ≤ lyapunovDerivative F V yM := hmax hy
      simpa [η] using hle
    have hstay_ann : ∀ t, 0 ≤ t → ϕ t x ∈ annulus := by
      intro t ht
      exact ⟨mem_closedBall.mpr (hδ x hx t ht).le, hVge t ht⟩
    let orbitV : ℝ → ℝ := fun u ↦ V (ϕ u x)
    have hcont : ContinuousOn orbitV (Ici 0) :=
      hV.continuousOn.comp (ϕ.continuous continuous_id continuous_const).continuousOn hforward
    have hdiff : DifferentiableOn ℝ orbitV (interior (Ici 0)) := by
      intro s hs
      exact (hasDerivAt_comp_lyapunov_ball hflow hV
        (hforward s (interior_subset hs))).differentiableAt.differentiableWithinAt
    have hderiv_le : ∀ s ∈ interior (Ici 0), deriv orbitV s ≤ -η := by
      intro s hs
      have hs0 : 0 ≤ s := interior_subset hs
      have hder := hasDerivAt_comp_lyapunov_ball hflow hV (hann_sub (hstay_ann s hs0))
      rw [hder.deriv]
      exact hLyap_le _ (hstay_ann s hs0)
    have hVx_nonneg : 0 ≤ V x :=
      lyapunov_nonneg_on_ball hV₀ hpos (by simpa [ϕ.map_zero_apply] using hforward 0 le_rfl)
    set tBig : ℝ := (V x + 1) / η
    have htBig : 0 ≤ tBig := div_nonneg (by linarith) hη_pos.le
    have hdrop : orbitV tBig - orbitV 0 ≤ -η * (tBig - 0) :=
      (convex_Ici 0).image_sub_le_mul_sub_of_deriv_le hcont hdiff hderiv_le 0
        (mem_Ici.mpr le_rfl) tBig (mem_Ici.mpr htBig) htBig
    have hupper : V (ϕ tBig x) ≤ -1 := by
      have hcalc : V x - η * tBig = -1 := by
        simp only [tBig]
        rw [mul_div_cancel₀ _ (ne_of_gt hη_pos)]
        ring
      have hsub : V (ϕ tBig x) - V x ≤ -η * tBig := by
        simpa [orbitV, ϕ.map_zero_apply, sub_zero] using hdrop
      linarith
    have hlower : 0 ≤ V (ϕ tBig x) :=
      lyapunov_nonneg_on_ball hV₀ hpos (hforward tBig htBig)
    linarith
  rw [hc_zero] at htendV
  rw [Metric.tendsto_nhds]
  intro ε₀ hε₀
  by_cases hρ_le : ρ ≤ ε₀
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (hδ x hx t ht).trans_le hρ_le
  · have hε₀_lt : ε₀ < ρ := lt_of_not_ge hρ_le
    let far : Set E := closedBall x₀ ρ ∩ (fun y ↦ dist y x₀) ⁻¹' Ici ε₀
    have hdist_cont : Continuous fun y : E ↦ dist y x₀ := continuous_id.dist continuous_const
    have hfar_closed : IsClosed far :=
      isClosed_closedBall.inter (isClosed_Ici.preimage hdist_cont)
    have hfar_compact : IsCompact far :=
      (isCompact_closedBall x₀ ρ).of_isClosed_subset hfar_closed inter_subset_left
    by_cases hfar_ne : far.Nonempty
    · have hfar_sub : far ⊆ ball x₀ r := fun y hy ↦ closedBall_subset_ball hρ_lt hy.1
      obtain ⟨yF, hyF, hmin⟩ :=
        hfar_compact.exists_isMinOn hfar_ne (hV.continuousOn.mono hfar_sub)
      have hm_pos : 0 < V yF := by
        refine hpos yF (hfar_sub hyF) ?_
        intro hy_eq
        have hdist0 : ε₀ ≤ dist x₀ x₀ := by simpa [hy_eq, dist_self] using hyF.2
        simp [dist_self] at hdist0
        linarith
      have hev_lt : ∀ᶠ t in atTop, V (ϕ t x) < V yF :=
        htendV.eventually_lt tendsto_const_nhds hm_pos
      filter_upwards [hev_lt, eventually_ge_atTop (0 : ℝ)] with t htV ht
      by_contra hge
      have hin : ϕ t x ∈ far :=
        ⟨mem_closedBall.mpr (hδ x hx t ht).le, le_of_not_gt hge⟩
      exact lt_irrefl _ (htV.trans_le (hmin hin))
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      by_contra hge
      exact hfar_ne ⟨ϕ t x, mem_closedBall.mpr (hδ x hx t ht).le, le_of_not_gt hge⟩

/-- **31.26**: LaSalle on a compact positively invariant set, without a finite-rest-set hypothesis.
  -/
theorem lasalle (ϕ : Flow ℝ E) (F : E → E) (V : E → ℝ)
    (hflow : FlowHasGenerator ϕ F)
    (hF : Continuous F) (hV : ContDiff ℝ 1 V)
    (K : Set E) (hK : IsCompact K) (hinv : ∀ t : ℝ, 0 ≤ t → Set.MapsTo (ϕ t) K K)
    (hdec : ∀ x ∈ K, lyapunovDerivative F V x ≤ 0) {x : E} (hx : x ∈ K) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop,
      ∃ y ∈ largestInvariantSubset ϕ {z ∈ K | lyapunovDerivative F V z = 0},
        dist (ϕ t x) y < ε := by
  have _hLyap_cont : Continuous (lyapunovDerivative F V) :=
    (hV.continuous_fderiv one_ne_zero).clm_apply hF
  have hstayK : ∀ t, 0 ≤ t → ϕ t x ∈ K := fun t ht ↦ hinv t ht hx
  have htail_sub : closure (image2 ϕ (Ici 0) {x}) ⊆ K := by
    refine closure_minimal ?_ hK.isClosed
    intro y hy
    obtain ⟨t, ht, z, hz, rfl⟩ := mem_image2.mp hy
    obtain rfl : z = x := mem_singleton_iff.mp hz
    exact hstayK t ht
  have habsorb : ∃ v ∈ atTop, closure (image2 ϕ v {x}) ⊆ K :=
    ⟨Ici 0, Ici_mem_atTop 0, htail_sub⟩
  let limitSet : Set E := omegaLimit atTop ϕ {x}
  have hlimit_ne : limitSet.Nonempty :=
    nonempty_omegaLimit_of_isCompact_absorbing atTop ϕ {x} hK habsorb (singleton_nonempty x)
  have hlimit_sub_K : limitSet ⊆ K := by
    intro y hy
    exact htail_sub (omegaLimit_subset_closure_image2 atTop ϕ {x} (Ici_mem_atTop 0) hy)
  have hlimit_inv : IsInvariant ϕ limitSet :=
    Flow.isInvariant_omegaLimit atTop ϕ {x} fun t ↦
      tendsto_atTop_add_const_left atTop t tendsto_id
  have hanti : AntitoneOn (fun t ↦ V (ϕ t x)) (Ici 0) :=
    antitoneOn_comp_lyapunov hflow hV (convex_Ici 0) fun t ht ↦
      hdec _ (hstayK t (interior_subset ht))
  have hbdd : BddBelow ((fun t ↦ V (ϕ t x)) '' Ici 0) := by
    refine (hK.bddBelow_image hV.continuous.continuousOn).mono ?_
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨ϕ t x, hstayK t ht, rfl⟩
  obtain ⟨c, htendV, _hVge⟩ := tendsto_atTop_of_antitoneOn_Ici hanti hbdd
  have hV_limit : ∀ y ∈ limitSet, V y = c := by
    intro y hy
    have hmap : MapClusterPt y atTop (fun t ↦ ϕ t x) :=
      (mem_omegaLimit_singleton_iff_mapClusterPt atTop ϕ x y).mp hy
    have hmapV : MapClusterPt (V y) atTop (fun t ↦ V (ϕ t x)) :=
      hmap.continuousAt_comp hV.continuous.continuousAt
    have hcl : ClusterPt (V y) (nhds c) := hmapV.clusterPt.mono htendV
    by_contra hne
    exact hcl.neBot.ne (disjoint_nhds_nhds.mpr hne).eq_bot
  have hderiv_limit : ∀ y ∈ limitSet, lyapunovDerivative F V y = 0 := by
    intro y hy
    have hconst_orbit : ∀ t, V (ϕ t y) = c := by
      intro t
      exact hV_limit _ (hlimit_inv t hy)
    have hder := hasDerivAt_comp_lyapunov (x := y) (t := 0) hflow hV
    have hzero : HasDerivAt (fun t ↦ V (ϕ t y)) 0 0 := by
      have hfun : (fun t ↦ V (ϕ t y)) = fun _ ↦ c := by
        funext t
        exact hconst_orbit t
      rw [hfun]
      exact hasDerivAt_const 0 c
    simpa [ϕ.map_zero_apply] using hder.unique hzero
  let zeroSet : Set E := {z ∈ K | lyapunovDerivative F V z = 0}
  have hlimit_sub : limitSet ⊆ largestInvariantSubset ϕ zeroSet := by
    intro y hy t
    exact ⟨hlimit_sub_K (hlimit_inv t hy), hderiv_limit _ (hlimit_inv t hy)⟩
  intro ε hε
  have hthick_open : IsOpen (thickening ε limitSet) := isOpen_thickening
  have hlimit_thick : limitSet ⊆ thickening ε limitSet := by
    intro y hy
    exact mem_thickening_iff.mpr ⟨y, hy, by simpa [dist_self] using hε⟩
  have habsorb_maps : ∀ᶠ t in atTop, MapsTo (ϕ t) {x} K := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht y hy
    obtain rfl : y = x := mem_singleton_iff.mp hy
    exact hstayK t ht
  have hev := eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset atTop ϕ {x}
    hK habsorb_maps hthick_open hlimit_thick
  filter_upwards [hev] with t ht
  have hmem : ϕ t x ∈ thickening ε limitSet := ht rfl
  have hinf : infDist (ϕ t x) limitSet < ε := (mem_thickening_iff_infDist_lt hlimit_ne).mp hmem
  obtain ⟨y, hy, hdist⟩ := (infDist_lt_iff hlimit_ne).mp hinf
  exact ⟨y, hlimit_sub hy, hdist⟩

end CKMA
