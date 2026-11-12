/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Dynamics.ODE.Planar.Transversal

/-!
# Poincaré–Bendixson for a planar flow

A `C¹` flow on `ℂ` whose positive orbit stays in a compact set, and whose omega-limit
set contains no equilibrium, has that omega-limit set equal to one periodic orbit.
Crossings of a transverse segment are ordered toward the forward endpoint of the segment;
from that ordering, the omega-limit set meets the segment once, a point of the limit set
is periodic, and connectedness identifies the whole limit set with the orbit.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Metric Set Topology

/-- Successive crossings of a transverse segment move toward its forward endpoint.
If the orbit meets the open segment at `t1` and later meets the forward subsegment at
`t2`, then after `t2` it does not meet the open segment from `a` to that second
crossing. -/
theorem transverse_monotone {φ : Flow ℝ ℂ} {F : ℂ → ℂ} (hgen : FlowHasGenerator φ F)
    {a b : ℂ} (htr : IsTransverseSegment F a b) {x : ℂ} {t1 t2 : ℝ} (ht : t1 ≤ t2)
    (hx1 : φ t1 x ∈ openSegment ℝ a b) (hx2 : φ t2 x ∈ openSegment ℝ (φ t1 x) b)
    {t : ℝ} (ht' : t2 < t) : φ t x ∉ openSegment ℝ a (φ t2 x) := by
  sorry

/-- An orbit clustering at an interior segment point crosses the segment at arbitrarily
large times, with the crossing kept inside a prescribed distance of that point. -/
theorem exists_late_crossing {φ : Flow ℝ ℂ} {F : ℂ → ℂ} (hgen : FlowHasGenerator φ F)
    {a b : ℂ} (htr : IsTransverseSegment F a b) {p : ℂ} (hp : p ∈ openSegment ℝ a b)
    {x : ℂ} (hcluster : MapClusterPt p atTop fun t ↦ φ t x) {ε : ℝ} (hε : 0 < ε)
    (T : ℝ) : ∃ t : ℝ, T < t ∧ dist (φ t x) p < ε ∧ φ t x ∈ openSegment ℝ a b := by
  obtain ⟨δ, hδ0, hnear⟩ :=
    exists_crossing_time hgen htr hp (min ε 1) (lt_min hε one_pos)
  have hfreq : ∃ᶠ u in atTop, φ u x ∈ ball p δ :=
    (mapClusterPt_iff_frequently.mp hcluster) (ball p δ) (ball_mem_nhds p hδ0)
  rw [frequently_atTop'] at hfreq
  obtain ⟨u, hu, hud⟩ := hfreq (T + 1)
  obtain ⟨s, hs, hsdist, hsseg⟩ := hnear (φ u x) (mem_ball.mp hud)
  refine ⟨s + u, ?_, ?_, ?_⟩
  · have hs1 : |s| < 1 := lt_of_lt_of_le hs (min_le_right _ _)
    rw [abs_lt] at hs1
    linarith
  · rw [φ.map_add]
    exact lt_of_lt_of_le hsdist (min_le_left _ _)
  · rw [φ.map_add]
    exact hsseg

/-- A point of the open segment closer to `v` than half the distance from `u` to `v`
lies strictly beyond `u`, when `v` itself lies beyond `u`. -/
private theorem mem_openSegment_of_near {a b u v q : ℂ} (hab : a ≠ b)
    (hu : u ∈ openSegment ℝ a b) (hv : v ∈ openSegment ℝ a b)
    (hq : q ∈ openSegment ℝ a b) (huv : v ∈ openSegment ℝ u b)
    (hdist : dist q v < dist u v / 2) : q ∈ openSegment ℝ u b := by
  set pu : ℝ := lineParam a b u
  set pv : ℝ := lineParam a b v
  have hlt : pu < pv := (mem_openSegment_right_iff hab hu hv).mp huv
  have hsideu : transverseSide a b u = 0 :=
    ((mem_openSegment_iff_lineParam hab).mp hu).1
  have hsidev : transverseSide a b v = 0 :=
    ((mem_openSegment_iff_lineParam hab).mp hv).1
  have hsideq : transverseSide a b q = 0 :=
    transverseSide_eq_zero_of_mem_segment (openSegment_subset_segment ℝ a b hq)
  have hnorm : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hab))
  have hd_uv : dist u v = (pv - pu) * ‖b - a‖ := by
    rw [dist_eq_abs_sub_mul_norm hab hsideu hsidev, abs_sub_comm,
      abs_of_pos (sub_pos.mpr hlt)]
  have hd_qv : dist q v = |lineParam a b q - pv| * ‖b - a‖ :=
    dist_eq_abs_sub_mul_norm hab hsideq hsidev
  have hparam : |lineParam a b q - pv| < (pv - pu) / 2 := by
    have hlt' : |lineParam a b q - pv| * ‖b - a‖ <
        (pv - pu) * ‖b - a‖ / 2 := by
      simpa [hd_qv, hd_uv] using hdist
    have hrew : (pv - pu) * ‖b - a‖ / 2 = (pv - pu) / 2 * ‖b - a‖ := by ring
    rw [hrew] at hlt'
    exact (mul_lt_mul_iff_of_pos_right hnorm).mp hlt'
  have habs := abs_lt.mp hparam
  have hqI := lineParam_mem_Ioo_of_mem_openSegment hab hq
  have hgt : pu < lineParam a b q := by linarith
  exact (mem_openSegment_right_iff hab hu hq).mpr hgt

/-- An omega-limit set meets an open transverse segment in at most one point. -/
private theorem no_two_omega_openSegment {φ : Flow ℝ ℂ} {F : ℂ → ℂ}
    (hgen : FlowHasGenerator φ F) {a b : ℂ} (htr : IsTransverseSegment F a b)
    {x u v : ℂ} (hu : u ∈ omegaLimit atTop φ {x}) (huab : u ∈ openSegment ℝ a b)
    (hv : v ∈ omegaLimit atTop φ {x}) (hvab : v ∈ openSegment ℝ a b)
    (hvb : v ∈ openSegment ℝ u b) : False := by
  set duv : ℝ := dist u v / 2
  have hpos : 0 < dist u v := by
    have hne : u ≠ v := by
      intro h
      have hvb' : v ∈ openSegment ℝ v b := by rw [h] at hvb; exact hvb
      have hv_eq : v = b := left_mem_openSegment_iff.mp hvb'
      have hvab' : b ∈ openSegment ℝ a b := by rw [hv_eq] at hvab; exact hvab
      exact htr.ne (right_mem_openSegment_iff.mp hvab')
    exact dist_pos.mpr hne
  have hduv : 0 < duv := by
    simp only [duv]
    exact half_pos hpos
  have hclu_u := (mem_omegaLimit_singleton_iff_mapClusterPt (f := atTop) φ x u).mp hu
  have hclu_v := (mem_omegaLimit_singleton_iff_mapClusterPt (f := atTop) φ x v).mp hv
  obtain ⟨t1, -, hd1, hs1⟩ := exists_late_crossing hgen htr huab hclu_u hduv 0
  obtain ⟨t2, ht2, hd2, hs2⟩ := exists_late_crossing hgen htr hvab hclu_v hduv t1
  obtain ⟨t3, ht3, hd3, hs3⟩ := exists_late_crossing hgen htr huab hclu_u hduv t2
  have h1v : φ t1 x ∈ openSegment ℝ a v :=
    openSegment_separate_left huab hvb hs1 (by
      have hdu : duv < dist u v := by simpa only [duv] using half_lt_self hpos
      linarith)
  have hdist1v : duv < dist v (φ t1 x) := by
    have htri := dist_triangle u (φ t1 x) v
    have hnear : dist u (φ t1 x) < dist u v / 2 := by
      simpa only [duv, dist_comm] using hd1
    have hle : dist u v - dist u (φ t1 x) ≤ dist (φ t1 x) v := by linarith
    have hgap : dist u v / 2 < dist u v - dist u (φ t1 x) := by linarith
    have hlt : dist u v / 2 < dist (φ t1 x) v := lt_of_lt_of_le hgap hle
    simpa only [duv, dist_comm] using hlt
  have h2right : φ t2 x ∈ openSegment ℝ (φ t1 x) b :=
    openSegment_separate_right hvab h1v hs2 (by linarith)
  have h2u : φ t2 x ∈ openSegment ℝ u b :=
    mem_openSegment_of_near htr.ne huab hvab hs2 hvb (by simpa only [duv] using hd2)
  have hdist2u : duv < dist u (φ t2 x) := by
    have htri := dist_triangle u (φ t2 x) v
    have hnear : dist (φ t2 x) v < dist u v / 2 := by simpa only [duv] using hd2
    have hle : dist u v - dist (φ t2 x) v ≤ dist u (φ t2 x) := by linarith
    have hgap : dist u v / 2 < dist u v - dist (φ t2 x) v := by linarith
    have hlt : dist u v / 2 < dist u (φ t2 x) := lt_of_lt_of_le hgap hle
    simpa only [duv] using hlt
  have h3left : φ t3 x ∈ openSegment ℝ a (φ t2 x) :=
    openSegment_separate_left huab h2u hs3 (by linarith)
  exact transverse_monotone hgen htr ht2.le hs1 h2right ht3 h3left

/-- The omega-limit set meets an open transverse segment in exactly one point. -/
theorem omega_openSegment_singleton {φ : Flow ℝ ℂ} {F : ℂ → ℂ}
    (hgen : FlowHasGenerator φ F) {a b : ℂ} (htr : IsTransverseSegment F a b)
    {x u : ℂ} (hu : u ∈ omegaLimit atTop φ {x}) (huab : u ∈ openSegment ℝ a b) :
    omegaLimit atTop φ {x} ∩ openSegment ℝ a b = {u} := by
  ext v
  constructor
  · intro hv
    have hvω : v ∈ omegaLimit atTop φ {x} := hv.1
    have hvab : v ∈ openSegment ℝ a b := hv.2
    rcases lt_trichotomy (lineParam a b u) (lineParam a b v) with hlt | heq | hgt
    · have hvb : v ∈ openSegment ℝ u b :=
        (mem_openSegment_right_iff htr.ne huab hvab).mpr hlt
      exact False.elim
        (no_two_omega_openSegment hgen htr hu huab hvω hvab hvb)
    · have hsideu : transverseSide a b u = 0 :=
        ((mem_openSegment_iff_lineParam htr.ne).mp huab).1
      have hsidev : transverseSide a b v = 0 :=
        ((mem_openSegment_iff_lineParam htr.ne).mp hvab).1
      have hu' := eq_add_lineParam_of_transverseSide_eq_zero htr.ne hsideu
      have hv' := eq_add_lineParam_of_transverseSide_eq_zero htr.ne hsidev
      rw [← heq] at hv'
      rw [← hu'] at hv'
      exact mem_singleton_iff.mpr hv'
    · have hub : u ∈ openSegment ℝ v b :=
        (mem_openSegment_right_iff htr.ne hvab huab).mpr hgt
      exact False.elim
        (no_two_omega_openSegment hgen htr hvω hvab hu huab hub)
  · intro hv
    rw [mem_singleton_iff] at hv
    subst hv
    exact ⟨hu, huab⟩

/-- A periodic orbit contained in a critical-point-free compact omega-limit set is
the whole omega-limit set. -/
theorem periodic_orbit_eq_omega {φ : Flow ℝ ℂ} {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (hgen : FlowHasGenerator φ F) {x : ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hstay : ∀ t : ℝ, 0 ≤ t → φ t x ∈ K)
    (hrest : ∀ y ∈ omegaLimit atTop φ {x}, F y ≠ 0) {y : ℂ} {T : ℝ}
    (hT0 : 0 < T) (hT : φ T y = y) (hy : y ∈ omegaLimit atTop φ {x}) :
    omegaLimit atTop φ {x} = Set.range (fun t : ℝ ↦ φ t y) := by
  set ω : Set ℂ := omegaLimit atTop φ {x}
  set P : Set ℂ := Set.range (fun t : ℝ ↦ φ t y)
  have hinv : IsInvariant φ ω := isInvariant_omegaLimit_atTop x
  have hpre : IsPreconnected ω := isPreconnected_omegaLimit_of_forward hK hstay
  have hPcomp : IsCompact P := by
    unfold P
    rw [range_eq_image_Icc_of_periodic (φ := φ) hT0 hT]
    exact isCompact_Icc.image (continuous_id.flow φ continuous_const)
  have hPcl : IsClosed P := hPcomp.isClosed
  have hPω : P ⊆ ω := by
    intro w hw
    unfold P at hw
    obtain ⟨t, rfl⟩ := hw
    exact hinv t hy
  obtain ⟨a, b, hyab, htr⟩ := exists_isTransverseSegment hF.continuous (hrest y hy)
  have huniq := omega_openSegment_singleton hgen htr hy hyab
  obtain ⟨δ, hδ0, hnear⟩ := exists_crossing_time hgen htr hyab 1 one_pos
  have hball : ∀ w ∈ ω, dist w y < δ → w ∈ P := by
    intro w hw hd
    obtain ⟨t, -, -, hseg⟩ := hnear w hd
    have hhit : φ t w = y := by
      have hmem : φ t w ∈ omegaLimit atTop φ {x} ∩ openSegment ℝ a b :=
        ⟨hinv t hw, hseg⟩
      rw [huniq] at hmem
      exact mem_singleton_iff.mp hmem
    have hback : φ (-t) y = w := by
      rw [← hhit, ← φ.map_add, neg_add_cancel, φ.map_zero_apply]
    unfold P
    exact ⟨-t, hback⟩
  let U : Set ℂ := ⋃ s ∈ Icc (0 : ℝ) T, (fun w ↦ φ (-s) w) ⁻¹' ball y δ
  have hUopen : IsOpen U :=
    isOpen_biUnion fun s _ => isOpen_ball.preimage (continuous_const.flow φ continuous_id)
  have hPU : P ⊆ U := by
    intro w hw
    unfold P at hw
    rw [range_eq_image_Icc_of_periodic (φ := φ) hT0 hT] at hw
    obtain ⟨s, hs, rfl⟩ := hw
    unfold U
    refine mem_iUnion₂.mpr ⟨s, hs, ?_⟩
    rw [mem_preimage, mem_ball, ← φ.map_add, neg_add_cancel, φ.map_zero_apply, dist_self]
    exact hδ0
  have hUω : U ∩ ω ⊆ P := by
    intro w hw
    obtain ⟨hwU, hwω⟩ := hw
    unfold U at hwU
    obtain ⟨s, -, hwpre⟩ := mem_iUnion₂.mp hwU
    have hd : dist (φ (-s) w) y < δ := by
      rw [mem_preimage, mem_ball] at hwpre
      exact hwpre
    have hback : φ (-s) w ∈ P := hball _ (hinv (-s) hwω) hd
    unfold P at hback
    obtain ⟨r, hr⟩ := hback
    have hr' : φ r y = φ (-s) w := hr
    unfold P
    refine ⟨s + r, ?_⟩
    change φ (s + r) y = w
    rw [φ.map_add, hr', ← φ.map_add, add_neg_cancel, φ.map_zero_apply]
  let V : Set ℂ := Pᶜ
  have hVopen : IsOpen V := hPcl.isOpen_compl
  refine subset_antisymm ?_ hPω
  intro w hw
  by_contra hwP
  have hcover : ω ⊆ U ∪ V := by
    intro q _hq
    by_cases hqP : q ∈ P
    · exact Or.inl (hPU hqP)
    · exact Or.inr (by simpa only [V, mem_compl_iff] using hqP)
  have hyU : y ∈ U := hPU ⟨0, by simp [φ.map_zero_apply]⟩
  have hwV : w ∈ V := by simpa only [V, mem_compl_iff] using hwP
  obtain ⟨q, hqω, hqU, hqV⟩ :=
    hpre U V hUopen hVopen hcover ⟨y, hy, hyU⟩ ⟨w, hw, hwV⟩
  exact hqV (by simpa only [V, mem_compl_iff] using hUω ⟨hqU, hqω⟩)

/-- On the complex plane, a compactly trapped orbit with no equilibrium in its
omega-limit set has that limit set equal to one periodic orbit. -/
theorem poincare_bendixson_complex (φ : Flow ℝ ℂ) (F : ℂ → ℂ) (hF : ContDiff ℝ 1 F)
    (hgen : FlowHasGenerator φ F) (x : ℂ) (K : Set ℂ) (hK : IsCompact K)
    (hstay : ∀ t : ℝ, 0 ≤ t → φ t x ∈ K)
    (hrest : ∀ y ∈ omegaLimit atTop φ {x}, F y ≠ 0) :
    ∃ y : ℂ, ∃ T : ℝ, 0 < T ∧ φ T y = y ∧
      omegaLimit atTop φ {x} = Set.range (fun t : ℝ ↦ φ t y) := by
  set ω : Set ℂ := omegaLimit atTop φ {x}
  have hne := nonempty_omegaLimit_of_forward hK hstay
  have hsub : ω ⊆ K := omegaLimit_subset_of_forward hK.isClosed hstay
  have hinv : IsInvariant φ ω := isInvariant_omegaLimit_atTop x
  have hcl : IsClosed ω := isClosed_omegaLimit atTop φ {x}
  obtain ⟨y, hy⟩ := hne
  have hyK : ∀ t : ℝ, 0 ≤ t → φ t y ∈ K := fun t _ => hsub (hinv t hy)
  obtain ⟨z, hz⟩ := nonempty_omegaLimit_of_forward hK hyK
  have hzω : z ∈ ω := by
    have htail : closure (image2 φ (Ici 0) {y}) ⊆ ω := by
      refine closure_minimal ?_ hcl
      intro w hw
      obtain ⟨t, -, w', hw', rfl⟩ := mem_image2.mp hw
      obtain rfl : w' = y := mem_singleton_iff.mp hw'
      exact hinv t hy
    exact htail (omegaLimit_subset_closure_image2 atTop φ {y} (Ici_mem_atTop 0) hz)
  have hzF : F z ≠ 0 := hrest z hzω
  obtain ⟨a, b, hzab, htr⟩ := exists_isTransverseSegment hF.continuous hzF
  have huniq := omega_openSegment_singleton hgen htr hzω hzab
  have hclu := (mem_omegaLimit_singleton_iff_mapClusterPt (f := atTop) φ y z).mp hz
  obtain ⟨t1, ht1, -, hs1⟩ := exists_late_crossing hgen htr hzab hclu one_pos 0
  obtain ⟨t2, ht2, -, hs2⟩ := exists_late_crossing hgen htr hzab hclu one_pos t1
  have h1 : φ t1 y = z := by
    have hmem : φ t1 y ∈ ω ∩ openSegment ℝ a b := ⟨hinv t1 hy, hs1⟩
    rw [huniq] at hmem
    exact mem_singleton_iff.mp hmem
  have h2 : φ t2 y = z := by
    have hmem : φ t2 y ∈ ω ∩ openSegment ℝ a b := ⟨hinv t2 hy, hs2⟩
    rw [huniq] at hmem
    exact mem_singleton_iff.mp hmem
  have hT0 : 0 < t2 - t1 := by linarith
  have hper : φ (t2 - t1) z = z := by
    rw [← h1, ← φ.map_add]
    have hsum : (t2 - t1) + t1 = t2 := by ring
    rw [hsum, h2, ← h1]
  exact ⟨z, t2 - t1, hT0, hper,
    periodic_orbit_eq_omega hF hgen hK hstay hrest hT0 hper hzω⟩

end CKMA
