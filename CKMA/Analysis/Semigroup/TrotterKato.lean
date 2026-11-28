/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.Semigroups.Generator.Basic
public import TauCeti.Analysis.Semigroups.GrowthBound
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Basic

import TauCeti.Analysis.Semigroups.CauchyProblem.Inhomogeneous
import TauCeti.Analysis.Semigroups.Generator.OrbitDerivative
import TauCeti.Analysis.Semigroups.Resolvent.Identity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Trotter–Kato approximation

Strong convergence of the generators' resolvents at one real parameter above a common growth
bound is equivalent to strong semigroup convergence uniformly on bounded time intervals.
The proof uses TauCeti's identification of the generator resolvent with the Laplace transform,
its Hille–Yosida resolvent bound, and its inhomogeneous Cauchy problem and Duhamel formula.
Mathlib's dominated convergence and equicontinuity theorems give the limit estimates.

## Main definitions

* `CKMA.SemigroupsConvergeUniformlyOnCompacts`: Uniform strong convergence on bounded time
  intervals.

## Main results

* `CKMA.semigroupsConvergeUniformlyOnCompacts_iff_tendstoUniformlyOn`: the predicate as
  `TendstoUniformlyOn` on bounded time intervals.
* `CKMA.trotter_kato`: Trotter–Kato approximation (**24.17**).

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology TauCeti.Semigroups intervalIntegral Set
open scoped NNReal Interval

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- Uniform strong convergence on every bounded nonnegative time interval. -/
@[expose]
def SemigroupsConvergeUniformlyOnCompacts
    (S : ℕ → StronglyContinuousSemigroup X) (T : StronglyContinuousSemigroup X) : Prop :=
  ∀ x : X, ∀ R : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
    ∀ t : ℝ≥0, t ≤ R → ‖S n t x - T t x‖ < ε

omit [CompleteSpace X] in
/-- Unfolding uniform strong convergence on bounded time intervals. -/
theorem semigroupsConvergeUniformlyOnCompacts_def {S : ℕ → StronglyContinuousSemigroup X}
    {T : StronglyContinuousSemigroup X} :
    SemigroupsConvergeUniformlyOnCompacts S T ↔ ∀ x : X, ∀ R : ℝ≥0, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ R → ‖S n t x - T t x‖ < ε :=
  Iff.rfl

omit [CompleteSpace X] in
/-- Uniform strong convergence on bounded time intervals is `TendstoUniformlyOn` on every
`Set.Iic R`, orbit by orbit. -/
theorem semigroupsConvergeUniformlyOnCompacts_iff_tendstoUniformlyOn
    {S : ℕ → StronglyContinuousSemigroup X} {T : StronglyContinuousSemigroup X} :
    SemigroupsConvergeUniformlyOnCompacts S T ↔ ∀ x : X, ∀ R : ℝ≥0,
      TendstoUniformlyOn (fun n (t : ℝ≥0) ↦ S n t x) (fun t ↦ T t x) atTop (Set.Iic R) := by
  refine forall_congr' fun x => forall_congr' fun R => ?_
  rw [Metric.tendstoUniformlyOn_iff]
  refine forall₂_congr fun ε _ => ⟨fun h => h.mono fun n hn t ht => ?_,
    fun h => h.mono fun n hn t ht => ?_⟩
  · rw [dist_comm, dist_eq_norm]
    exact hn t ht
  · rw [← dist_eq_norm, dist_comm]
    exact hn t ht

/-- Strong semigroup convergence implies strong convergence of the Laplace resolvents. -/
private theorem tendsto_resolvent_of_semigroupsConverge
    (S : ℕ → StronglyContinuousSemigroup X) (T : StronglyContinuousSemigroup X)
    {ω M r : ℝ} (hS : ∀ n, (S n).HasGrowthBound ω M) (hT : T.HasGrowthBound ω M)
    (hr : ω < r) (h : SemigroupsConvergeUniformlyOnCompacts S T) (x : X) :
    Tendsto (fun n ↦ (S n).generator.resolvent r x) atTop
      (𝓝 (T.generator.resolvent r x)) := by
  simp_rw [StronglyContinuousSemigroup.generator_resolvent_eq _ (hS _) hr,
    T.generator_resolvent_eq hT hr, StronglyContinuousSemigroup.resolvent_apply]
  refine tendsto_integral_of_dominated_convergence
    (fun t : ℝ ↦ M * ‖x‖ * Real.exp (-(r - ω) * t))
    (fun n ↦ ((S n).integrableOn_resolvent_integrand (hS n) r hr x).aestronglyMeasurable)
    ?_ (fun n ↦ ?_) ?_
  · exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos (sub_pos.mpr hr)) 0).integrable.const_mul _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (S n).norm_resolvent_integrand_le (hS n) r x (le_of_lt ht)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    apply Tendsto.const_smul
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [h x (Real.toNNReal t) ε hε] with n hn
    simpa only [dist_eq_norm, StronglyContinuousSemigroup.realOperator_def] using
      hn (Real.toNNReal t) le_rfl


/-- Applying the first semigroup's resolvent to an orbit of the second gives a forced
trajectory for the first. The force measures the error in the generator equation. -/
private theorem isForcedMildSolution_resolvent_orbit
    (S T : StronglyContinuousSemigroup X) {ω M r : ℝ}
    (hS : S.HasGrowthBound ω M) (hr : ω < r) (x : T.domain) :
    let Q := S.resolvent hS r hr
    let Ax := T.generator ⟨x, by rw [T.generator_domain]; exact x.property⟩
    IsForcedMildSolution S.generator
      (fun t ↦ Q (T.realOperator t (Ax - r • (x : X))) + T.realOperator t x)
      (Q x) (fun t ↦ Q (T.realOperator t x)) := by
  dsimp only
  let Q := S.resolvent hS r hr
  let Ax := T.generator ⟨x, by rw [T.generator_domain]; exact x.property⟩
  let z := Ax - r • (x : X)
  have hcont (y : X) : Continuous (fun t : ℝ ↦ T.realOperator t y) :=
    T.continuous_realOperator_apply y
  have hF : Continuous (fun t : ℝ ↦ Q (T.realOperator t z) + T.realOperator t x) :=
    (Q.continuous.comp (hcont z)).add (hcont x)
  rw [isForcedMildSolution_iff]
  refine ⟨inferInstance, hF.locallyIntegrable.locallyIntegrableOn _,
    (Q.continuous.comp (hcont x)).continuousOn, ?_, fun t ht ↦ ?_⟩
  · simp only [T.realOperator_zero_apply]
  have hint (y : X) : IntegrableOn (fun s : ℝ ↦ T.realOperator s y) (Ioc 0 t) :=
    (hcont y).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have horbit : (∫ s in Ioc 0 t, T.realOperator s Ax) = T.realOperator t x - x := by
    rw [← intervalIntegral.integral_of_le ht]
    have hx := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
      ((hcont (x : X)).continuousOn)
      (fun s hs ↦ (T.realOperator_hasDerivWithinAt_map_generator x hs.1.le).mono
        Ioi_subset_Ici_self) ((hcont Ax).intervalIntegrable 0 t)
    rwa [T.realOperator_zero_apply] at hx
  have hI :
      (∫ s in Ioc 0 t, Q (T.realOperator s x)) = Q (∫ s in Ioc 0 t, T.realOperator s x) :=
    Q.integral_comp_comm (hint x)
  have hdom (y : X) : Q y ∈ S.generator.domain := by
    rw [S.generator_domain]
    exact S.resolvent_mem_domain hS r hr y
  let J := ∫ s in Ioc 0 t, T.realOperator s x
  have hmem : (∫ s in Ioc 0 t, Q (T.realOperator s x)) ∈ S.generator.domain :=
    hI.symm ▸ hdom J
  refine ⟨hmem, ?_⟩
  have hsub : (⟨∫ s in Ioc 0 t, Q (T.realOperator s x), hmem⟩ : S.generator.domain) =
      ⟨Q J, hdom J⟩ := Subtype.ext hI
  have hgen : r • Q J = J + S.generator ⟨Q J, hdom J⟩ :=
    sub_eq_iff_eq_add.mp (S.resolventRightInv hS r hr J)
  have hforce :
      (∫ s in Ioc 0 t, Q (T.realOperator s z) + T.realOperator s x) =
        Q (T.realOperator t x - x) -
          r • Q (∫ s in Ioc 0 t, T.realOperator s x) + ∫ s in Ioc 0 t, T.realOperator s x := by
    rw [integral_add (Q.integrable_comp (hint z)) (hint x), Q.integral_comp_comm (hint z)]
    simp only [z, map_sub, map_smul]
    have hsmul : Integrable (fun s ↦ r • T.realOperator s x) (volume.restrict (Ioc 0 t)) :=
      Integrable.smul r (hint x)
    simp only [MeasureTheory.integral_sub (hint Ax) hsmul, MeasureTheory.integral_smul,
      horbit, map_sub, map_smul]
  rw [hsub, hforce, map_sub]
  have hq : r • Q (∫ s in Ioc 0 t, T.realOperator s x) =
      J + S.generator ⟨Q J, hdom J⟩ := hgen
  rw [hq]
  dsimp only [J, Q]
  abel

/-- A semigroup resolvent commutes with each nonnegative-time operator of that semigroup. -/
private theorem realOperator_resolvent_apply
    (T : StronglyContinuousSemigroup X) {ω M r t : ℝ}
    (hT : T.HasGrowthBound ω M) (hr : ω < r) (ht : 0 ≤ t) (x : X) :
    T.realOperator t (T.resolvent hT r hr x) = T.resolvent hT r hr (T.realOperator t x) := by
  rw [T.resolvent_apply, T.resolvent_apply, ← (T.realOperator t).integral_comp_comm
    (T.integrableOn_resolvent_integrand hT r hr x)]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs ↦ ?_
  rw [map_smul, ← T.realOperator_add_apply t s ht hs.le,
    ← T.realOperator_add_apply s t hs.le ht, add_comm t s]

omit [CompleteSpace X] in
/-- Resolvent convergence is uniform on compact sets of input vectors by the common
Hille–Yosida bound and the equicontinuity form of Ascoli's theorem. -/
private theorem tendstoUniformlyOn_semigroup_resolvent
    (S : ℕ → StronglyContinuousSemigroup X) (T : StronglyContinuousSemigroup X)
    {ω M r : ℝ} (hS : ∀ n, (S n).HasGrowthBound ω M) (hT : T.HasGrowthBound ω M)
    (hr : ω < r)
    (h : ∀ x, Tendsto (fun n ↦ (S n).resolvent (hS n) r hr x) atTop
      (𝓝 (T.resolvent hT r hr x))) {K : Set X} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n x ↦ (S n).resolvent (hS n) r hr x)
      (fun x ↦ T.resolvent hT r hr x) atTop K := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let C : ℝ≥0 := Real.toNNReal (M / (r - ω))
  let F : ℕ → K → X := fun n x ↦ (S n).resolvent (hS n) r hr x
  let f : K → X := fun x ↦ T.resolvent hT r hr x
  have hC : 0 ≤ M / (r - ω) := div_nonneg (zero_le_one.trans hT.one_le) (sub_pos.mpr hr).le
  have hLip (n : ℕ) : LipschitzWith C (F n) := by
    have hbound : ‖(S n).resolvent (hS n) r hr‖ ≤ (C : ℝ) := by
      rw [Real.coe_toNNReal _ hC]
      exact (S n).resolvent_norm_le (hS n) r hr
    exact LipschitzWith.of_dist_le_mul fun x y ↦
      (ContinuousLinearMap.lipschitzWith_of_opNorm_le hbound).dist_le_mul (x : X) (y : X)
  have hp : Tendsto F atTop (𝓝 f) := tendsto_pi_nhds.mpr fun x ↦ h x
  have he := (LipschitzWith.uniformEquicontinuous F C hLip).equicontinuous
  have hu := (he.tendsto_uniformFun_iff_pi atTop f).mpr hp
  have hd := Metric.tendstoUniformly_iff.mp (UniformFun.tendsto_iff_tendstoUniformly.mp hu)
  refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε ↦ ?_
  filter_upwards [hd ε hε] with n hn x hx
  exact hn ⟨x, hx⟩

/-- The inhomogeneous comparison force vanishes when both resolvents agree on the
orbit of `Ax - rx`. -/
private theorem resolvent_orbit_force_eq_sub
    (T : StronglyContinuousSemigroup X) {ω M r : ℝ} (hT : T.HasGrowthBound ω M)
    (hr : ω < r) (x : T.domain) (Q : X →L[ℝ] X) (t : ℝ) :
    let Ax := T.generator ⟨x, by rw [T.generator_domain]; exact x.property⟩
    let z := T.realOperator t (Ax - r • (x : X))
    Q z + T.realOperator t x = Q z - T.resolvent hT r hr z := by
  dsimp only
  let y : T.domain := ⟨T.realOperator t x, T.realOperator_mem_domain x.property⟩
  have hleft := T.resolventLeftInv hT r hr y
  rw [T.realOperator_generator_map x] at hleft
  have hneg : T.resolvent hT r hr
      (T.realOperator t (T.generator ⟨x, by rw [T.generator_domain]; exact x.property⟩ -
        r • (x : X))) = -T.realOperator t x := by
    rw [map_sub, map_smul, ← neg_sub, map_neg]
    exact congrArg Neg.neg hleft
  rw [hneg, sub_neg_eq_add]

omit [CompleteSpace X] in
/-- The comparison error from a uniformly small force is bounded linearly in time. -/
private theorem norm_duhamel_le_mul_of_forall
    (S : StronglyContinuousSemigroup X) {F : ℝ → X}
    {t C δ : ℝ} (ht : 0 ≤ t) (hC : 0 ≤ C)
    (hS : ∀ s ∈ Icc 0 t, ‖S.realOperator s‖ ≤ C)
    (hF : IntegrableOn F (Ioc 0 t)) (hδ : ∀ s ∈ Ioc 0 t, ‖F s‖ ≤ δ) :
    ‖S.duhamel F t‖ ≤ C * (δ * t) := by
  refine (S.norm_duhamel_le hS hF).trans (mul_le_mul_of_nonneg_left ?_ hC)
  have h := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Ioc 0 t)) (f := fun s ↦ ‖F s‖)
    ((ae_restrict_mem measurableSet_Ioc).mono
      fun s hs ↦ by simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hδ s hs)
  have hnonneg : 0 ≤ ∫ s in Ioc 0 t, ‖F s‖ := integral_nonneg fun _ ↦ norm_nonneg _
  rwa [measureReal_restrict_apply_univ, measureReal_def, Real.volume_Ioc, sub_zero,
    ENNReal.toReal_ofReal ht, Real.norm_eq_abs, abs_of_nonneg hnonneg] at h

/-- The forcing error and the two resolvent errors control the difference between the orbits. -/
private theorem norm_sub_orbits_resolvent_apply_le
    (S T : StronglyContinuousSemigroup X) {ω M r t : ℝ}
    (hT : T.HasGrowthBound ω M) (hr : ω < r) (ht : 0 ≤ t)
    {Q : X →L[ℝ] X} {x : X} {F : ℝ → X}
    (hm : IsForcedMildSolution S.generator F (Q x) (fun s ↦ Q (T.realOperator s x))) :
    let P := T.resolvent hT r hr
    ‖S.realOperator t (P x) - T.realOperator t (P x)‖ ≤
      ‖S.realOperator t (P x - Q x)‖ +
        (‖S.duhamel F t‖ + ‖Q (T.realOperator t x) - P (T.realOperator t x)‖) := by
  dsimp only
  let P := T.resolvent hT r hr
  have heq : S.realOperator t (P x) - T.realOperator t (P x) =
      S.realOperator t (P x - Q x) +
        (-S.duhamel F t + (Q (T.realOperator t x) - P (T.realOperator t x))) := by
    rw [realOperator_resolvent_apply T hT hr ht x, map_sub, hm.eq_realOperator_add_duhamel ht]
    abel
  rw [heq, ← norm_neg (S.duhamel F t)]
  exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))

/-- Strong resolvent convergence yields uniform orbit convergence on resolvent images of
generator-domain vectors. -/
private theorem semigroup_orbit_convergence_on_resolvent_domain
    (S : ℕ → StronglyContinuousSemigroup X) (T : StronglyContinuousSemigroup X)
    {ω M r : ℝ} (hS : ∀ n, (S n).HasGrowthBound ω M) (hT : T.HasGrowthBound ω M)
    (hr : ω < r)
    (h : ∀ x, Tendsto (fun n ↦ (S n).resolvent (hS n) r hr x) atTop
      (𝓝 (T.resolvent hT r hr x)))
    (x : T.domain) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    let P := T.resolvent hT r hr
    ∀ᶠ n in atTop, ∀ t ∈ Icc 0 R,
      ‖(S n).realOperator t (P x) - T.realOperator t (P x)‖ < ε := by
  dsimp only
  let P := T.resolvent hT r hr
  let Q (n : ℕ) := (S n).resolvent (hS n) r hr
  let C := M * Real.exp (max ω 0 * R)
  let z := T.generator ⟨x, by rw [T.generator_domain]; exact x.property⟩ - r • (x : X)
  let K := (fun t ↦ T.realOperator t x) '' Icc 0 R ∪ (fun t ↦ T.realOperator t z) '' Icc 0 R
  have hK : IsCompact K :=
    (isCompact_Icc.image (T.continuous_realOperator_apply x)).union
      (isCompact_Icc.image (T.continuous_realOperator_apply z))
  have hC : 0 ≤ C := mul_nonneg (zero_le_one.trans hT.one_le) (Real.exp_nonneg _)
  let δ := ε / (C * (1 + R) + 1)
  have hden : 0 < C * (1 + R) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hsum : C * δ + (C * (δ * R) + δ) = ε := by
    calc
      _ = δ * (C * (1 + R) + 1) := by ring
      _ = ε := div_mul_cancel₀ _ hden.ne'
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_semigroup_resolvent S T hS hT hr h hK) δ hδ] with n hn t ht
  have herr (y : X) (hy : y ∈ K) : ‖Q n y - P y‖ < δ := by
    calc
      _ = dist (P y) (Q n y) := by rw [dist_eq_norm, norm_sub_rev]
      _ < δ := hn y hy
  let F (s : ℝ) := Q n (T.realOperator s z) + T.realOperator s x
  have hm : IsForcedMildSolution (S n).generator F (Q n x)
      (fun s ↦ Q n (T.realOperator s x)) :=
    isForcedMildSolution_resolvent_orbit (S n) T (hS n) hr x
  have hF (s : ℝ) (hs : s ∈ Ioc 0 t) : ‖F s‖ ≤ δ := by
    dsimp only [F]
    rw [resolvent_orbit_force_eq_sub T hT hr x]
    exact (herr _ (Or.inr ⟨s, ⟨hs.1.le, hs.2.trans ht.2⟩, rfl⟩)).le
  have hD := norm_duhamel_le_mul_of_forall (S n) ht.1 hC
    (fun s hs ↦ (hS n).norm_le_mul_exp_max_zero_mul_of_le hs.1 (hs.2.trans ht.2))
    (hm.locallyIntegrableOn.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc
      |>.mono_set Ioc_subset_Icc_self) hF
  have hx : (x : X) ∈ K := Or.inl ⟨0, ⟨le_rfl, hR⟩, T.realOperator_zero_apply x⟩
  have h0 : ‖(S n).realOperator t (P x - Q n x)‖ ≤ C * δ :=
    (((S n).realOperator t).le_of_opNorm_le
      ((hS n).norm_le_mul_exp_max_zero_mul_of_le ht.1 ht.2) _).trans
        (mul_le_mul_of_nonneg_left (by rw [norm_sub_rev]; exact (herr x hx).le) hC)
  rw [← hsum]
  exact (norm_sub_orbits_resolvent_apply_le (S n) T hT hr ht.1 hm).trans_lt
    (add_lt_add_of_le_of_lt h0 (add_lt_add_of_le_of_lt
      (hD.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht.2 hδ.le) hC))
      (herr _ (Or.inl ⟨t, ht, rfl⟩))))

/-- The resolvent takes the dense generator domain to a dense subset of the ambient space. -/
private theorem dense_resolvent_image_domain
    (T : StronglyContinuousSemigroup X) {ω M r : ℝ} (hT : T.HasGrowthBound ω M)
    (hr : ω < r) :
    Dense ((T.resolvent hT r hr) '' (T.domain : Set X)) := by
  have hrange : DenseRange (T.resolvent hT r hr) :=
    T.dense_domain.mono fun x hx ↦
      ⟨r • x - T.generator ⟨x, by rwa [T.generator_domain]⟩,
        T.resolventLeftInv hT r hr ⟨x, hx⟩⟩
  exact hrange.dense_image (T.resolvent hT r hr).continuous T.dense_domain

/-- Strong resolvent convergence implies uniformly strong semigroup convergence on compact
time intervals. A common growth bound extends the comparison from a dense subset. -/
private theorem semigroupsConverge_of_tendsto_resolvent
    (S : ℕ → StronglyContinuousSemigroup X) (T : StronglyContinuousSemigroup X)
    {ω M r : ℝ} (hS : ∀ n, (S n).HasGrowthBound ω M) (hT : T.HasGrowthBound ω M)
    (hr : ω < r)
    (h : ∀ x, Tendsto (fun n ↦ (S n).generator.resolvent r x) atTop
      (𝓝 (T.generator.resolvent r x))) :
    SemigroupsConvergeUniformlyOnCompacts S T := by
  simp_rw [StronglyContinuousSemigroup.generator_resolvent_eq _ (hS _) hr,
    T.generator_resolvent_eq hT hr] at h
  intro x R ε hε
  let C := M * Real.exp (max ω 0 * (R : ℝ))
  have hC : 0 < C := mul_pos (zero_lt_one.trans_le hT.one_le) (Real.exp_pos _)
  let δ := ε / (4 * C)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ :=
    Metric.mem_closure_iff.mp (dense_resolvent_image_domain T hT hr x) δ hδ
  let w := T.resolvent hT r hr y
  have hw : ‖x - w‖ ≤ δ := (by simpa only [dist_eq_norm] using hxy : ‖x - w‖ < δ).le
  filter_upwards [semigroup_orbit_convergence_on_resolvent_domain S T hS hT hr h
    ⟨y, hy⟩ (NNReal.coe_nonneg R) (half_pos hε)] with n hn t ht
  have htR : (t : ℝ) ∈ Icc 0 (R : ℝ) := ⟨NNReal.coe_nonneg t, ht⟩
  have hSx : ‖(S n).realOperator (t : ℝ) (x - w)‖ ≤ C * δ :=
    (((S n).realOperator _).le_of_opNorm_le
      ((hS n).norm_le_mul_exp_max_zero_mul_of_le htR.1 htR.2) _).trans
        (mul_le_mul_of_nonneg_left hw hC.le)
  have hTx : ‖T.realOperator (t : ℝ) (x - w)‖ ≤ C * δ :=
    ((T.realOperator _).le_of_opNorm_le
      (hT.norm_le_mul_exp_max_zero_mul_of_le htR.1 htR.2) _).trans
        (mul_le_mul_of_nonneg_left hw hC.le)
  have heq : (S n).realOperator (t : ℝ) x - T.realOperator (t : ℝ) x =
      ((S n).realOperator (t : ℝ) (x - w) - T.realOperator (t : ℝ) (x - w)) +
        ((S n).realOperator (t : ℝ) w - T.realOperator (t : ℝ) w) := by
    simp only [map_sub]
    abel
  rw [← (S n).realOperator_coe t, ← T.realOperator_coe t]
  calc
    ‖(S n).realOperator (t : ℝ) x - T.realOperator (t : ℝ) x‖
      ≤ (C * δ + C * δ) + ‖(S n).realOperator (t : ℝ) w - T.realOperator (t : ℝ) w‖ := by
        rw [heq]
        exact (norm_add_le _ _).trans (add_le_add (norm_sub_le_of_le hSx hTx) le_rfl)
    _ < (C * δ + C * δ) + ε / 2 := add_lt_add_of_le_of_lt le_rfl (hn t htR)
    _ = ε := by
      dsimp only [δ]
      field_simp [hC.ne']
      ring

/-- **24.17**, Trotter–Kato: one sufficiently large real resolvent parameter characterizes
uniform-on-bounded-time strong semigroup convergence under a common exponential bound. -/
theorem trotter_kato (S : ℕ → StronglyContinuousSemigroup X)
    (T : StronglyContinuousSemigroup X) {ω M : ℝ}
    (hS : ∀ n, (S n).HasGrowthBound ω M) (hT : T.HasGrowthBound ω M)
    {r : ℝ} (hr : ω < r) :
    (∀ x : X, Tendsto (fun n ↦ (S n).generator.resolvent r x) atTop
      (𝓝 (T.generator.resolvent r x))) ↔ SemigroupsConvergeUniformlyOnCompacts S T := by
  exact ⟨semigroupsConverge_of_tendsto_resolvent S T hS hT hr,
    fun h x ↦ tendsto_resolvent_of_semigroupsConverge S T hS hT hr h x⟩

end CKMA
