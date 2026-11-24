/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.Semigroups.Generator.Basic
import TauCeti.Analysis.Semigroups.Generator.Closed
import TauCeti.Analysis.Semigroups.Generator.Uniqueness
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Duhamel formula and integrated semigroup solutions

Variation-of-constants trajectories and their integrated generator equations for
strongly continuous semigroups. Generators, resolvents and core domains reuse TauCeti's
semigroup modules; integration uses Mathlib.

## Main definitions

* `CKMA.forcedSemigroupTrajectory`: the variation-of-constants trajectory
  `t ↦ S(t) x + ∫₀ᵗ S(t - s) f(s) ds`.
* `CKMA.IsIntegratedSemigroupSolution`: integrated solution of `u' = A u + f` on `[0, T]`.

## Main results

* `CKMA.isIntegratedSemigroupSolution_forcedSemigroupTrajectory`: for `L¹` forcing on
  `[0, T]`, `forcedSemigroupTrajectory` is an integrated solution.
* `CKMA.IsIntegratedSemigroupSolution.eqOn`: integrated solutions with the same initial datum
  and forcing agree on `[0, T]`.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology TauCeti.Semigroups intervalIntegral
open scoped NNReal BoundedContinuousFunction

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The actual variation-of-constants trajectory, using the upstream real-time semigroup shim. -/
@[expose]
def forcedSemigroupTrajectory (S : StronglyContinuousSemigroup X) (x : X)
    (f : ℝ → X) (t : ℝ) : X := S.realOperator t x + ∫ s in (0 : ℝ)..t, S.realOperator (t - s) (f s)

/-- An integrated solution of `u'=Au+f`, phrased independently of the variation-of-constants
formula. The time integral, rather than every value of `u`, belongs to the generator domain. -/
@[expose]
def IsIntegratedSemigroupSolution (S : StronglyContinuousSemigroup X) (x : X)
    (f u : ℝ → X) (T : ℝ) : Prop :=
  ContinuousOn u (Set.Icc 0 T) ∧ ∀ t ∈ Set.Icc 0 T,
    ∃ h : (∫ s in (0 : ℝ)..t, u s) ∈ S.generator.domain,
      u t = x + S.generator ⟨∫ s in (0 : ℝ)..t, u s, h⟩ + ∫ s in (0 : ℝ)..t, f s

/-- Joint strong continuity of `(t, x) ↦ S.realOperator t x`, including nonpositive times. -/
private theorem continuous_prod_realOperator (S : StronglyContinuousSemigroup X) :
    Continuous fun p : ℝ × X => S.realOperator p.1 p.2 := by
  have hneg : ContinuousOn (fun p : ℝ × X => S.realOperator p.1 p.2)
      (Set.Iic 0 ×ˢ Set.univ) := by
    refine continuous_snd.continuousOn.congr fun p hp => ?_
    rw [S.realOperator_def, Real.toNNReal_of_nonpos hp.1]
    exact S.map_zero_apply p.2
  have hpos : ContinuousOn (fun p : ℝ × X => S.realOperator p.1 p.2)
      (Set.Ici 0 ×ˢ Set.univ) := fun p _ =>
    S.tendsto_realOperator_apply
      (continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hunion := hneg.union_of_isClosed hpos (isClosed_Iic.prod isClosed_univ)
    (isClosed_Ici.prod isClosed_univ)
  rw [← Set.union_prod, Set.Iic_union_Ici, Set.univ_prod_univ] at hunion
  exact continuousOn_univ.mp hunion

/-- An operator-norm bound for the semigroup on a compact time interval `[0, T]`. -/
private theorem norm_realOperator_le_on_Icc (S : StronglyContinuousSemigroup X) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → t ≤ T → ‖S.realOperator t‖ ≤ C := by
  obtain ⟨growth, growthConst, hgrowth⟩ := S.existsGrowthBound
  refine ⟨growthConst * Real.exp (max growth 0 * T), ?_, fun t ht htT => ?_⟩
  · exact mul_nonneg (zero_le_one.trans hgrowth.one_le) (Real.exp_nonneg _)
  · exact hgrowth.norm_le_mul_exp_max_zero_mul_of_le ht htT

/-- The orbit average `(1 / h) • ∫₀ʰ S(u) y du` tends to `y` as `h → 0⁺`. -/
private theorem tendsto_average_interval_zero (S : StronglyContinuousSemigroup X) (y : X) :
    Tendsto (fun h : ℝ => (1 / h) • ∫ u in (0 : ℝ)..h, S.realOperator u y)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds y) := by
  refine (S.tendsto_average_orbit_zero y).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [integral_of_le hh.le]

/-- Shifting a nonnegative orbit integral by a positive time. -/
private theorem orbitIntegral_shift (S : StronglyContinuousSemigroup X) (y : X) {a h : ℝ}
    (ha : 0 ≤ a) (hh : 0 < h) :
    S.realOperator h (∫ u in (0 : ℝ)..a, S.realOperator u y) -
        ∫ u in (0 : ℝ)..a, S.realOperator u y =
      (∫ u in a..(a + h), S.realOperator u y) -
        ∫ u in (0 : ℝ)..h, S.realOperator u y := by
  let phi : ℝ → X := fun u => S.realOperator u y
  have hcont : ContinuousOn phi (Set.Ici 0) := S.realOperator_continuousOn_Ici y
  have hint : ∀ {p q : ℝ}, 0 ≤ p → 0 ≤ q → IntervalIntegrable phi volume p q := by
    intro p q hp hq
    exact (hcont.mono fun u hu => by
      exact (le_inf hp hq).trans hu.1).intervalIntegrable
  have hpush : S.realOperator h (∫ u in (0 : ℝ)..a, phi u) =
      ∫ u in h..(a + h), phi u := by
    rw [← (S.realOperator h).intervalIntegral_comp_comm (hint le_rfl ha)]
    rw [integral_congr (g := fun u => phi (u + h))]
    · simp [zero_add]
    · intro u hu
      have hu0 : 0 ≤ u := by
        rw [Set.uIcc_of_le ha] at hu
        exact hu.1
      have happly : S.realOperator h (S.realOperator u y) =
          S.realOperator (u + h) y := by
        rw [add_comm u h]
        exact (S.realOperator_add_apply h u hh.le hu0 y).symm
      simpa [phi] using happly
  have hsub := integral_interval_sub_interval_comm' (f := phi) (a := h) (b := a + h)
    (c := 0) (d := a) (hint hh.le (by linarith)) (hint le_rfl ha) (hint hh.le le_rfl)
  rw [hpush]
  exact hsub

/-- The indefinite orbit integral depends continuously on the upper limit and the vector. -/
private theorem continuous_orbitIntegral (S : StronglyContinuousSemigroup X) :
    Continuous fun p : ℝ × X => ∫ u in (0 : ℝ)..p.1, S.realOperator u p.2 := by
  have hun : Continuous fun q : (ℝ × X) × ℝ => S.realOperator q.2 q.1.2 :=
    (continuous_prod_realOperator S).comp
      (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
  exact continuous_parametric_intervalIntegral_of_continuous (μ := volume) (a₀ := 0)
    (f := fun p : ℝ × X => fun u => S.realOperator u p.2) (s := Prod.fst) hun continuous_fst

omit [CompleteSpace X] in
/-- Substitution putting the elapsed time in the semigroup argument of a Duhamel integral. -/
private theorem duhamel_eq_shifted (S : StronglyContinuousSemigroup X) (f : ℝ → X) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, S.realOperator (t - s) (f s)) =
      ∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s)) := by
  have hsub := integral_comp_sub_left (f := fun s => S.realOperator s (f (t - s)))
    (a := (0 : ℝ)) (b := t) (d := t)
  have hcongr : (∫ s in (0 : ℝ)..t, S.realOperator (t - s) (f s)) =
      ∫ s in (0 : ℝ)..t, S.realOperator (t - s) (f (t - (t - s))) := by
    refine integral_congr fun s _ => ?_
    rw [sub_sub_cancel]
  rw [hcongr]
  simpa [sub_self, sub_zero] using hsub

/-- For globally continuous forcing, the Duhamel term is a continuous function of time. -/
private theorem continuous_duhamel (S : StronglyContinuousSemigroup X) {f : ℝ → X}
    (hf : Continuous f) :
    Continuous fun t : ℝ => ∫ s in (0 : ℝ)..t, S.realOperator (t - s) (f s) := by
  have hF : Continuous fun q : ℝ × ℝ => S.realOperator q.2 (f (q.1 - q.2)) :=
    (continuous_prod_realOperator S).comp
      (continuous_snd.prodMk (hf.comp (continuous_fst.sub continuous_snd)))
  have hcont : Continuous fun t => ∫ s in (0 : ℝ)..t, S.realOperator s (f (t - s)) :=
    continuous_parametric_intervalIntegral_of_continuous (μ := volume) (a₀ := 0)
      (f := fun t s => S.realOperator s (f (t - s))) (s := id) hF continuous_id
  exact hcont.congr fun t => (duhamel_eq_shifted S f t).symm

/-- The Duhamel integrand of an integrable forcing is integrable on each subinterval. -/
private theorem integrableOn_duhamelIntegrand (S : StronglyContinuousSemigroup X) {T : ℝ}
    {f : ℝ → X} (hf : IntegrableOn f (Set.Icc 0 T)) {t : ℝ} (htT : t ≤ T) :
    IntegrableOn (fun s => S.realOperator (t - s) (f s)) (Set.Icc 0 t) := by
  obtain ⟨C, -, hC⟩ := norm_realOperator_le_on_Icc S T
  have hf' : IntegrableOn f (Set.Icc 0 t) := hf.mono_set (Set.Icc_subset_Icc_right htT)
  let applyReal : ℝ → X → X := fun time vec => S.realOperator time vec
  have hsm : AEStronglyMeasurable (fun s => S.realOperator (t - s) (f s))
      (volume.restrict (Set.Icc 0 t)) :=
    (continuous_prod_realOperator S).comp_aestronglyMeasurable₂
      (g := applyReal)
      (continuous_const.sub continuous_id).aestronglyMeasurable hf'.aestronglyMeasurable
  have hdom : IntegrableOn (fun s => C * ‖f s‖) (Set.Icc 0 t) := hf'.norm.const_mul C
  refine hdom.mono' hsm ?_
  refine ae_restrict_of_forall_mem measurableSet_Icc fun s hs => ?_
  have htime0 : 0 ≤ t - s := sub_nonneg.mpr hs.2
  have htimeT : t - s ≤ T := by linarith [hs.1, htT]
  calc ‖S.realOperator (t - s) (f s)‖
      ≤ ‖S.realOperator (t - s)‖ * ‖f s‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * ‖f s‖ := mul_le_mul_of_nonneg_right (hC _ htime0 htimeT) (norm_nonneg _)

/-- The Duhamel kernel `(s, r) ↦ S(s - r) f(r)` on the half-plane `r ≤ s`, extended by zero. -/
private def duhamelKernel (S : StronglyContinuousSemigroup X) (f : ℝ → X) (p : ℝ × ℝ) : X :=
  if p.2 ≤ p.1 then S.realOperator (p.1 - p.2) (f p.2) else 0

omit [CompleteSpace X] in
/-- The Duhamel kernel on the half-plane `r ≤ s`. -/
private theorem duhamelKernel_of_le (S : StronglyContinuousSemigroup X) (f : ℝ → X) {s r : ℝ}
    (hrs : r ≤ s) : duhamelKernel S f (s, r) = S.realOperator (s - r) (f r) :=
  ite_eq_left hrs

omit [CompleteSpace X] in
/-- The Duhamel kernel vanishes for `s < r`. -/
private theorem duhamelKernel_of_lt (S : StronglyContinuousSemigroup X) (f : ℝ → X) {s r : ℝ}
    (hsr : s < r) : duhamelKernel S f (s, r) = 0 :=
  ite_eq_right (not_le.mpr hsr)

/-- For continuous forcing the Duhamel kernel is strongly measurable on the plane. -/
private theorem stronglyMeasurable_duhamelKernel (S : StronglyContinuousSemigroup X)
    {f : ℝ → X} (hf : Continuous f) : StronglyMeasurable (duhamelKernel S f) := by
  have hpair : Continuous fun p : ℝ × ℝ => (p.1 - p.2, f p.2) :=
    (continuous_fst.sub continuous_snd).prodMk (hf.comp continuous_snd)
  exact StronglyMeasurable.ite (isClosed_le continuous_snd continuous_fst).measurableSet
    ((continuous_prod_realOperator S).comp_stronglyMeasurable hpair.stronglyMeasurable)
    stronglyMeasurable_const

omit [CompleteSpace X] in
/-- A bound `C` for the semigroup on `[0, t]` bounds the Duhamel kernel at `(s, r)` by
`C * ‖f r‖` whenever `0 ≤ r` and `s ≤ t`. -/
private theorem norm_duhamelKernel_le (S : StronglyContinuousSemigroup X) (f : ℝ → X)
    {t C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ s : ℝ, 0 ≤ s → s ≤ t → ‖S.realOperator s‖ ≤ C)
    {s r : ℝ} (hr0 : 0 ≤ r) (hsT : s ≤ t) :
    ‖duhamelKernel S f (s, r)‖ ≤ C * ‖f r‖ := by
  rcases le_or_gt r s with hrs | hsr
  · rw [duhamelKernel_of_le S f hrs]
    calc ‖S.realOperator (s - r) (f r)‖
        ≤ ‖S.realOperator (s - r)‖ * ‖f r‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * ‖f r‖ :=
          mul_le_mul_of_nonneg_right (hC _ (sub_nonneg.mpr hrs) (by linarith)) (norm_nonneg _)
  · rw [duhamelKernel_of_lt S f hsr, norm_zero]
    exact mul_nonneg hC0 (norm_nonneg _)

/-- For continuous forcing the Duhamel kernel is integrable on the square `[0, t]²`. -/
private theorem integrableOn_duhamelKernel (S : StronglyContinuousSemigroup X) {f : ℝ → X}
    (hf : Continuous f) {t C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ s : ℝ, 0 ≤ s → s ≤ t → ‖S.realOperator s‖ ≤ C) :
    IntegrableOn (duhamelKernel S f) (Set.Icc 0 t ×ˢ Set.Icc 0 t) := by
  have hdom : IntegrableOn (fun p : ℝ × ℝ => C * ‖f p.2‖) (Set.Icc 0 t ×ˢ Set.Icc 0 t) :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      (continuous_const.mul ((continuous_norm.comp hf).comp continuous_snd)).continuousOn
  refine hdom.mono' (stronglyMeasurable_duhamelKernel S hf).aestronglyMeasurable.restrict ?_
  refine ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc) fun p hp => ?_
  exact norm_duhamelKernel_le S f hC0 hC hp.2.1 hp.1.2

/-- A horizontal slice of the Duhamel kernel: the inner Duhamel integral up to `s ∈ [0, t]`
is the integral of the kernel over `[0, t]` in the second variable. -/
private theorem intervalIntegral_duhamelKernel_left (S : StronglyContinuousSemigroup X)
    {f : ℝ → X} (hf : Continuous f) {s t : ℝ} (hs0 : 0 ≤ s) (hsT : s ≤ t) :
    (∫ r in (0 : ℝ)..s, S.realOperator (s - r) (f r)) =
      ∫ r in (0 : ℝ)..t, duhamelKernel S f (s, r) := by
  obtain ⟨C, hC0, hC⟩ := norm_realOperator_le_on_Icc S t
  have hint : IntegrableOn (fun r => duhamelKernel S f (s, r)) (Set.Icc 0 t) := by
    have hdom : IntegrableOn (fun r => C * ‖f r‖) (Set.Icc 0 t) :=
      (continuous_const.mul (continuous_norm.comp hf)).integrableOn_Icc
    refine hdom.mono' ((stronglyMeasurable_duhamelKernel S hf).comp_measurable
      measurable_prodMk_left).aestronglyMeasurable.restrict ?_
    exact ae_restrict_of_forall_mem measurableSet_Icc fun r hr =>
      norm_duhamelKernel_le S f hC0 hC hr.1 hsT
  have hleft : IntervalIntegrable (fun r => duhamelKernel S f (s, r)) volume 0 s :=
    ((Set.uIcc_of_le hs0).symm ▸
      (hint.mono_set (Set.Icc_subset_Icc_right hsT))).intervalIntegrable
  have hright : IntervalIntegrable (fun r => duhamelKernel S f (s, r)) volume s t :=
    ((Set.uIcc_of_le hsT).symm ▸
      (hint.mono_set (Set.Icc_subset_Icc_left hs0))).intervalIntegrable
  have hadd := integral_add_adjacent_intervals (a := (0 : ℝ)) (b := s) (c := t) hleft hright
  have htail : ∫ r in s..t, duhamelKernel S f (s, r) = 0 := by
    refine integral_zero_ae ?_
    refine Eventually.of_forall fun r hr => ?_
    exact duhamelKernel_of_lt S f (Set.mem_Ioc.mp (Set.uIoc_of_le hsT ▸ hr)).1
  have hhead : ∫ r in (0 : ℝ)..s, duhamelKernel S f (s, r) =
      ∫ r in (0 : ℝ)..s, S.realOperator (s - r) (f r) := by
    refine integral_congr fun r hr => ?_
    have hrI : r ∈ Set.Icc 0 s := by simpa [Set.uIcc_of_le hs0] using hr
    exact duhamelKernel_of_le S f hrI.2
  rw [htail, add_zero, hhead] at hadd
  exact hadd

/-- A vertical slice of the Duhamel kernel: for `r ∈ [0, t]` the integral of the kernel over
`[0, t]` in the first variable is the orbit integral of `f r` up to time `t - r`. -/
private theorem intervalIntegral_duhamelKernel_right (S : StronglyContinuousSemigroup X)
    {f : ℝ → X} (hf : Continuous f) {r t : ℝ} (hr0 : 0 ≤ r) (hrT : r ≤ t) :
    (∫ s in (0 : ℝ)..t, duhamelKernel S f (s, r)) =
      ∫ u in (0 : ℝ)..(t - r), S.realOperator u (f r) := by
  obtain ⟨C, hC0, hC⟩ := norm_realOperator_le_on_Icc S t
  have hint : IntegrableOn (fun s => duhamelKernel S f (s, r)) (Set.Icc 0 t) := by
    have hdom : IntegrableOn (fun _ : ℝ => C * ‖f r‖) (Set.Icc 0 t) :=
      integrableOn_const measure_Icc_lt_top.ne
    refine hdom.mono' ((stronglyMeasurable_duhamelKernel S hf).comp_measurable
      measurable_prodMk_right).aestronglyMeasurable.restrict ?_
    exact ae_restrict_of_forall_mem measurableSet_Icc fun s hs =>
      norm_duhamelKernel_le S f hC0 hC hr0 hs.2
  have hleft : IntervalIntegrable (fun s => duhamelKernel S f (s, r)) volume 0 r :=
    ((Set.uIcc_of_le hr0).symm ▸
      (hint.mono_set (Set.Icc_subset_Icc_right hrT))).intervalIntegrable
  have hright : IntervalIntegrable (fun s => duhamelKernel S f (s, r)) volume r t :=
    ((Set.uIcc_of_le hrT).symm ▸
      (hint.mono_set (Set.Icc_subset_Icc_left hr0))).intervalIntegrable
  have hadd := integral_add_adjacent_intervals (a := (0 : ℝ)) (b := r) (c := t) hleft hright
  have hhead : ∫ s in (0 : ℝ)..r, duhamelKernel S f (s, r) = 0 := by
    refine integral_zero_ae ?_
    refine ae_iff.mpr ?_
    refine measure_mono_null ?_ (measure_singleton r)
    intro s hs
    obtain ⟨hmem, hne⟩ := not_imp.mp hs
    have hmem' : s ∈ Set.Ioc 0 r := by simpa [Set.uIoc_of_le hr0] using hmem
    have hrs : r ≤ s := by
      by_contra hbad
      exact hne (duhamelKernel_of_lt S f (not_le.mp hbad))
    exact le_antisymm hmem'.2 hrs
  have htail : ∫ s in r..t, duhamelKernel S f (s, r) =
      ∫ s in r..t, S.realOperator (s - r) (f r) := by
    refine integral_congr fun s hs => ?_
    have hsI : s ∈ Set.Icc r t := by simpa [Set.uIcc_of_le hrT] using hs
    exact duhamelKernel_of_le S f hsI.1
  rw [hhead, zero_add, htail] at hadd
  have hcomp := integral_comp_sub_right
    (f := fun u => S.realOperator u (f r)) (a := r) (b := t) r
  calc (∫ s in (0 : ℝ)..t, duhamelKernel S f (s, r))
      = ∫ s in r..t, S.realOperator (s - r) (f r) := hadd.symm
    _ = ∫ u in (0 : ℝ)..(t - r), S.realOperator u (f r) := by
        simpa [sub_self] using hcomp

/-- For continuous forcing, the integrated Duhamel term is an iterated orbit integral. The
proof writes both sides as iterated integrals of `duhamelKernel` over `[0, t]²` and swaps the
order of integration. -/
private theorem duhamelIntegral_eq_orbitIntegral (S : StronglyContinuousSemigroup X)
    {f : ℝ → X} (hf : Continuous f) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s, S.realOperator (s - r) (f r)) =
      ∫ r in (0 : ℝ)..t, ∫ u in (0 : ℝ)..(t - r), S.realOperator u (f r) := by
  obtain ⟨C, hC0, hC⟩ := norm_realOperator_le_on_Icc S t
  let F : ℝ → ℝ → X := fun s r => duhamelKernel S f (s, r)
  have hprod : IntegrableOn F.uncurry (Set.uIoc 0 t ×ˢ Set.uIoc 0 t) := by
    have hsub : Set.uIoc 0 t ×ˢ Set.uIoc 0 t ⊆ Set.Icc 0 t ×ˢ Set.Icc 0 t := by
      rw [Set.uIoc_of_le ht]
      exact Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self
    exact (integrableOn_duhamelKernel S hf hC0 hC).mono_set hsub
  calc (∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s, S.realOperator (s - r) (f r))
      = ∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..t, F s r := by
        refine integral_congr fun s hs => ?_
        have hsI : s ∈ Set.Icc 0 t := by simpa [Set.uIcc_of_le ht] using hs
        exact intervalIntegral_duhamelKernel_left S hf hsI.1 hsI.2
    _ = ∫ r in (0 : ℝ)..t, ∫ s in (0 : ℝ)..t, F s r :=
        intervalIntegral_intervalIntegral_swap hprod
    _ = ∫ r in (0 : ℝ)..t, ∫ u in (0 : ℝ)..(t - r), S.realOperator u (f r) := by
        refine integral_congr fun r hr => ?_
        have hrI : r ∈ Set.Icc 0 t := by simpa [Set.uIcc_of_le ht] using hr
        exact intervalIntegral_duhamelKernel_right S hf hrI.1 hrI.2

/-- A positive time shift of the integrated Duhamel term, for continuous forcing. -/
private theorem duhamelPrimitive_shift (S : StronglyContinuousSemigroup X) {f : ℝ → X}
    (hf : Continuous f) {t h : ℝ} (ht : 0 ≤ t) (hh : 0 < h) :
    S.realOperator h (∫ s in (0 : ℝ)..t,
        ∫ r in (0 : ℝ)..s, S.realOperator (s - r) (f r)) -
      ∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s, S.realOperator (s - r) (f r) =
      (∫ step in (0 : ℝ)..h, S.realOperator step
          (∫ r in (0 : ℝ)..t, S.realOperator (t - r) (f r))) -
        ∫ step in (0 : ℝ)..h, S.realOperator step (∫ r in (0 : ℝ)..t, f r) := by
  let inner : ℝ → X := fun r => ∫ u in (0 : ℝ)..(t - r), S.realOperator u (f r)
  have hinner : Continuous inner :=
    (continuous_orbitIntegral S).comp ((continuous_const.sub continuous_id).prodMk hf)
  have hpush : S.realOperator h (∫ r in (0 : ℝ)..t, inner r) =
      ∫ r in (0 : ℝ)..t, S.realOperator h (inner r) :=
    ((S.realOperator h).intervalIntegral_comp_comm (hinner.intervalIntegrable 0 t)).symm
  let forward : ℝ → X := fun r =>
    ∫ step in (0 : ℝ)..h, S.realOperator step (S.realOperator (t - r) (f r))
  let backward : ℝ → X := fun r => ∫ step in (0 : ℝ)..h, S.realOperator step (f r)
  have hforwardCont : Continuous forward := by
    have huncurry : Continuous fun q : ℝ × ℝ =>
        S.realOperator q.2 (S.realOperator (t - q.1) (f q.1)) :=
      (continuous_prod_realOperator S).comp (continuous_snd.prodMk
        ((continuous_prod_realOperator S).comp
          ((continuous_const.sub continuous_fst).prodMk (hf.comp continuous_fst))))
    exact continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
      (f := fun r step => S.realOperator step (S.realOperator (t - r) (f r)))
      huncurry 0 h
  have hbackwardCont : Continuous backward := by
    have huncurry : Continuous fun q : ℝ × ℝ => S.realOperator q.2 (f q.1) :=
      (continuous_prod_realOperator S).comp (continuous_snd.prodMk (hf.comp continuous_fst))
    exact continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
      (f := fun r step => S.realOperator step (f r)) huncurry 0 h
  have hpoint : ∀ r ∈ Set.Icc 0 t, S.realOperator h (inner r) - inner r =
      forward r - backward r := by
    intro r hr
    have hshift := orbitIntegral_shift S (f r) (sub_nonneg.mpr hr.2) hh
    have hlength : h + (t - r) = t - r + h := add_comm _ _
    have hchange := integral_comp_add_right
      (f := fun u => S.realOperator u (f r)) (a := (0 : ℝ)) (b := h) (d := t - r)
    rw [zero_add, hlength] at hchange
    have hsem : (∫ step in (0 : ℝ)..h, S.realOperator (step + (t - r)) (f r)) =
        forward r := by
      refine integral_congr fun step hs => ?_
      have hs0 : 0 ≤ step :=
        (Set.mem_Icc.mp (Set.uIcc_of_le hh.le ▸ hs)).1
      exact S.realOperator_add_apply step (t - r) hs0 (sub_nonneg.mpr hr.2) (f r)
    calc S.realOperator h (inner r) - inner r
        = (∫ u in (t - r)..(t - r + h), S.realOperator u (f r)) -
            ∫ u in (0 : ℝ)..h, S.realOperator u (f r) := by simpa [inner] using hshift
      _ = forward r - backward r := by
          rw [← hchange, hsem]
  have hcontPush : Continuous fun r => S.realOperator h (inner r) :=
    (S.realOperator h).continuous.comp hinner
  rw [duhamelIntegral_eq_orbitIntegral S hf ht, hpush,
    ← integral_sub (f := fun r => S.realOperator h (inner r)) (g := inner)
      (hcontPush.intervalIntegrable 0 t) (hinner.intervalIntegrable 0 t)]
  have hcongr : (∫ r in (0 : ℝ)..t, S.realOperator h (inner r) - inner r) =
      ∫ r in (0 : ℝ)..t, forward r - backward r := by
    refine integral_congr fun r hr => ?_
    exact hpoint r (Set.mem_Icc.mp (Set.uIcc_of_le ht ▸ hr))
  rw [hcongr, integral_sub (hforwardCont.intervalIntegrable 0 t)
    (hbackwardCont.intervalIntegrable 0 t)]
  have hforwardSwap : (∫ r in (0 : ℝ)..t, forward r) =
      ∫ step in (0 : ℝ)..h, S.realOperator step
        (∫ r in (0 : ℝ)..t, S.realOperator (t - r) (f r)) := by
    let G : ℝ → ℝ → X := fun r step =>
      S.realOperator step (S.realOperator (t - r) (f r))
    have hG : IntegrableOn G.uncurry (Set.uIoc 0 t ×ˢ Set.uIoc 0 h) := by
      let explicit : ℝ × ℝ → X := fun q =>
        S.realOperator q.2 (S.realOperator (t - q.1) (f q.1))
      have hcont : Continuous explicit :=
        (continuous_prod_realOperator S).comp (continuous_snd.prodMk
          ((continuous_prod_realOperator S).comp
            ((continuous_const.sub continuous_fst).prodMk (hf.comp continuous_fst))))
      have hsquare : IntegrableOn explicit (Set.Icc 0 t ×ˢ Set.Icc 0 h) :=
        hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      have hsub : Set.uIoc 0 t ×ˢ Set.uIoc 0 h ⊆ Set.Icc 0 t ×ˢ Set.Icc 0 h := by
        rw [Set.uIoc_of_le ht, Set.uIoc_of_le hh.le]
        exact Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self
      have hEq : G.uncurry = explicit := by
        ext q
        rw [Function.uncurry]
      exact hEq.symm ▸ hsquare.mono_set hsub
    rw [show forward = fun r => ∫ step in (0 : ℝ)..h, G r step by rfl,
      intervalIntegral_intervalIntegral_swap (F := G) hG]
    refine integral_congr fun step _ => ?_
    exact (S.realOperator step).intervalIntegral_comp_comm
      (((continuous_prod_realOperator S).comp
        ((continuous_const.sub continuous_id).prodMk hf)).intervalIntegrable 0 t)
  have hbackwardSwap : (∫ r in (0 : ℝ)..t, backward r) =
      ∫ step in (0 : ℝ)..h, S.realOperator step (∫ r in (0 : ℝ)..t, f r) := by
    let H : ℝ → ℝ → X := fun r step => S.realOperator step (f r)
    have hH : IntegrableOn H.uncurry (Set.uIoc 0 t ×ˢ Set.uIoc 0 h) := by
      let explicit : ℝ × ℝ → X := fun q => S.realOperator q.2 (f q.1)
      have hcont : Continuous explicit :=
        (continuous_prod_realOperator S).comp
          (continuous_snd.prodMk (hf.comp continuous_fst))
      have hsquare : IntegrableOn explicit (Set.Icc 0 t ×ˢ Set.Icc 0 h) :=
        hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      have hsub : Set.uIoc 0 t ×ˢ Set.uIoc 0 h ⊆ Set.Icc 0 t ×ˢ Set.Icc 0 h := by
        rw [Set.uIoc_of_le ht, Set.uIoc_of_le hh.le]
        exact Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self
      have hEq : H.uncurry = explicit := by
        ext q
        rw [Function.uncurry]
      exact hEq.symm ▸ hsquare.mono_set hsub
    rw [show backward = fun r => ∫ step in (0 : ℝ)..h, H r step by rfl,
      intervalIntegral_intervalIntegral_swap (F := H) hH]
    refine integral_congr fun step _ => ?_
    exact (S.realOperator step).intervalIntegral_comp_comm (hf.intervalIntegrable 0 t)
  rw [hforwardSwap, hbackwardSwap]

/-- Globally continuous forcing makes the variation-of-constants trajectory continuous. -/
private theorem continuous_forcedSemigroupTrajectory (S : StronglyContinuousSemigroup X) (x : X)
    {f : ℝ → X} (hf : Continuous f) :
    Continuous (forcedSemigroupTrajectory S x f) := by
  have hfun : forcedSemigroupTrajectory S x f =
      fun t => S.realOperator t x + ∫ s in (0 : ℝ)..t, S.realOperator (t - s) (f s) := rfl
  rw [hfun]
  exact (S.continuous_realOperator_apply x).add (continuous_duhamel S hf)

/-- Difference quotients of the integrated Duhamel term tend to that term minus the forcing
integral. -/
private theorem tendsto_quot_duhamelIntegral (S : StronglyContinuousSemigroup X) {f : ℝ → X}
    (hf : Continuous f) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun h : ℝ => (1 / h) •
        (S.realOperator h (∫ s in (0 : ℝ)..t,
            ∫ r in (0 : ℝ)..s, S.realOperator (s - r) (f r)) -
          ∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s, S.realOperator (s - r) (f r)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((∫ r in (0 : ℝ)..t, S.realOperator (t - r) (f r)) -
        ∫ r in (0 : ℝ)..t, f r)) := by
  set y : X := ∫ r in (0 : ℝ)..t, S.realOperator (t - r) (f r)
  set z : X := ∫ r in (0 : ℝ)..t, f r
  refine ((tendsto_average_interval_zero S y).sub
    (tendsto_average_interval_zero S z)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [← smul_sub, duhamelPrimitive_shift S hf ht.le hh]

omit [CompleteSpace X] in
/-- At time zero the variation-of-constants trajectory satisfies the integrated generator
equation, since both integrals over `[0, 0]` vanish. -/
private theorem integrated_at_zero (S : StronglyContinuousSemigroup X) (x : X) (f : ℝ → X) :
    ∃ h : (∫ s in (0 : ℝ)..0, forcedSemigroupTrajectory S x f s) ∈ S.generator.domain,
      forcedSemigroupTrajectory S x f 0 =
        x + S.generator ⟨∫ s in (0 : ℝ)..0, forcedSemigroupTrajectory S x f s, h⟩ +
          ∫ s in (0 : ℝ)..0, f s := by
  let u : ℝ → X := forcedSemigroupTrajectory S x f
  have hzero : (∫ s in (0 : ℝ)..0, u s) = 0 := integral_same
  have hmemU : (∫ s in (0 : ℝ)..0, u s) ∈ S.generator.domain := by
    rw [hzero]
    exact S.generator.domain.zero_mem
  have hpack : (⟨∫ s in (0 : ℝ)..0, u s, hmemU⟩ : S.generator.domain) = 0 :=
    Subtype.ext hzero
  have hA : S.generator ⟨∫ s in (0 : ℝ)..0, u s, hmemU⟩ = 0 := by
    rw [hpack]
    exact S.generator.map_zero
  have hu0 : u 0 = x := by
    simp [u, forcedSemigroupTrajectory, integral_same]
  have heq : u 0 = x + S.generator ⟨∫ s in (0 : ℝ)..0, u s, hmemU⟩ +
      ∫ s in (0 : ℝ)..0, f s := by
    rw [hu0, hA, integral_same, add_zero, add_zero]
  exact ⟨hmemU, heq⟩

/-- At each nonnegative time, continuous forcing satisfies the integrated generator equation. -/
private theorem integrated_at_of_continuous (S : StronglyContinuousSemigroup X) (x : X)
    {f : ℝ → X} (hf : Continuous f) {t : ℝ} (ht : 0 ≤ t) :
    ∃ h : (∫ s in (0 : ℝ)..t, forcedSemigroupTrajectory S x f s) ∈ S.generator.domain,
      forcedSemigroupTrajectory S x f t =
        x + S.generator ⟨∫ s in (0 : ℝ)..t, forcedSemigroupTrajectory S x f s, h⟩ +
          ∫ s in (0 : ℝ)..t, f s := by
  let u : ℝ → X := forcedSemigroupTrajectory S x f
  rcases ht.eq_or_lt with rfl | ht
  · exact integrated_at_zero S x f
  · let orbit : ℝ → X := fun s => S.realOperator s x
    let duh : ℝ → X := fun s => ∫ r in (0 : ℝ)..s, S.realOperator (s - r) (f r)
    have hintO : IntervalIntegrable orbit volume 0 t :=
      (S.continuous_realOperator_apply x).intervalIntegrable 0 t
    have hintD : IntervalIntegrable duh volume 0 t :=
      (continuous_duhamel S hf).intervalIntegrable 0 t
    let Iorb : X := ∫ s in (0 : ℝ)..t, orbit s
    let Iduh : X := ∫ s in (0 : ℝ)..t, duh s
    have hsplit : (∫ s in (0 : ℝ)..t, u s) = Iorb + Iduh := by
      simpa [u, orbit, duh, Iorb, Iduh, forcedSemigroupTrajectory] using integral_add hintO hintD
    have hmemO : Iorb ∈ S.domain := by
      rw [show Iorb = ∫ s in Set.Ioc 0 t, S.realOperator s x by
        simpa [Iorb, orbit] using (integral_of_le ht.le)]
      exact S.integral_orbit_mem_domain x t
    have hmemO' : Iorb ∈ S.generator.domain := by
      rw [S.generator_domain]
      exact hmemO
    have hpackO : (⟨Iorb, hmemO'⟩ : S.generator.domain) =
        ⟨∫ s in Set.Ioc 0 t, S.realOperator s x, by
          rw [S.generator_domain]
          exact S.integral_orbit_mem_domain x t⟩ := by
      apply Subtype.ext
      simpa [Iorb, orbit] using (integral_of_le ht.le)
    have hAO : S.generator ⟨Iorb, hmemO'⟩ = S.realOperator t x - x := by
      rw [hpackO]
      exact S.generator_integral_orbit x t
    have htend := tendsto_quot_duhamelIntegral S hf ht
    have hmemD : Iduh ∈ S.domain :=
      (S.mem_domain_iff_tendsto Iduh).mpr ⟨_, by simpa [Iduh, duh] using htend⟩
    have hmemD' : Iduh ∈ S.generator.domain := by
      rw [S.generator_domain]
      exact hmemD
    have hpackD : (⟨Iduh, hmemD'⟩ : S.generator.domain) =
        ⟨Iduh, by rw [S.generator_domain]; exact hmemD⟩ := Subtype.ext rfl
    have hAD : S.generator ⟨Iduh, hmemD'⟩ =
        duh t - ∫ r in (0 : ℝ)..t, f r := by
      rw [hpackD]
      simpa [Iduh, duh] using S.generator_eq_of_tendsto hmemD (by simpa [Iduh, duh] using htend)
    have hmemSum : Iorb + Iduh ∈ S.generator.domain :=
      S.generator.domain.add_mem hmemO' hmemD'
    have hsumSub : (⟨Iorb + Iduh, hmemSum⟩ : S.generator.domain) =
        (⟨Iorb, hmemO'⟩ : S.generator.domain) + ⟨Iduh, hmemD'⟩ := by
      apply Subtype.ext
      rw [Submodule.coe_add]
    have hAsum : S.generator ⟨Iorb + Iduh, hmemSum⟩ =
        (S.realOperator t x - x) + (duh t - ∫ r in (0 : ℝ)..t, f r) := by
      rw [hsumSub, LinearPMap.map_add, hAO, hAD]
    have hmemU : (∫ s in (0 : ℝ)..t, u s) ∈ S.generator.domain := by
      rw [hsplit]
      exact hmemSum
    have hpack : (⟨∫ s in (0 : ℝ)..t, u s, hmemU⟩ : S.generator.domain) =
        ⟨Iorb + Iduh, hmemSum⟩ := Subtype.ext hsplit
    have hshift : (S.realOperator t x - x) + (duh t - ∫ r in (0 : ℝ)..t, f r) =
        u t - x - ∫ r in (0 : ℝ)..t, f r := by
      have hu : u t = S.realOperator t x + duh t := by
        simp [u, duh, forcedSemigroupTrajectory]
      calc (S.realOperator t x - x) + (duh t - ∫ r in (0 : ℝ)..t, f r)
          = S.realOperator t x - x + duh t - ∫ r in (0 : ℝ)..t, f r := by
              rw [← add_sub_assoc]
        _ = S.realOperator t x + duh t - x - ∫ r in (0 : ℝ)..t, f r := by
              rw [sub_add_eq_add_sub]
        _ = u t - x - ∫ r in (0 : ℝ)..t, f r := by rw [hu]
    have hgen : S.generator ⟨∫ s in (0 : ℝ)..t, u s, hmemU⟩ =
        u t - x - ∫ r in (0 : ℝ)..t, f r := by
      rw [hpack, hAsum, hshift]
    have heq : u t = x + S.generator ⟨∫ s in (0 : ℝ)..t, u s, hmemU⟩ +
        ∫ r in (0 : ℝ)..t, f r := by
      rw [hgen, add_assoc, sub_add_cancel, add_comm x (u t - x), sub_add_cancel]
    exact ⟨hmemU, heq⟩

/-- Continuous forcing produces an integrated solution on every compact time interval. -/
private theorem integrated_of_continuous (S : StronglyContinuousSemigroup X) (T : ℝ)
    (x : X) {f : ℝ → X} (hf : Continuous f) :
    IsIntegratedSemigroupSolution S x f (forcedSemigroupTrajectory S x f) T := by
  refine ⟨(continuous_forcedSemigroupTrajectory S x hf).continuousOn, fun t ht => ?_⟩
  simpa using integrated_at_of_continuous S x hf ht.1

/-- An operator-norm bound controls the difference of two Duhamel integrals. -/
private theorem norm_duhamel_sub_le (S : StronglyContinuousSemigroup X) {T C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ s : ℝ, 0 ≤ s → s ≤ T → ‖S.realOperator s‖ ≤ C)
    {f g : ℝ → X} (hf : IntegrableOn f (Set.Icc 0 T)) (hg : IntegrableOn g (Set.Icc 0 T))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖(∫ s in (0 : ℝ)..t, S.realOperator (t - s) (g s)) -
        ∫ s in (0 : ℝ)..t, S.realOperator (t - s) (f s)‖ ≤
      C * ∫ s in Set.Icc 0 T, ‖g s - f s‖ := by
  have hfg : IntegrableOn (fun s => g s - f s) (Set.Icc 0 T) := hg.sub hf
  have hpiece : IntegrableOn (fun s => g s - f s) (Set.Icc 0 t) :=
    hfg.mono_set (Set.Icc_subset_Icc_right htT)
  have hintDiff : IntervalIntegrable (fun s => g s - f s) volume 0 t :=
    ((Set.uIcc_of_le ht0).symm ▸ hpiece).intervalIntegrable
  have hSg : IntegrableOn (fun s => S.realOperator (t - s) (g s)) (Set.Icc 0 t) :=
    integrableOn_duhamelIntegrand S hg htT
  have hSf : IntegrableOn (fun s => S.realOperator (t - s) (f s)) (Set.Icc 0 t) :=
    integrableOn_duhamelIntegrand S hf htT
  have hintG : IntervalIntegrable (fun s => S.realOperator (t - s) (g s)) volume 0 t :=
    ((Set.uIcc_of_le ht0).symm ▸ hSg).intervalIntegrable
  have hintF : IntervalIntegrable (fun s => S.realOperator (t - s) (f s)) volume 0 t :=
    ((Set.uIcc_of_le ht0).symm ▸ hSf).intervalIntegrable
  have hvec : IntegrableOn (fun s => S.realOperator (t - s) (g s - f s)) (Set.Icc 0 t) :=
    integrableOn_duhamelIntegrand S hfg htT
  have hpoint : (∫ s in (0 : ℝ)..t, S.realOperator (t - s) (g s - f s)) =
      (∫ s in (0 : ℝ)..t, S.realOperator (t - s) (g s)) -
        ∫ s in (0 : ℝ)..t, S.realOperator (t - s) (f s) := by
    refine Eq.trans (integral_congr fun s _ => ?_) (integral_sub hintG hintF)
    exact (S.realOperator (t - s)).map_sub (g s) (f s)
  rw [← hpoint]
  have hnormOn : IntegrableOn (fun s => ‖S.realOperator (t - s) (g s - f s)‖) (Set.Icc 0 t) :=
    hvec.norm
  have hmulOn : IntegrableOn (fun s => C * ‖g s - f s‖) (Set.Icc 0 t) :=
    hpiece.norm.const_mul C
  have hnorm1 : IntervalIntegrable (fun s => ‖S.realOperator (t - s) (g s - f s)‖) volume 0 t :=
    ((Set.uIcc_of_le ht0).symm ▸ hnormOn).intervalIntegrable
  have hnorm2 : IntervalIntegrable (fun s => C * ‖g s - f s‖) volume 0 t :=
    ((Set.uIcc_of_le ht0).symm ▸ hmulOn).intervalIntegrable
  have hbound : ∀ s ∈ Set.Icc 0 t, ‖S.realOperator (t - s) (g s - f s)‖ ≤ C * ‖g s - f s‖ := by
    intro s hs
    have hs0 : 0 ≤ t - s := sub_nonneg.mpr hs.2
    have hsT : t - s ≤ T := by linarith [hs.1, htT]
    exact le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_right (hC _ hs0 hsT) (norm_nonneg _))
  have hmono := integral_mono_on ht0 hnorm1 hnorm2 hbound
  rw [intervalIntegral.integral_const_mul] at hmono
  have htail : (∫ s in (0 : ℝ)..t, ‖g s - f s‖) ≤ ∫ s in Set.Icc 0 T, ‖g s - f s‖ := by
    rw [integral_of_le ht0]
    refine setIntegral_mono_set hfg.norm ?_ ?_
    · exact ae_restrict_of_forall_mem measurableSet_Icc fun _ _ => norm_nonneg _
    · exact ae_of_all volume
        (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_right htT))
  calc ‖∫ s in (0 : ℝ)..t, S.realOperator (t - s) (g s - f s)‖
      ≤ ∫ s in (0 : ℝ)..t, ‖S.realOperator (t - s) (g s - f s)‖ :=
        norm_integral_le_integral_norm ht0
    _ ≤ C * ∫ s in (0 : ℝ)..t, ‖g s - f s‖ := hmono
    _ ≤ C * ∫ s in Set.Icc 0 T, ‖g s - f s‖ :=
        mul_le_mul_of_nonneg_left htail hC0

omit [CompleteSpace X] in
/-- The plain time integral is controlled by the L¹ norm on the ambient interval. -/
private theorem norm_intervalIntegral_sub_le {T : ℝ}
    {f g : ℝ → X} (hf : IntegrableOn f (Set.Icc 0 T)) (hg : IntegrableOn g (Set.Icc 0 T))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖(∫ s in (0 : ℝ)..t, g s) - ∫ s in (0 : ℝ)..t, f s‖ ≤
      ∫ s in Set.Icc 0 T, ‖g s - f s‖ := by
  have hfg : IntegrableOn (fun s => g s - f s) (Set.Icc 0 T) := hg.sub hf
  have hintG : IntervalIntegrable g volume 0 t :=
    ((Set.uIcc_of_le ht0).symm ▸ hg.mono_set (Set.Icc_subset_Icc_right htT)).intervalIntegrable
  have hintF : IntervalIntegrable f volume 0 t :=
    ((Set.uIcc_of_le ht0).symm ▸ hf.mono_set (Set.Icc_subset_Icc_right htT)).intervalIntegrable
  rw [← integral_sub hintG hintF]
  calc ‖∫ s in (0 : ℝ)..t, g s - f s‖
      ≤ ∫ s in (0 : ℝ)..t, ‖g s - f s‖ := norm_integral_le_integral_norm ht0
    _ ≤ ∫ s in Set.Icc 0 T, ‖g s - f s‖ := by
        rw [integral_of_le ht0]
        refine setIntegral_mono_set hfg.norm ?_ ?_
        · exact ae_restrict_of_forall_mem measurableSet_Icc fun _ _ => norm_nonneg _
        · exact ae_of_all volume
            (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_right htT))

omit [CompleteSpace X] in
/-- Integrable forcing on `[0, T]` is an `L¹` limit of bounded continuous forcings, at rate
`1 / (n + 1)`. -/
private theorem exists_seq_boundedContinuous_integral_sub_le {T : ℝ} {f : ℝ → X}
    (hf : IntegrableOn f (Set.Icc 0 T)) :
    ∃ g : ℕ → ℝ →ᵇ X, ∀ n, IntegrableOn (g n : ℝ → X) (Set.Icc 0 T) ∧
      ∫ s in Set.Icc 0 T, ‖(g n : ℝ → X) s - f s‖ ≤ 1 / ((n : ℝ) + 1) := by
  have : Measure.WeaklyRegular (volume.restrict (Set.Icc 0 T)) :=
    Measure.WeaklyRegular.restrict_of_measure_ne_top measure_Icc_lt_top.ne
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n =>
    div_pos one_pos (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) one_pos)
  choose g hg using fun n => hf.exists_boundedContinuous_integral_sub_le (hpos n)
  refine ⟨g, fun n => ⟨(hg n).2, ?_⟩⟩
  rw [setIntegral_congr_fun measurableSet_Icc fun s _ => norm_sub_rev ((g n : ℝ → X) s) (f s)]
  simpa using (hg n).1

/-- Forcings that are `δ`-close in `L¹` on `[0, T]` give trajectories that are `C * δ`-close
on `[0, T]`, where `C` bounds the semigroup on `[0, T]`. -/
private theorem norm_forcedSemigroupTrajectory_sub_le (S : StronglyContinuousSemigroup X)
    {T C δ : ℝ} (hC0 : 0 ≤ C) (hC : ∀ s : ℝ, 0 ≤ s → s ≤ T → ‖S.realOperator s‖ ≤ C)
    {f g : ℝ → X} (hf : IntegrableOn f (Set.Icc 0 T)) (hg : IntegrableOn g (Set.Icc 0 T))
    (hδ : ∫ s in Set.Icc 0 T, ‖g s - f s‖ ≤ δ) (x : X) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖forcedSemigroupTrajectory S x g t - forcedSemigroupTrajectory S x f t‖ ≤ C * δ := by
  simp only [forcedSemigroupTrajectory, add_sub_add_left_eq_sub]
  exact (norm_duhamel_sub_le S hC0 hC hf hg ht0 htT).trans (mul_le_mul_of_nonneg_left hδ hC0)

/-- Closedness of the generator passes the integrated generator equation at time `t` to the
limit: if the time integrals, the values at `t` and the forcing integrals converge, the limit
path satisfies the equation at `t`. -/
private theorem integrated_at_of_tendsto (S : StronglyContinuousSemigroup X) (x : X) {t : ℝ}
    {u f : ℝ → X} {un fn : ℕ → ℝ → X}
    (hInt : Tendsto (fun n => ∫ s in (0 : ℝ)..t, un n s) atTop
      (nhds (∫ s in (0 : ℝ)..t, u s)))
    (hVal : Tendsto (fun n => un n t) atTop (nhds (u t)))
    (hForce : Tendsto (fun n => ∫ s in (0 : ℝ)..t, fn n s) atTop
      (nhds (∫ s in (0 : ℝ)..t, f s)))
    (happrox : ∀ n, ∃ h : (∫ s in (0 : ℝ)..t, un n s) ∈ S.generator.domain,
      un n t = x + S.generator ⟨∫ s in (0 : ℝ)..t, un n s, h⟩ + ∫ s in (0 : ℝ)..t, fn n s) :
    ∃ h : (∫ s in (0 : ℝ)..t, u s) ∈ S.generator.domain,
      u t = x + S.generator ⟨∫ s in (0 : ℝ)..t, u s, h⟩ + ∫ s in (0 : ℝ)..t, f s := by
  have hRight : Tendsto (fun n => un n t - x - ∫ s in (0 : ℝ)..t, fn n s)
      atTop (nhds (u t - x - ∫ s in (0 : ℝ)..t, f s)) :=
    (hVal.sub tendsto_const_nhds).sub hForce
  let pair : ℕ → X × X := fun n =>
    (∫ s in (0 : ℝ)..t, un n s, un n t - x - ∫ s in (0 : ℝ)..t, fn n s)
  have hpair : Tendsto pair atTop
      (nhds (∫ s in (0 : ℝ)..t, u s, u t - x - ∫ s in (0 : ℝ)..t, f s)) := by
    rw [nhds_prod_eq]
    exact hInt.prodMk hRight
  have hgraph : ∀ n, pair n ∈ S.generator.graph := by
    intro n
    obtain ⟨hmem, heq⟩ := happrox n
    rw [LinearPMap.mem_graph_iff]
    refine ⟨⟨∫ s in (0 : ℝ)..t, un n s, hmem⟩, rfl, ?_⟩
    have hA : un n t - x - ∫ s in (0 : ℝ)..t, fn n s =
        S.generator ⟨∫ s in (0 : ℝ)..t, un n s, hmem⟩ := by
      rw [heq, add_assoc, add_sub_cancel_left, add_sub_cancel_right]
    exact hA.symm
  have hlimSet := S.isClosed_generator.mem_of_tendsto hpair
    (Filter.Eventually.of_forall hgraph)
  have hlim : (∫ s in (0 : ℝ)..t, u s, u t - x - ∫ s in (0 : ℝ)..t, f s) ∈
      S.generator.graph := by
    simpa [SetLike.mem_coe] using hlimSet
  rw [LinearPMap.mem_graph_iff] at hlim
  obtain ⟨y, hy1, hy2⟩ := hlim
  have hyInt : (y : X) = ∫ s in (0 : ℝ)..t, u s := by simpa using hy1
  have hyVal : S.generator y = u t - x - ∫ s in (0 : ℝ)..t, f s := by simpa using hy2
  have hmem : (∫ s in (0 : ℝ)..t, u s) ∈ S.generator.domain := by
    rw [← hyInt]
    exact y.property
  have hpack : (⟨∫ s in (0 : ℝ)..t, u s, hmem⟩ : S.generator.domain) = y :=
    Subtype.ext hyInt.symm
  have hA : S.generator ⟨∫ s in (0 : ℝ)..t, u s, hmem⟩ =
      u t - x - ∫ s in (0 : ℝ)..t, f s := by
    rw [hpack]
    exact hyVal
  have heq : u t = x + S.generator ⟨∫ s in (0 : ℝ)..t, u s, hmem⟩ +
      ∫ s in (0 : ℝ)..t, f s := by
    rw [hA, add_assoc, sub_add_cancel, add_comm x (u t - x), sub_add_cancel]
  exact ⟨hmem, heq⟩

/-- Integrable forcing still produces an integrated solution, by L¹ approximation and closedness
of the generator. -/
theorem isIntegratedSemigroupSolution_forcedSemigroupTrajectory
    (S : StronglyContinuousSemigroup X) {T : ℝ}
    (x : X) {f : ℝ → X} (hf : IntegrableOn f (Set.Icc 0 T)) :
    IsIntegratedSemigroupSolution S x f (forcedSemigroupTrajectory S x f) T := by
  obtain ⟨C, hC0, hC⟩ := norm_realOperator_le_on_Icc S T
  obtain ⟨approx, happrox⟩ := exists_seq_boundedContinuous_integral_sub_le hf
  have hto0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) := by
    have hinv : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) :=
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).inv_tendsto_atTop
    refine hinv.congr fun n => ?_
    rw [Nat.cast_add, Nat.cast_one, one_div]
  have hCto0 : Tendsto (fun n : ℕ => C * (1 / ((n : ℝ) + 1))) atTop (nhds 0) := by
    simpa only [mul_zero] using hto0.const_mul C
  have hclose : ∀ n, ∀ t, 0 ≤ t → t ≤ T →
      ‖forcedSemigroupTrajectory S x (approx n) t - forcedSemigroupTrajectory S x f t‖ ≤
        C * (1 / ((n : ℝ) + 1)) := fun n _ ht0 htT =>
    norm_forcedSemigroupTrajectory_sub_le S hC0 hC hf (happrox n).1 (happrox n).2 x ht0 htT
  let u : ℝ → X := forcedSemigroupTrajectory S x f
  have huniform : TendstoUniformlyOn (fun n t => forcedSemigroupTrajectory S x (approx n) t) u
      atTop (Set.Icc 0 T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    refine (hCto0.eventually (Iio_mem_nhds hε)).mono fun n hn t ht => ?_
    rw [dist_eq_norm, norm_sub_rev]
    exact lt_of_le_of_lt (hclose n t ht.1 ht.2) hn
  have hcont : ContinuousOn u (Set.Icc 0 T) :=
    huniform.continuousOn (Frequently.of_forall fun n =>
      (continuous_forcedSemigroupTrajectory S x (approx n).continuous).continuousOn)
  refine ⟨hcont, fun t ht => ?_⟩
  rcases ht.1.eq_or_lt with rfl | ht0
  · exact integrated_at_zero S x f
  have htT : t ≤ T := ht.2
  let un : ℕ → ℝ → X := fun n => forcedSemigroupTrajectory S x (approx n)
  have hintU : IntervalIntegrable u volume 0 t :=
    (hcont.mono (Set.Icc_subset_Icc_right htT)).intervalIntegrable_of_Icc ht0.le
  have hintUn : ∀ n, IntervalIntegrable (un n) volume 0 t := fun n =>
    (continuous_forcedSemigroupTrajectory S x (approx n).continuous).intervalIntegrable 0 t
  have hInt : Tendsto (fun n => ∫ s in (0 : ℝ)..t, un n s) atTop
      (nhds (∫ s in (0 : ℝ)..t, u s)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (g := fun n : ℕ => C * (1 / ((n : ℝ) + 1)) * t)
      (fun n : ℕ => norm_nonneg
        ((∫ s in (0 : ℝ)..t, un n s) - ∫ s in (0 : ℝ)..t, u s))
      (fun n => ?_) ?_
    · rw [← integral_sub (hintUn n) hintU]
      have hle := norm_integral_le_of_norm_le_const
        (fun s hs => hclose n s (le_of_lt (Set.mem_Ioc.mp (Set.uIoc_of_le ht0.le ▸ hs)).1)
          (le_trans (Set.mem_Ioc.mp (Set.uIoc_of_le ht0.le ▸ hs)).2 htT))
      simpa [sub_zero, abs_of_nonneg ht0.le] using hle
    · simpa only [zero_mul] using hCto0.mul_const t
  have hForce : Tendsto (fun n => ∫ s in (0 : ℝ)..t, (approx n : ℝ → X) s) atTop
      (nhds (∫ s in (0 : ℝ)..t, f s)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hto0
    exact le_trans (norm_intervalIntegral_sub_le hf (happrox n).1 ht0.le htT) (happrox n).2
  have hVal : Tendsto (fun n => un n t) atTop (nhds (u t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => hclose n t ht0.le htT) hCto0
  exact integrated_at_of_tendsto S x hInt hVal hForce fun n =>
    integrated_at_of_continuous S x (approx n).continuous ht0.le

/-- The indefinite integral of a function continuous on `[0, T]` has right derivative equal to
the integrand at each `s ∈ [0, T)`. -/
private theorem primitive_hasDerivWithinAt_Ici {T : ℝ} {d : ℝ → X}
    (hd : ContinuousOn d (Set.Icc 0 T)) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T) :
    HasDerivWithinAt (fun u => ∫ r in (0 : ℝ)..u, d r) (d s) (Set.Ici s) s := by
  have hint : IntervalIntegrable d volume 0 s :=
    (hd.mono (Set.Icc_subset_Icc_right hsT.le)).intervalIntegrable_of_Icc hs0
  have hmeas : StronglyMeasurableAtFilter d (nhdsWithin s (Set.Ioi s)) := by
    refine ⟨Set.Ioo s T, ?_, ?_⟩
    · rw [mem_nhdsWithin]
      refine ⟨Set.Iio T, isOpen_Iio, hsT, ?_⟩
      intro y hy
      exact ⟨hy.2, hy.1⟩
    · refine (hd.mono ?_).aestronglyMeasurable (μ := volume) measurableSet_Ioo
      intro y hy
      exact ⟨hs0.trans (le_of_lt hy.1), hy.2.le⟩
  have hcont : ContinuousWithinAt d (Set.Ioi s) s := by
    refine (hd s ⟨hs0, hsT.le⟩).mono_of_mem_nhdsWithin ?_
    rw [mem_nhdsWithin]
    refine ⟨Set.Iio T, isOpen_Iio, hsT, ?_⟩
    intro y hy
    exact ⟨hs0.trans (le_of_lt hy.2), hy.1.le⟩
  exact integral_hasDerivWithinAt_right (s := Set.Ici s) (t := Set.Ioi s) hint hmeas hcont

/-- The backward semigroup orbit of a generator-domain path cancels the path's right
derivative. The two slopes are the generator applied to the same vector. -/
private theorem hasDerivWithinAt_integratedInterpolate (S : StronglyContinuousSemigroup X)
    {t s : ℝ} {g : ℝ → X} {dx : X} (hmem : g s ∈ S.generator.domain)
    (hA : S.generator ⟨g s, hmem⟩ = dx) (hprim : HasDerivWithinAt g dx (Set.Ici s) s)
    (hst : s < t) :
    HasDerivWithinAt (fun r => S.realOperator (t - r) (g r)) 0 (Set.Ici s) s := by
  let y : S.domain := ⟨g s, by
    rw [← S.generator_domain]
    exact hmem⟩
  have hfull := S.realOperator_hasDerivWithinAt_Ici y (sub_pos.mpr hst).le
  rw [S.realOperator_generator_map (s := t - s) y] at hfull
  have hAy : S.generator ⟨(y : X), by
      rw [S.generator_domain]
      exact y.property⟩ = dx := by
    have hsub : (⟨(y : X), by rw [S.generator_domain]; exact y.property⟩ :
        S.generator.domain) = ⟨g s, hmem⟩ := Subtype.ext rfl
    rw [hsub, hA]
  rw [hAy] at hfull
  have hback : HasDerivWithinAt (fun r => S.realOperator (t - r) (g s))
      (-S.realOperator (t - s) dx) (Set.Ici s) s :=
    ((hfull.hasDerivAt (Ici_mem_nhds (sub_pos.mpr hst))).comp_const_sub t s).hasDerivWithinAt
  rw [hasDerivWithinAt_iff_tendsto_slope, Set.Ici_sdiff_left] at hprim hback ⊢
  have htime : Tendsto (fun r : ℝ => t - r) (nhdsWithin s (Set.Ioi s)) (nhds (t - s)) :=
    ((continuous_sub_left t).tendsto s).mono_left nhdsWithin_le_nhds
  have hlim := S.tendsto_realOperator_apply htime hprim
  have hsum := hlim.add hback
  rw [add_neg_cancel] at hsum
  refine hsum.congr fun r => ?_
  simp only [slope_def_module, map_smul, map_sub, smul_sub]
  abel

/-- Integrated solutions with the same initial value and forcing agree on `[0, T]`. -/
theorem IsIntegratedSemigroupSolution.eqOn {S : StronglyContinuousSemigroup X} {T : ℝ} {x : X}
    {f u v : ℝ → X} (hu : IsIntegratedSemigroupSolution S x f u T)
    (hv : IsIntegratedSemigroupSolution S x f v T) :
    Set.EqOn u v (Set.Icc 0 T) := by
  intro t ht
  let d : ℝ → X := fun s => u s - v s
  have hd : ContinuousOn d (Set.Icc 0 T) := hu.1.sub hv.1
  have hkey : ∀ s ∈ Set.Icc 0 T,
      ∃ h : (∫ r in (0 : ℝ)..s, d r) ∈ S.generator.domain,
        d s = S.generator ⟨∫ r in (0 : ℝ)..s, d r, h⟩ := by
    intro s hs
    obtain ⟨hmu, heqU⟩ := hu.2 s hs
    obtain ⟨hmv, heqV⟩ := hv.2 s hs
    have hintU : IntervalIntegrable u volume 0 s :=
      (hu.1.mono (Set.Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc hs.1
    have hintV : IntervalIntegrable v volume 0 s :=
      (hv.1.mono (Set.Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc hs.1
    have hsubInt : (∫ r in (0 : ℝ)..s, d r) =
        (∫ r in (0 : ℝ)..s, u r) - ∫ r in (0 : ℝ)..s, v r := by
      simpa [d] using integral_sub hintU hintV
    have hmem : (∫ r in (0 : ℝ)..s, d r) ∈ S.generator.domain := by
      rw [hsubInt]
      exact S.generator.domain.sub_mem hmu hmv
    have hpack : (⟨∫ r in (0 : ℝ)..s, d r, hmem⟩ : S.generator.domain) =
        (⟨∫ r in (0 : ℝ)..s, u r, hmu⟩ : S.generator.domain) -
          ⟨∫ r in (0 : ℝ)..s, v r, hmv⟩ := by
      apply Subtype.ext
      rw [Submodule.coe_sub]
      exact hsubInt
    have hgen : S.generator ⟨∫ r in (0 : ℝ)..s, d r, hmem⟩ =
        S.generator ⟨∫ r in (0 : ℝ)..s, u r, hmu⟩ -
          S.generator ⟨∫ r in (0 : ℝ)..s, v r, hmv⟩ := by
      rw [hpack, LinearPMap.map_sub]
    have hdiff : d s = S.generator ⟨∫ r in (0 : ℝ)..s, u r, hmu⟩ -
        S.generator ⟨∫ r in (0 : ℝ)..s, v r, hmv⟩ := by
      unfold d
      rw [heqU, heqV]
      abel
    exact ⟨hmem, hdiff.trans hgen.symm⟩
  obtain ⟨hmem, hAt⟩ := hkey t ht
  have hzero : (∫ r in (0 : ℝ)..t, d r) = 0 := by
    rcases ht.1.eq_or_lt with rfl | htpos
    · exact integral_same
    · let g : ℝ → X := fun s => ∫ r in (0 : ℝ)..s, d r
      have hintD : IntegrableOn d (Set.Icc 0 t) volume :=
        (hd.mono (Set.Icc_subset_Icc_right ht.2)).integrableOn_Icc
      have hintUcc : IntegrableOn d (Set.uIcc 0 t) volume := by
        simpa [Set.uIcc_of_le htpos.le] using hintD
      have hgcont : ContinuousOn g (Set.Icc 0 t) := by
        simpa [g, Set.uIcc_of_le htpos.le] using continuousOn_primitive_interval hintUcc
      have hconst := S.realOperator_apply_eq_of_hasDerivWithinAt_zero (f := fun s => t - s)
        (g := g) (continuous_sub_left t).continuousOn hgcont
        (fun s hs => by
          have hex := hkey s ⟨hs.1, hs.2.le.trans ht.2⟩
          have hgs : g s ∈ S.generator.domain := by simpa [g] using hex.choose
          have hAg : S.generator ⟨g s, hgs⟩ = d s := by
            have hsub : (⟨g s, hgs⟩ : S.generator.domain) =
                ⟨∫ r in (0 : ℝ)..s, d r, hex.choose⟩ := Subtype.ext (by simp [g])
            rw [hsub]
            exact hex.choose_spec.symm
          have hprim : HasDerivWithinAt g (d s) (Set.Ici s) s := by
            simpa [g] using primitive_hasDerivWithinAt_Ici
              (hd.mono (Set.Icc_subset_Icc_right ht.2)) hs.1 hs.2
          exact hasDerivWithinAt_integratedInterpolate S hgs hAg hprim hs.2)
      have happly := hconst t (Set.right_mem_Icc.mpr htpos.le)
      rw [sub_self, sub_zero, S.realOperator_zero_apply, show g 0 = 0 from integral_same,
        (S.realOperator t).map_zero] at happly
      simpa [g] using happly
  have hdt : d t = 0 := by
    rw [hAt]
    have hpack : (⟨∫ r in (0 : ℝ)..t, d r, hmem⟩ : S.generator.domain) = 0 :=
      Subtype.ext hzero
    rw [hpack, S.generator.map_zero]
  unfold d at hdt
  exact sub_eq_zero.mp hdt

end CKMA
