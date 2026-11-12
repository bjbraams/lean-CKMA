/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.Semigroups.Resolvent.Basic
public import TauCeti.Analysis.Semigroups.Generator.Closed
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.Algebra.Module.LinearPMap
import TauCeti.Analysis.Semigroups.Generator.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Abel

/-!
# Inhomogeneous evolution and semigroup approximation

Variation-of-constants trajectories and their integrated and classical generator
equations. Trotter–Kato relates strong resolvent convergence to uniform strong convergence
on bounded time intervals under a common growth bound. Chernoff products are stable
families tangent to the generator on an actual core. Generators, resolvents and core
domains reuse TauCeti's semigroup modules; integration uses Mathlib.
Sources: GAPS 24.13, 24.17 and 24.18.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology TauCeti.Semigroups intervalIntegral
open scoped NNReal BoundedContinuousFunction

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The actual variation-of-constants trajectory, using the upstream real-time semigroup shim. -/
def forcedSemigroupTrajectory (S : StronglyContinuousSemigroup X) (x : X)
    (f : ℝ → X) (t : ℝ) : X := S.realOperator t x + ∫ s in (0 : ℝ)..t, S.realOperator (t - s) (f s)

/-- An integrated solution of `u'=Au+f`, phrased independently of the variation-of-constants
formula. The time integral, rather than every value of `u`, belongs to the generator domain. -/
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
      (Set.Ici 0 ×ˢ Set.univ) := fun p hp =>
    S.tendsto_realOperator_apply
      (continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun q hq => hq.1) hp.1
      (continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hunion := hneg.union_of_isClosed hpos (isClosed_Iic.prod isClosed_univ)
    (isClosed_Ici.prod isClosed_univ)
  rw [← Set.union_prod, Set.Iic_union_Ici, Set.univ_prod_univ] at hunion
  exact continuousOn_univ.mp hunion

/-- An operator-norm bound for the semigroup on a compact time interval `[0, T]`. -/
private theorem norm_realOperator_le_on_Icc (S : StronglyContinuousSemigroup X) {T : ℝ}
    (_hT : 0 ≤ T) :
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
    (hT : 0 ≤ T) {f : ℝ → X} (hf : IntegrableOn f (Set.Icc 0 T)) {t : ℝ} (_ht0 : 0 ≤ t)
    (htT : t ≤ T) :
    IntegrableOn (fun s => S.realOperator (t - s) (f s)) (Set.Icc 0 t) := by
  obtain ⟨C, -, hC⟩ := norm_realOperator_le_on_Icc S hT
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

/-- For continuous forcing, the integrated Duhamel term is an iterated orbit integral. -/
private theorem duhamelIntegral_eq_orbitIntegral (S : StronglyContinuousSemigroup X)
    {f : ℝ → X} (hf : Continuous f) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s, S.realOperator (s - r) (f r)) =
      ∫ r in (0 : ℝ)..t, ∫ u in (0 : ℝ)..(t - r), S.realOperator u (f r) := by
  classical
  obtain ⟨C, hC0, hC⟩ := norm_realOperator_le_on_Icc S ht
  let seminorm : ℝ × ℝ → X := fun p => S.realOperator (p.1 - p.2) (f p.2)
  let kernel : ℝ × ℝ → X := fun p => if p.2 ≤ p.1 then seminorm p else 0
  have hker_pos {s r : ℝ} (hrs : r ≤ s) :
      kernel (s, r) = S.realOperator (s - r) (f r) := by
    simp only [kernel, seminorm, ite_eq_left hrs]
  have hker_neg {s r : ℝ} (hrs : ¬ r ≤ s) : kernel (s, r) = 0 := by
    simp only [kernel, ite_eq_right hrs]
  have hpair : Continuous fun p : ℝ × ℝ => (p.1 - p.2, f p.2) :=
    (continuous_fst.sub continuous_snd).prodMk (hf.comp continuous_snd)
  have hsemi : StronglyMeasurable seminorm :=
    (continuous_prod_realOperator S).comp_stronglyMeasurable hpair.stronglyMeasurable
  have hclosed : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
    (isClosed_le continuous_snd continuous_fst).measurableSet
  have hkernel : StronglyMeasurable kernel :=
    StronglyMeasurable.ite hclosed hsemi stronglyMeasurable_const
  let F : ℝ → ℝ → X := fun s r => kernel (s, r)
  have hFun : F.uncurry = kernel := by
    ext p
    rw [Function.uncurry]
  have hFsm : StronglyMeasurable F.uncurry := by
    rw [hFun]
    exact hkernel
  have hdom_r : IntegrableOn (fun r => C * ‖f r‖) (Set.Icc 0 t) :=
    (continuous_const.mul (continuous_norm.comp hf)).integrableOn_Icc
  have hhoriz_int : ∀ s, 0 ≤ s → s ≤ t →
      IntegrableOn (fun r => kernel (s, r)) (Set.Icc 0 t) := by
    intro s _ hsT
    refine hdom_r.mono' (hFsm.of_uncurry_left (x := s)).aestronglyMeasurable.restrict ?_
    refine ae_restrict_of_forall_mem measurableSet_Icc fun r hr => ?_
    by_cases hrs : r ≤ s
    · have htime0 : 0 ≤ s - r := sub_nonneg.mpr hrs
      have htimeT : s - r ≤ t := by linarith [hr.1, hsT]
      rw [hker_pos hrs]
      calc ‖S.realOperator (s - r) (f r)‖
          ≤ ‖S.realOperator (s - r)‖ * ‖f r‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ C * ‖f r‖ :=
            mul_le_mul_of_nonneg_right (hC _ htime0 htimeT) (norm_nonneg _)
    · rw [hker_neg hrs, norm_zero]
      exact mul_nonneg hC0 (norm_nonneg _)
  have hvert_int : ∀ r, 0 ≤ r → r ≤ t →
      IntegrableOn (fun s => kernel (s, r)) (Set.Icc 0 t) := by
    intro r hr0 hrT
    have hdom : IntegrableOn (fun _ : ℝ => C * ‖f r‖) (Set.Icc 0 t) :=
      integrableOn_const measure_Icc_lt_top.ne
    refine hdom.mono' (hFsm.of_uncurry_right (y := r)).aestronglyMeasurable.restrict ?_
    refine ae_restrict_of_forall_mem measurableSet_Icc fun s hs => ?_
    by_cases hrs : r ≤ s
    · have htime0 : 0 ≤ s - r := sub_nonneg.mpr hrs
      have htimeT : s - r ≤ t := by linarith [hs.2, hr0, hrT]
      rw [hker_pos hrs]
      calc ‖S.realOperator (s - r) (f r)‖
          ≤ ‖S.realOperator (s - r)‖ * ‖f r‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ C * ‖f r‖ :=
            mul_le_mul_of_nonneg_right (hC _ htime0 htimeT) (norm_nonneg _)
    · rw [hker_neg hrs, norm_zero]
      exact mul_nonneg hC0 (norm_nonneg _)
  have hhoriz_eq : ∀ s, 0 ≤ s → s ≤ t →
      (∫ r in (0 : ℝ)..s, S.realOperator (s - r) (f r)) =
        ∫ r in (0 : ℝ)..t, kernel (s, r) := by
    intro s hs0 hsT
    have hleft : IntervalIntegrable (fun r => kernel (s, r)) volume 0 s :=
      ((Set.uIcc_of_le hs0).symm ▸ ((hhoriz_int s hs0 hsT).mono_set
        (Set.Icc_subset_Icc_right hsT))).intervalIntegrable
    have hright : IntervalIntegrable (fun r => kernel (s, r)) volume s t :=
      ((Set.uIcc_of_le hsT).symm ▸ ((hhoriz_int s hs0 hsT).mono_set
        (Set.Icc_subset_Icc_left hs0))).intervalIntegrable
    have hadd := integral_add_adjacent_intervals (a := (0 : ℝ)) (b := s) (c := t) hleft hright
    have htail : ∫ r in s..t, kernel (s, r) = 0 := by
      refine integral_zero_ae ?_
      refine Eventually.of_forall fun r hr => ?_
      have hrgt : s < r := (Set.mem_Ioc.mp (Set.uIoc_of_le hsT ▸ hr)).1
      exact hker_neg (not_le.mpr hrgt)
    have hhead : ∫ r in (0 : ℝ)..s, kernel (s, r) =
        ∫ r in (0 : ℝ)..s, S.realOperator (s - r) (f r) := by
      refine integral_congr fun r hr => ?_
      have hrI : r ∈ Set.Icc 0 s := by simpa [Set.uIcc_of_le hs0] using hr
      exact hker_pos hrI.2
    rw [htail, add_zero, hhead] at hadd
    exact hadd
  have hvert_eq : ∀ r, 0 ≤ r → r ≤ t →
      (∫ s in (0 : ℝ)..t, kernel (s, r)) =
        ∫ u in (0 : ℝ)..(t - r), S.realOperator u (f r) := by
    intro r hr0 hrT
    have hleft : IntervalIntegrable (fun s => kernel (s, r)) volume 0 r :=
      ((Set.uIcc_of_le hr0).symm ▸ ((hvert_int r hr0 hrT).mono_set
        (Set.Icc_subset_Icc_right hrT))).intervalIntegrable
    have hright : IntervalIntegrable (fun s => kernel (s, r)) volume r t :=
      ((Set.uIcc_of_le hrT).symm ▸ ((hvert_int r hr0 hrT).mono_set
        (Set.Icc_subset_Icc_left hr0))).intervalIntegrable
    have hadd := integral_add_adjacent_intervals (a := (0 : ℝ)) (b := r) (c := t) hleft hright
    have hhead : ∫ s in (0 : ℝ)..r, kernel (s, r) = 0 := by
      refine integral_zero_ae ?_
      refine ae_iff.mpr ?_
      refine measure_mono_null ?_ (measure_singleton r)
      intro s hs
      obtain ⟨hmem, hne⟩ := not_imp.mp hs
      have hmem' : s ∈ Set.Ioc 0 r := by simpa [Set.uIoc_of_le hr0] using hmem
      have hrs : r ≤ s := by
        by_contra hbad
        exact hne (hker_neg hbad)
      exact le_antisymm hmem'.2 hrs
    have htail : ∫ s in r..t, kernel (s, r) =
        ∫ s in r..t, S.realOperator (s - r) (f r) := by
      refine integral_congr fun s hs => ?_
      have hsI : s ∈ Set.Icc r t := by simpa [Set.uIcc_of_le hrT] using hs
      exact hker_pos hsI.1
    rw [hhead, zero_add, htail] at hadd
    have hcomp := integral_comp_sub_right
      (f := fun u => S.realOperator u (f r)) (a := r) (b := t) r
    calc (∫ s in (0 : ℝ)..t, kernel (s, r))
        = ∫ s in r..t, S.realOperator (s - r) (f r) := hadd.symm
      _ = ∫ u in (0 : ℝ)..(t - r), S.realOperator u (f r) := by
          simpa [sub_self] using hcomp
  have hleft : (∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s, S.realOperator (s - r) (f r)) =
      ∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..t, F s r := by
    refine integral_congr fun s hs => ?_
    have hsI : s ∈ Set.Icc 0 t := by simpa [Set.uIcc_of_le ht] using hs
    simpa [F] using hhoriz_eq s hsI.1 hsI.2
  have hprod : IntegrableOn F.uncurry (Set.uIoc 0 t ×ˢ Set.uIoc 0 t) := by
    have hsquare : IntegrableOn kernel (Set.Icc 0 t ×ˢ Set.Icc 0 t) := by
      have hdom : IntegrableOn (fun p : ℝ × ℝ => C * ‖f p.2‖)
          (Set.Icc 0 t ×ˢ Set.Icc 0 t) :=
        ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
          (continuous_const.mul
            ((continuous_norm.comp hf).comp continuous_snd)).continuousOn
      refine hdom.mono' hkernel.aestronglyMeasurable.restrict ?_
      refine ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc) fun p hp => ?_
      obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
      obtain ⟨_, hsT⟩ := Set.mem_Icc.mp hp1
      obtain ⟨hr0, _⟩ := Set.mem_Icc.mp hp2
      by_cases hrs : p.2 ≤ p.1
      · have htime0 : 0 ≤ p.1 - p.2 := sub_nonneg.mpr hrs
        have htimeT : p.1 - p.2 ≤ t := by linarith
        rw [show kernel p = seminorm p by simp only [kernel, ite_eq_left hrs]]
        calc ‖seminorm p‖
            ≤ ‖S.realOperator (p.1 - p.2)‖ * ‖f p.2‖ := by
              simpa [seminorm] using ContinuousLinearMap.le_opNorm _ _
          _ ≤ C * ‖f p.2‖ :=
              mul_le_mul_of_nonneg_right (hC _ htime0 htimeT) (norm_nonneg _)
      · rw [show kernel p = 0 by simp only [kernel, ite_eq_right hrs], norm_zero]
        exact mul_nonneg hC0 (norm_nonneg _)
    have hsub : Set.uIoc 0 t ×ˢ Set.uIoc 0 t ⊆ Set.Icc 0 t ×ˢ Set.Icc 0 t := by
      rw [Set.uIoc_of_le ht]
      exact Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self
    exact hFun.symm ▸ hsquare.mono_set hsub
  have hswap := intervalIntegral_intervalIntegral_swap (F := F) hprod
  have hright : (∫ r in (0 : ℝ)..t, ∫ s in (0 : ℝ)..t, F s r) =
      ∫ r in (0 : ℝ)..t, ∫ u in (0 : ℝ)..(t - r), S.realOperator u (f r) := by
    refine integral_congr fun r hr => ?_
    have hrI : r ∈ Set.Icc 0 t := by simpa [Set.uIcc_of_le ht] using hr
    simpa [F] using hvert_eq r hrI.1 hrI.2
  exact hleft.trans (hswap.trans hright)

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

/-- At each nonnegative time, continuous forcing satisfies the integrated generator equation. -/
private theorem integrated_at_of_continuous (S : StronglyContinuousSemigroup X) (x : X)
    {f : ℝ → X} (hf : Continuous f) {t : ℝ} (ht : 0 ≤ t) :
    ∃ h : (∫ s in (0 : ℝ)..t, forcedSemigroupTrajectory S x f s) ∈ S.generator.domain,
      forcedSemigroupTrajectory S x f t =
        x + S.generator ⟨∫ s in (0 : ℝ)..t, forcedSemigroupTrajectory S x f s, h⟩ +
          ∫ s in (0 : ℝ)..t, f s := by
  let u : ℝ → X := forcedSemigroupTrajectory S x f
  rcases ht.eq_or_lt with rfl | ht
  · have hzero : (∫ s in (0 : ℝ)..0, u s) = 0 := integral_same
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
      exact S.integral_orbit_mem_domain x ht
    have hmemO' : Iorb ∈ S.generator.domain := by
      rw [S.generator_domain]
      exact hmemO
    have hpackO : (⟨Iorb, hmemO'⟩ : S.generator.domain) =
        ⟨∫ s in Set.Ioc 0 t, S.realOperator s x, by
          rw [S.generator_domain]
          exact S.integral_orbit_mem_domain x ht⟩ := by
      apply Subtype.ext
      simpa [Iorb, orbit] using (integral_of_le ht.le)
    have hAO : S.generator ⟨Iorb, hmemO'⟩ = S.realOperator t x - x := by
      rw [hpackO]
      exact S.generator_integral_orbit x ht
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
private theorem integrated_of_continuous (S : StronglyContinuousSemigroup X) {T : ℝ}
    (_hT : 0 ≤ T) (x : X) {f : ℝ → X} (hf : Continuous f) :
    IsIntegratedSemigroupSolution S x f (forcedSemigroupTrajectory S x f) T := by
  refine ⟨(continuous_forcedSemigroupTrajectory S x hf).continuousOn, fun t ht => ?_⟩
  simpa using integrated_at_of_continuous S x hf ht.1

/-- An operator-norm bound controls the difference of two Duhamel integrals. -/
private theorem norm_duhamel_sub_le (S : StronglyContinuousSemigroup X) {T C : ℝ} (hT : 0 ≤ T)
    (hC0 : 0 ≤ C) (hC : ∀ s : ℝ, 0 ≤ s → s ≤ T → ‖S.realOperator s‖ ≤ C)
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
    integrableOn_duhamelIntegrand S hT hg ht0 htT
  have hSf : IntegrableOn (fun s => S.realOperator (t - s) (f s)) (Set.Icc 0 t) :=
    integrableOn_duhamelIntegrand S hT hf ht0 htT
  have hintG : IntervalIntegrable (fun s => S.realOperator (t - s) (g s)) volume 0 t :=
    ((Set.uIcc_of_le ht0).symm ▸ hSg).intervalIntegrable
  have hintF : IntervalIntegrable (fun s => S.realOperator (t - s) (f s)) volume 0 t :=
    ((Set.uIcc_of_le ht0).symm ▸ hSf).intervalIntegrable
  have hvec : IntegrableOn (fun s => S.realOperator (t - s) (g s - f s)) (Set.Icc 0 t) :=
    integrableOn_duhamelIntegrand S hT hfg ht0 htT
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
    · exact (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_right htT)).eventuallyLE
  calc ‖∫ s in (0 : ℝ)..t, S.realOperator (t - s) (g s - f s)‖
      ≤ ∫ s in (0 : ℝ)..t, ‖S.realOperator (t - s) (g s - f s)‖ :=
        norm_integral_le_integral_norm ht0
    _ ≤ C * ∫ s in (0 : ℝ)..t, ‖g s - f s‖ := hmono
    _ ≤ C * ∫ s in Set.Icc 0 T, ‖g s - f s‖ :=
        mul_le_mul_of_nonneg_left htail hC0

omit [CompleteSpace X] in
/-- The plain time integral is controlled by the L¹ norm on the ambient interval. -/
private theorem norm_intervalIntegral_sub_le {T : ℝ} (_hT : 0 ≤ T)
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
        · exact (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_right htT)).eventuallyLE

/-- Integrable forcing still produces an integrated solution, by L¹ approximation and closedness
of the generator. -/
private theorem integrated_of_integrable (S : StronglyContinuousSemigroup X) {T : ℝ} (hT : 0 ≤ T)
    (x : X) {f : ℝ → X} (hf : IntegrableOn f (Set.Icc 0 T)) :
    IsIntegratedSemigroupSolution S x f (forcedSemigroupTrajectory S x f) T := by
  by_cases hT0 : T = 0
  · subst hT0
    refine ⟨?_, ?_⟩
    · rw [show Set.Icc (0 : ℝ) 0 = {0} by ext t; simp]
      exact continuousOn_singleton _ 0
    · intro t ht
      have ht0 : t = 0 := le_antisymm ht.2 ht.1
      subst ht0
      have hzero : (∫ s in (0 : ℝ)..0, forcedSemigroupTrajectory S x f s) = 0 := integral_same
      have hmem : (∫ s in (0 : ℝ)..0, forcedSemigroupTrajectory S x f s) ∈ S.generator.domain := by
        rw [hzero]
        exact S.generator.domain.zero_mem
      have hpack : (⟨∫ s in (0 : ℝ)..0, forcedSemigroupTrajectory S x f s, hmem⟩ :
          S.generator.domain) = 0 := Subtype.ext hzero
      have hA : S.generator ⟨∫ s in (0 : ℝ)..0, forcedSemigroupTrajectory S x f s, hmem⟩ = 0 := by
        rw [hpack]
        exact S.generator.map_zero
      have hu0 : forcedSemigroupTrajectory S x f 0 = x := by
        simp [forcedSemigroupTrajectory, integral_same]
      have heq : forcedSemigroupTrajectory S x f 0 =
          x + S.generator ⟨∫ s in (0 : ℝ)..0, forcedSemigroupTrajectory S x f s, hmem⟩ +
            ∫ s in (0 : ℝ)..0, f s := by
        rw [hu0, hA, integral_same, add_zero, add_zero]
      exact ⟨hmem, heq⟩
  · have : Measure.WeaklyRegular (volume.restrict (Set.Icc 0 T)) :=
      Measure.WeaklyRegular.restrict_of_measure_ne_top measure_Icc_lt_top.ne
    obtain ⟨C, hC0, hC⟩ := norm_realOperator_le_on_Icc S hT
    have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n =>
      div_pos one_pos (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) one_pos)
    have hex : ∀ n : ℕ, ∃ g : ℝ →ᵇ X,
        (∫ s, ‖f s - g s‖ ∂volume.restrict (Set.Icc 0 T)) ≤ 1 / ((n : ℝ) + 1) ∧
          Integrable (g : ℝ → X) (volume.restrict (Set.Icc 0 T)) :=
      fun n => hf.exists_boundedContinuous_integral_sub_le (hpos n)
    let approx : ℕ → ℝ →ᵇ X := fun n => Classical.choose (hex n)
    have hspec : ∀ n, (∫ s, ‖f s - (approx n) s‖ ∂volume.restrict (Set.Icc 0 T)) ≤
        1 / ((n : ℝ) + 1) ∧ Integrable (approx n : ℝ → X) (volume.restrict (Set.Icc 0 T)) :=
      fun n => Classical.choose_spec (hex n)
    have hrev : ∀ n, (∫ s in Set.Icc 0 T, ‖(approx n : ℝ → X) s - f s‖) =
        ∫ s in Set.Icc 0 T, ‖f s - (approx n) s‖ := fun n =>
      setIntegral_congr_fun measurableSet_Icc fun s _ => norm_sub_rev ((approx n : ℝ → X) s) (f s)
    have hL1 : ∀ n, ∫ s in Set.Icc 0 T, ‖(approx n : ℝ → X) s - f s‖ ≤ 1 / ((n : ℝ) + 1) := by
      intro n
      rw [hrev n]
      simpa using (hspec n).1
    have hclose : ∀ n, ∀ t, 0 ≤ t → t ≤ T →
        ‖forcedSemigroupTrajectory S x (approx n) t - forcedSemigroupTrajectory S x f t‖ ≤
          C / ((n : ℝ) + 1) := by
      intro n t ht0 htT
      have hg : IntegrableOn (approx n : ℝ → X) (Set.Icc 0 T) := (hspec n).2
      have hdiff := norm_duhamel_sub_le S hT hC0 hC hf hg ht0 htT
      have hcancel : forcedSemigroupTrajectory S x (approx n) t -
          forcedSemigroupTrajectory S x f t =
          (∫ s in (0 : ℝ)..t, S.realOperator (t - s) ((approx n : ℝ → X) s)) -
            ∫ s in (0 : ℝ)..t, S.realOperator (t - s) (f s) := by
        set a : X := S.realOperator t x
        set b : X := ∫ s in (0 : ℝ)..t, S.realOperator (t - s) ((approx n : ℝ → X) s)
        set c : X := ∫ s in (0 : ℝ)..t, S.realOperator (t - s) (f s)
        change (a + b) - (a + c) = b - c
        abel
      rw [hcancel]
      calc ‖(∫ s in (0 : ℝ)..t, S.realOperator (t - s) ((approx n : ℝ → X) s)) -
            ∫ s in (0 : ℝ)..t, S.realOperator (t - s) (f s)‖
          ≤ C * ∫ s in Set.Icc 0 T, ‖(approx n : ℝ → X) s - f s‖ := hdiff
        _ ≤ C * (1 / ((n : ℝ) + 1)) := mul_le_mul_of_nonneg_left (hL1 n) hC0
        _ = C / ((n : ℝ) + 1) := by rw [mul_one_div]
    have hCto0 : Tendsto (fun n : ℕ => C / ((n : ℝ) + 1)) atTop (nhds 0) := by
      have hinv : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) :=
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).inv_tendsto_atTop
      have hmul : Tendsto (fun n : ℕ => C * (((n + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) := by
        simpa [mul_zero] using Filter.Tendsto.const_mul C hinv
      refine hmul.congr fun n => ?_
      rw [Nat.cast_add, Nat.cast_one, div_eq_mul_inv]
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
    · have hzero : (∫ s in (0 : ℝ)..0, u s) = 0 := integral_same
      have hmem : (∫ s in (0 : ℝ)..0, u s) ∈ S.generator.domain := by
        rw [hzero]
        exact S.generator.domain.zero_mem
      have hpack : (⟨∫ s in (0 : ℝ)..0, u s, hmem⟩ : S.generator.domain) = 0 :=
        Subtype.ext hzero
      have hA : S.generator ⟨∫ s in (0 : ℝ)..0, u s, hmem⟩ = 0 := by
        rw [hpack]
        exact S.generator.map_zero
      have hu0 : u 0 = x := by simp [u, forcedSemigroupTrajectory, integral_same]
      have heq : u 0 = x + S.generator ⟨∫ s in (0 : ℝ)..0, u s, hmem⟩ +
          ∫ s in (0 : ℝ)..0, f s := by
        rw [hu0, hA, integral_same, add_zero, add_zero]
      exact ⟨hmem, heq⟩
    · have htT : t ≤ T := ht.2
      have hto0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) := by
        have hinv : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) :=
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).inv_tendsto_atTop
        refine hinv.congr fun n => ?_
        rw [Nat.cast_add, Nat.cast_one, one_div]
      let un : ℕ → ℝ → X := fun n => forcedSemigroupTrajectory S x (approx n)
      have hintU : IntervalIntegrable u volume 0 t :=
        (hcont.mono (Set.Icc_subset_Icc_right htT)).intervalIntegrable_of_Icc ht0.le
      have hintUn : ∀ n, IntervalIntegrable (un n) volume 0 t := fun n =>
        (continuous_forcedSemigroupTrajectory S x (approx n).continuous).intervalIntegrable 0 t
      have hInt0 : Tendsto (fun n => ‖(∫ s in (0 : ℝ)..t, un n s) - ∫ s in (0 : ℝ)..t, u s‖)
          atTop (nhds 0) := by
        refine squeeze_zero (g := fun n : ℕ => (C / ((n : ℝ) + 1)) * t)
          (fun n : ℕ => norm_nonneg
            ((∫ s in (0 : ℝ)..t, un n s) - ∫ s in (0 : ℝ)..t, u s))
          (fun n => ?_) ?_
        · have hsub : (∫ s in (0 : ℝ)..t, un n s - u s) =
              (∫ s in (0 : ℝ)..t, un n s) - ∫ s in (0 : ℝ)..t, u s :=
            integral_sub (hintUn n) hintU
          rw [← hsub]
          have hle := norm_integral_le_of_norm_le_const
            (fun s hs => hclose n s (le_of_lt (Set.mem_Ioc.mp (Set.uIoc_of_le ht0.le ▸ hs)).1)
              (le_trans (Set.mem_Ioc.mp (Set.uIoc_of_le ht0.le ▸ hs)).2 htT))
          simpa [sub_zero, abs_of_nonneg ht0.le] using hle
        · simpa [mul_zero] using hCto0.mul_const t
      have hInt : Tendsto (fun n => ∫ s in (0 : ℝ)..t, un n s) atTop
          (nhds (∫ s in (0 : ℝ)..t, u s)) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        exact hInt0
      have hForce0 : Tendsto (fun n => ‖(∫ s in (0 : ℝ)..t, (approx n : ℝ → X) s) -
          ∫ s in (0 : ℝ)..t, f s‖) atTop (nhds 0) := by
        refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hto0
        exact le_trans (norm_intervalIntegral_sub_le hT hf (hspec n).2 ht0.le htT) (hL1 n)
      have hForce : Tendsto (fun n => ∫ s in (0 : ℝ)..t, (approx n : ℝ → X) s) atTop
          (nhds (∫ s in (0 : ℝ)..t, f s)) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        exact hForce0
      have hVal : Tendsto (fun n => un n t) atTop (nhds (u t)) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        refine squeeze_zero (fun _ => norm_nonneg _) (fun n => hclose n t ht0.le htT) hCto0
      have hRight : Tendsto (fun n => un n t - x - ∫ s in (0 : ℝ)..t, (approx n : ℝ → X) s)
          atTop (nhds (u t - x - ∫ s in (0 : ℝ)..t, f s)) :=
        (hVal.sub tendsto_const_nhds).sub hForce
      let pair : ℕ → X × X := fun n =>
        (∫ s in (0 : ℝ)..t, un n s, un n t - x - ∫ s in (0 : ℝ)..t, (approx n : ℝ → X) s)
      have hpair : Tendsto pair atTop
          (nhds (∫ s in (0 : ℝ)..t, u s, u t - x - ∫ s in (0 : ℝ)..t, f s)) := by
        rw [nhds_prod_eq]
        exact hInt.prodMk hRight
      have hgraph : ∀ n, pair n ∈ S.generator.graph := by
        intro n
        obtain ⟨hmem, heq⟩ := integrated_at_of_continuous S x (approx n).continuous ht0.le
        rw [LinearPMap.mem_graph_iff]
        refine ⟨⟨∫ s in (0 : ℝ)..t, un n s, hmem⟩, rfl, ?_⟩
        have hA : un n t - x - ∫ s in (0 : ℝ)..t, (approx n : ℝ → X) s =
            S.generator ⟨∫ s in (0 : ℝ)..t, un n s, hmem⟩ := by
          unfold un
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
  rw [S.realOperator_generator_map (sub_pos.mpr hst).le y] at hfull
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
  have hlim := S.tendsto_realOperator_apply htime
    ((htime.eventually_const_lt (sub_pos.mpr hst)).mono fun _ h => h.le)
    (sub_pos.mpr hst).le hprim
  have hsum := hlim.add hback
  rw [add_neg_cancel] at hsum
  refine hsum.congr fun r => ?_
  simp only [slope_def_module, map_smul, map_sub, smul_sub]
  abel

/-- Integrated solutions with the same initial value and forcing agree on `[0, T]`. -/
private theorem eqOn_integrated (S : StronglyContinuousSemigroup X) {T : ℝ} {x : X}
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
        (g := g) (continuous_sub_left t).continuousOn (fun s hs => sub_nonneg.mpr hs.2) hgcont
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

/-- **24.13**: the variation-of-constants formula is the unique continuous integrated solution. -/
theorem variation_of_constants (S : StronglyContinuousSemigroup X) {T : ℝ} (hT : 0 ≤ T)
    (x : X) {f : ℝ → X} (hf : IntegrableOn f (Set.Icc 0 T)) :
    IsIntegratedSemigroupSolution S x f (forcedSemigroupTrajectory S x f) T ∧
      ∀ u : ℝ → X, IsIntegratedSemigroupSolution S x f u T →
        Set.EqOn u (forcedSemigroupTrajectory S x f) (Set.Icc 0 T) := by
  refine ⟨integrated_of_integrable S hT x hf, fun u hu => ?_⟩
  exact eqOn_integrated S hu (integrated_of_integrable S hT x hf)

/-- With domain initial data and C1 forcing, the trajectory is a classical solution in the
interior time interval, and all nonnegative-time values belong to the generator domain. -/
theorem variation_of_constants_classical (S : StronglyContinuousSemigroup X) {T : ℝ}
    (hT : 0 < T) (x : S.generator.domain) {f : ℝ → X}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 T)) :
    (∀ t ∈ Set.Icc 0 T, forcedSemigroupTrajectory S x f t ∈ S.generator.domain) ∧
      ∀ t ∈ Set.Ioo 0 T, ∃ h : forcedSemigroupTrajectory S x f t ∈ S.generator.domain,
        HasDerivAt (forcedSemigroupTrajectory S x f)
          (S.generator ⟨forcedSemigroupTrajectory S x f t, h⟩ + f t) t := by
  sorry

/-- Uniform strong convergence on every bounded nonnegative time interval. -/
def SemigroupsConvergeUniformlyOnCompacts
    (S : ℕ → StronglyContinuousSemigroup X) (T : StronglyContinuousSemigroup X) : Prop :=
  ∀ x : X, ∀ R : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
    ∀ t : ℝ≥0, t ≤ R → ‖S n t x - T t x‖ < ε

/-- **24.17**, Trotter–Kato: one sufficiently large real resolvent parameter characterizes
uniform-on-bounded-time strong semigroup convergence under a common exponential bound. -/
theorem trotter_kato (S : ℕ → StronglyContinuousSemigroup X)
    (T : StronglyContinuousSemigroup X) {ω M : ℝ}
    (hS : ∀ n, (S n).HasGrowthBound ω M) (hT : T.HasGrowthBound ω M)
    {r : ℝ} (hr : ω < r) :
    (∀ x : X, Tendsto (fun n ↦ (S n).generator.resolvent r x) atTop
      (𝓝 (T.generator.resolvent r x))) ↔ SemigroupsConvergeUniformlyOnCompacts S T := by
  sorry

/-- **24.18**, Chernoff: a stable strongly continuous product family tangent to a generator
on an actual core converges uniformly over bounded nonnegative time intervals. -/
theorem chernoff_product (S : StronglyContinuousSemigroup X)
    (F : ℝ≥0 → X →L[ℝ] X) (hF0 : F 0 = 1)
    (hF : ∀ x, Continuous (fun t ↦ F t x)) {M ω : ℝ}
    (hbound : ∀ t : ℝ≥0, ∀ n : ℕ, ‖F t ^ n‖ ≤ M * Real.exp (ω * n * t))
    (D : Submodule ℝ X) (hD : S.generator.HasCore D)
    (htangent : ∀ x : D, Tendsto (fun t : ℝ ↦ t⁻¹ • (F (Real.toNNReal t) x - x))
      (𝓝[>] 0) (𝓝 (S.generator ⟨x, hD.le_domain x.property⟩))) :
    ∀ x : X, ∀ R : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in atTop,
      ∀ t : ℝ≥0, t ≤ R → ‖(F (t / (n + 1 : ℝ≥0)) ^ (n + 1)) x - S t x‖ < ε := by
  sorry

end CKMA
