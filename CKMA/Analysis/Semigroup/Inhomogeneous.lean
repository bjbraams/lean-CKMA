/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.Semigroups.CauchyProblem.Inhomogeneous

/-!
# Duhamel formula and integrated semigroup solutions on a bounded interval

Variation-of-constants trajectories `t ↦ S(t) x + ∫₀ᵗ S(t - s) f(s) ds` of a strongly continuous
semigroup on a real Banach space, and integrated solutions of `u' = A u + f` on `[0, T]`, where
`A` is the generator. For forcing integrable on `[0, T]` the trajectory is the unique integrated
solution (**24.13**). Source: GAPS 24.13.

The proofs reduce to TauCeti's inhomogeneous Cauchy problem on `[0, ∞)`
(`TauCeti.Analysis.Semigroups.CauchyProblem.Inhomogeneous`): the trajectory agrees on `[0, T]`
with the mild solution `S.realOperator t x + S.duhamel F t` for the forcing `F` extended by zero
outside `[0, T]`, and uniqueness is TauCeti's
`eqOn_realOperator_sub_add_setIntegral_of_generator_setIntegral_eq` applied to the difference of
two solutions.

## Main definitions

* `CKMA.forcedSemigroupTrajectory`: the variation-of-constants trajectory.
* `CKMA.IsIntegratedSemigroupSolution`: integrated solution of `u' = A u + f` on `[0, T]`.

## Main results

* `CKMA.forcedSemigroupTrajectory_eq_add_duhamel`: for `t ≥ 0` the trajectory is
  `S.realOperator t x + S.duhamel f t`.
* `CKMA.isIntegratedSemigroupSolution_forcedSemigroupTrajectory`: for forcing integrable on
  `[0, T]`, the trajectory is an integrated solution.
* `CKMA.IsIntegratedSemigroupSolution.eqOn`: integrated solutions with the same initial datum
  and forcing agree on `[0, T]`.
* `CKMA.variation_of_constants`: the two statements together (**24.13**).
* `CKMA.linearPMap_mk_add`, `CKMA.linearPMap_mk_sub`, `CKMA.linearPMap_mk_congr`: a partial
  linear map at a sum or difference of domain vectors, with explicit domain proofs.

## References

* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*.
* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology TauCeti.Semigroups intervalIntegral

section LinearPMap

variable {R E F : Type*} [Ring R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

/-- A partial linear map takes equal values at equal domain vectors, whatever the domain proofs. -/
theorem linearPMap_mk_congr (f : E →ₗ.[R] F) {x y : E} (h : x = y) (hx : x ∈ f.domain)
    (hy : y ∈ f.domain) : f ⟨x, hx⟩ = f ⟨y, hy⟩ := by
  subst h
  rfl

/-- A partial linear map at a sum of domain vectors, with explicit domain proofs. -/
theorem linearPMap_mk_add (f : E →ₗ.[R] F) {x y : E} (hx : x ∈ f.domain) (hy : y ∈ f.domain)
    (hxy : x + y ∈ f.domain) : f ⟨x + y, hxy⟩ = f ⟨x, hx⟩ + f ⟨y, hy⟩ :=
  f.map_add ⟨x, hx⟩ ⟨y, hy⟩

/-- A partial linear map at a difference of domain vectors, with explicit domain proofs. -/
theorem linearPMap_mk_sub (f : E →ₗ.[R] F) {x y : E} (hx : x ∈ f.domain) (hy : y ∈ f.domain)
    (hxy : x - y ∈ f.domain) : f ⟨x - y, hxy⟩ = f ⟨x, hx⟩ - f ⟨y, hy⟩ :=
  f.map_sub ⟨x, hx⟩ ⟨y, hy⟩

end LinearPMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The variation-of-constants trajectory `t ↦ S(t) x + ∫₀ᵗ S(t - s) f(s) ds`, with an oriented
interval integral. For `t ≥ 0` it is `S.realOperator t x + S.duhamel f t`
(`forcedSemigroupTrajectory_eq_add_duhamel`). -/
@[expose]
def forcedSemigroupTrajectory (S : StronglyContinuousSemigroup X) (x : X)
    (f : ℝ → X) (t : ℝ) : X := S.realOperator t x + ∫ s in (0 : ℝ)..t, S.realOperator (t - s) (f s)

/-- Unfolding the variation-of-constants trajectory. -/
theorem forcedSemigroupTrajectory_def (S : StronglyContinuousSemigroup X) (x : X) (f : ℝ → X)
    (t : ℝ) : forcedSemigroupTrajectory S x f t =
      S.realOperator t x + ∫ s in (0 : ℝ)..t, S.realOperator (t - s) (f s) :=
  rfl

/-- At a nonnegative time the trajectory is the orbit plus TauCeti's Duhamel integral. -/
theorem forcedSemigroupTrajectory_eq_add_duhamel (S : StronglyContinuousSemigroup X) (x : X)
    (f : ℝ → X) {t : ℝ} (ht : 0 ≤ t) :
    forcedSemigroupTrajectory S x f t = S.realOperator t x + S.duhamel f t := by
  rw [forcedSemigroupTrajectory, S.duhamel_def, integral_of_le ht]

/-- An integrated solution of `u' = A u + f` on `[0, T]`, where `A` is the generator of `S`: `u`
is continuous on `[0, T]` and, for `t ∈ [0, T]`, `∫₀ᵗ u` lies in the domain of `A` with
`u t = x + A (∫₀ᵗ u) + ∫₀ᵗ f`. -/
@[expose]
def IsIntegratedSemigroupSolution (S : StronglyContinuousSemigroup X) (x : X)
    (f u : ℝ → X) (T : ℝ) : Prop :=
  ContinuousOn u (Set.Icc 0 T) ∧ ∀ t ∈ Set.Icc 0 T,
    ∃ h : (∫ s in (0 : ℝ)..t, u s) ∈ S.generator.domain,
      u t = x + S.generator ⟨∫ s in (0 : ℝ)..t, u s, h⟩ + ∫ s in (0 : ℝ)..t, f s

/-- Unfolding the integrated-solution predicate. -/
theorem isIntegratedSemigroupSolution_iff {S : StronglyContinuousSemigroup X} {x : X}
    {f u : ℝ → X} {T : ℝ} :
    IsIntegratedSemigroupSolution S x f u T ↔ ContinuousOn u (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, ∃ h : (∫ s in (0 : ℝ)..t, u s) ∈ S.generator.domain,
        u t = x + S.generator ⟨∫ s in (0 : ℝ)..t, u s, h⟩ + ∫ s in (0 : ℝ)..t, f s :=
  Iff.rfl

namespace IsIntegratedSemigroupSolution

variable {S : StronglyContinuousSemigroup X} {x : X} {f u v : ℝ → X} {T t : ℝ}

/-- An integrated solution is continuous on `[0, T]`. -/
theorem continuousOn (hu : IsIntegratedSemigroupSolution S x f u T) :
    ContinuousOn u (Set.Icc 0 T) :=
  hu.1

/-- The time integral of an integrated solution lies in the generator domain. -/
theorem integral_mem_domain (hu : IsIntegratedSemigroupSolution S x f u T)
    (ht : t ∈ Set.Icc 0 T) : (∫ s in (0 : ℝ)..t, u s) ∈ S.generator.domain :=
  (hu.2 t ht).fst

/-- The integrated equation `u t = x + A (∫₀ᵗ u) + ∫₀ᵗ f`. -/
theorem eq_add (hu : IsIntegratedSemigroupSolution S x f u T) (ht : t ∈ Set.Icc 0 T) :
    u t = x + S.generator ⟨∫ s in (0 : ℝ)..t, u s, hu.integral_mem_domain ht⟩ +
      ∫ s in (0 : ℝ)..t, f s :=
  (hu.2 t ht).snd

/-- The difference `d = u - v` of two integrated solutions with the same data satisfies
`d t = A (∫₀ᵗ d)` on `[0, T]`. -/
private theorem sub_eq_generator (hu : IsIntegratedSemigroupSolution S x f u T)
    (hv : IsIntegratedSemigroupSolution S x f v T) (ht : t ∈ Set.Icc 0 T) :
    ∃ h : (∫ s in (0 : ℝ)..t, (u - v) s) ∈ S.generator.domain,
      (u - v) t = S.generator ⟨∫ s in (0 : ℝ)..t, (u - v) s, h⟩ := by
  have hint {w : ℝ → X} (hw : ContinuousOn w (Set.Icc 0 T)) : IntervalIntegrable w volume 0 t :=
    (hw.mono (Set.Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
  have hsub : (∫ s in (0 : ℝ)..t, (u - v) s) =
      (∫ s in (0 : ℝ)..t, u s) - ∫ s in (0 : ℝ)..t, v s := by
    simpa only [Pi.sub_apply] using integral_sub (hint hu.continuousOn) (hint hv.continuousOn)
  have hmem := sub_mem (hu.integral_mem_domain ht) (hv.integral_mem_domain ht)
  refine ⟨hsub ▸ hmem, ?_⟩
  rw [linearPMap_mk_congr _ hsub _ hmem, linearPMap_mk_sub _ (hu.integral_mem_domain ht)
    (hv.integral_mem_domain ht), Pi.sub_apply, hu.eq_add ht, hv.eq_add ht]
  abel

/-- Integrated solutions with the same initial value and forcing agree on `[0, T]`. No
integrability of the forcing is needed: the difference of two solutions solves the unforced
equation. -/
theorem eqOn [CompleteSpace X] (hu : IsIntegratedSemigroupSolution S x f u T)
    (hv : IsIntegratedSemigroupSolution S x f v T) : Set.EqOn u v (Set.Icc 0 T) := by
  intro t ht
  have hd0 : (u - v) 0 = 0 := by
    obtain ⟨h, heq⟩ := hu.sub_eq_generator hv ⟨le_rfl, ht.1.trans ht.2⟩
    rw [heq, linearPMap_mk_congr _ integral_same h (zero_mem _)]
    exact S.generator.map_zero
  have hmild : ∀ s ∈ Set.Icc 0 T,
      ∃ h : (∫ r in Set.Ioc 0 s, (u - v) r) ∈ S.generator.domain,
        S.generator ⟨_, h⟩ = (u - v) s - (u - v) 0 - ∫ r in Set.Ioc 0 s, (0 : ℝ → X) r := by
    intro s hs
    obtain ⟨h, heq⟩ := hu.sub_eq_generator hv hs
    have hI : (∫ r in (0 : ℝ)..s, (u - v) r) = ∫ r in Set.Ioc 0 s, (u - v) r :=
      integral_of_le hs.1
    refine ⟨hI ▸ h, ?_⟩
    rw [linearPMap_mk_congr _ hI.symm _ h, ← heq, hd0]
    simp
  have h := S.eqOn_realOperator_sub_add_setIntegral_of_generator_setIntegral_eq
    integrableOn_zero (hu.continuousOn.sub hv.continuousOn) hmild ht
  rw [hd0] at h
  simpa [sub_eq_zero] using h

end IsIntegratedSemigroupSolution

/-- For forcing integrable on `[0, T]`, the variation-of-constants trajectory is an integrated
solution on `[0, T]`. On `[0, T]` it agrees with TauCeti's mild solution for the forcing extended
by zero outside `[0, T]`. -/
theorem isIntegratedSemigroupSolution_forcedSemigroupTrajectory [CompleteSpace X]
    (S : StronglyContinuousSemigroup X) {T : ℝ} (x : X) {f : ℝ → X}
    (hf : IntegrableOn f (Set.Icc 0 T)) :
    IsIntegratedSemigroupSolution S x f (forcedSemigroupTrajectory S x f) T := by
  set F : ℝ → X := (Set.Icc 0 T).indicator f
  have hF : LocallyIntegrableOn F (Set.Ici 0) :=
    ((integrable_indicator_iff measurableSet_Icc).2 hf).locallyIntegrable.locallyIntegrableOn _
  have hFf {t : ℝ} (ht : t ≤ T) : Set.EqOn F f (Set.Ioc 0 t) := fun s hs =>
    Set.indicator_of_mem (show s ∈ Set.Icc 0 T from ⟨hs.1.le, hs.2.trans ht⟩) f
  have hm := S.isForcedMildSolution_realOperator_add_duhamel hF x
  have hEq : Set.EqOn (fun t => S.realOperator t x + S.duhamel F t)
      (forcedSemigroupTrajectory S x f) (Set.Icc 0 T) := fun t ht => by
    dsimp only
    rw [forcedSemigroupTrajectory_eq_add_duhamel S x f ht.1, S.duhamel_def, S.duhamel_def,
      setIntegral_congr_fun measurableSet_Ioc fun s hs => by rw [hFf ht.2 hs]]
  refine ⟨(hm.continuousOn.mono Set.Icc_subset_Ici_self).congr hEq.symm, fun t ht => ?_⟩
  have hI : (∫ s in (0 : ℝ)..t, forcedSemigroupTrajectory S x f s) =
      ∫ s in Set.Ioc 0 t, (S.realOperator s x + S.duhamel F s) := by
    rw [integral_of_le ht.1]
    exact setIntegral_congr_fun measurableSet_Ioc fun s hs =>
      (hEq ⟨hs.1.le, hs.2.trans ht.2⟩).symm
  have hIf : (∫ s in (0 : ℝ)..t, f s) = ∫ s in Set.Ioc 0 t, F s := by
    rw [integral_of_le ht.1]
    exact setIntegral_congr_fun measurableSet_Ioc fun s hs => (hFf ht.2 hs).symm
  refine ⟨hI ▸ hm.integral_mem_domain ht.1, ?_⟩
  have hv : S.realOperator t x + S.duhamel F t = forcedSemigroupTrajectory S x f t := hEq ht
  rw [linearPMap_mk_congr _ hI _ (hm.integral_mem_domain ht.1), hm.map_integral_eq_sub ht.1,
    hv, hIf]
  abel

/-- **24.13**, **variation of constants**: for forcing integrable on `[0, T]`, the
variation-of-constants trajectory is the unique integrated solution on `[0, T]`. -/
theorem variation_of_constants [CompleteSpace X] (S : StronglyContinuousSemigroup X) {T : ℝ}
    (x : X) {f : ℝ → X} (hf : IntegrableOn f (Set.Icc 0 T)) :
    IsIntegratedSemigroupSolution S x f (forcedSemigroupTrajectory S x f) T ∧
      ∀ u : ℝ → X, IsIntegratedSemigroupSolution S x f u T →
        Set.EqOn u (forcedSemigroupTrajectory S x f) (Set.Icc 0 T) :=
  have h := isIntegratedSemigroupSolution_forcedSemigroupTrajectory S x hf
  ⟨h, fun _ hu => hu.eqOn h⟩

end CKMA
