/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Topology.DenseEmbedding

/-!
# Uniqueness of a minimal unitary power dilation

Two-sided orbit vectors of a unitary power dilation have inner products determined by the
original contraction. The resulting linear isometry of the dense orbit extends to the unique
unitary intertwiner. The argument is the uniqueness half of Sz.-Nagy's dilation theorem, as in
Sz.-Nagy–Foiaş–Bercovici–Kérchy, Chapter I.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped InnerProductSpace
open ContinuousLinearMap Submodule

universe u

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- A natural-number power of a unitary agrees with iteration of the underlying map. -/
theorem linearIsometryEquiv_pow_apply (U : K ≃ₗᵢ[ℂ] K) (n : ℕ) (x : K) :
    (U ^ n) x = (U^[n]) x := by
  induction n with
  | zero =>
    rw [pow_zero, LinearIsometryEquiv.coe_one]
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ', LinearIsometryEquiv.coe_mul,
      Function.comp_apply, ih]

/-- An integer power with a natural value agrees with iteration. -/
theorem linearIsometryEquiv_zpow_natCast (U : K ≃ₗᵢ[ℂ] K) (n : ℕ) (x : K) :
    (U ^ (n : ℤ)) x = (U^[n]) x := by
  rw [zpow_natCast, linearIsometryEquiv_pow_apply]

/-- A negative successor power is iteration of the inverse unitary. -/
theorem linearIsometryEquiv_zpow_negSucc (U : K ≃ₗᵢ[ℂ] K) (n : ℕ) (x : K) :
    (U ^ Int.negSucc n) x = (U.symm^[n + 1]) x := by
  rw [zpow_negSucc, ← inv_pow, LinearIsometryEquiv.inv_def, linearIsometryEquiv_pow_apply]

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The two-sided orbit vector indexed by a time and a vector of `H`. -/
def unitaryOrbitVec (U : K ≃ₗᵢ[ℂ] K) (J : H →ₗᵢ[ℂ] K) (p : ℤ × H) : K :=
  (U ^ p.1) (J p.2)

/-- Finite linear combinations of two-sided orbit vectors. -/
def unitaryOrbit (U : K ≃ₗᵢ[ℂ] K) (J : H →ₗᵢ[ℂ] K) :
    ((ℤ × H) →₀ ℂ) →ₗ[ℂ] K :=
  Finsupp.linearCombination ℂ (unitaryOrbitVec U J)

/-- A single coefficient reproduces the corresponding orbit vector. -/
theorem unitaryOrbit_single (U : K ≃ₗᵢ[ℂ] K) (J : H →ₗᵢ[ℂ] K) (p : ℤ × H) (a : ℂ) :
    unitaryOrbit U J (Finsupp.single p a) = a • unitaryOrbitVec U J p := by
  rw [unitaryOrbit, Finsupp.linearCombination_single]

/-- Shift every time index of a finitely supported coefficient by one. -/
def unitaryOrbitShift (c : (ℤ × H) →₀ ℂ) : (ℤ × H) →₀ ℂ :=
  c.mapDomain (fun p => (p.1 + 1, p.2))

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- The time shift is additive. -/
theorem unitaryOrbitShift_add (f g : (ℤ × H) →₀ ℂ) :
    unitaryOrbitShift (f + g) = unitaryOrbitShift f + unitaryOrbitShift g := by
  rw [unitaryOrbitShift, unitaryOrbitShift, unitaryOrbitShift, Finsupp.mapDomain_add]

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
/-- The time shift sends a single coefficient to the shifted index. -/
theorem unitaryOrbitShift_single (p : ℤ × H) (a : ℂ) :
    unitaryOrbitShift (Finsupp.single p a) = Finsupp.single (p.1 + 1, p.2) a := by
  rw [unitaryOrbitShift, Finsupp.mapDomain_single]

/-- Applying the unitary moves an orbit combination onto the shifted coefficient. -/
theorem unitary_apply_unitaryOrbit (U : K ≃ₗᵢ[ℂ] K) (J : H →ₗᵢ[ℂ] K)
    (c : (ℤ × H) →₀ ℂ) :
    U (unitaryOrbit U J c) = unitaryOrbit U J (unitaryOrbitShift c) := by
  induction c using Finsupp.induction_linear with
  | zero =>
    rw [map_zero (unitaryOrbit U J), map_zero U, unitaryOrbitShift, Finsupp.mapDomain_zero]
    exact (map_zero (unitaryOrbit U J)).symm
  | add f g ihf ihg =>
    calc
      U (unitaryOrbit U J (f + g))
          = U (unitaryOrbit U J f + unitaryOrbit U J g) := by
            rw [map_add (unitaryOrbit U J)]
      _ = U (unitaryOrbit U J f) + U (unitaryOrbit U J g) := map_add U _ _
      _ = unitaryOrbit U J (unitaryOrbitShift f) +
            unitaryOrbit U J (unitaryOrbitShift g) := by
            rw [ihf, ihg]
      _ = unitaryOrbit U J (unitaryOrbitShift f + unitaryOrbitShift g) := by
            rw [← map_add (unitaryOrbit U J)]
      _ = unitaryOrbit U J (unitaryOrbitShift (f + g)) := by
            rw [unitaryOrbitShift_add]
  | single p a =>
    rw [unitaryOrbit_single, map_smul, unitaryOrbitShift_single, unitaryOrbit_single]
    congr 1
    rw [unitaryOrbitVec, unitaryOrbitVec]
    have hmul : (U * U ^ p.1) (J p.2) = U ((U ^ p.1) (J p.2)) := by
      rw [LinearIsometryEquiv.coe_mul, Function.comp_apply]
    rw [← hmul, ← zpow_one_add]
    exact congrArg (fun k : ℤ => (U ^ k) (J p.2)) (add_comm 1 p.1)

/-- The inner product of two finite combinations expands over the two supports. -/
theorem inner_linearCombination_eq_sum {ι : Type*} (v : ι → K) (f g : ι →₀ ℂ) :
    ⟪Finsupp.linearCombination ℂ v f, Finsupp.linearCombination ℂ v g⟫_ℂ =
      ∑ i ∈ f.support, ∑ j ∈ g.support,
        (star (f i) * g j) * ⟪v i, v j⟫_ℂ := by
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  have hsumf : f.sum (fun i a => a • v i) = ∑ i ∈ f.support, f i • v i := rfl
  have hsumg : g.sum (fun j b => b • v j) = ∑ j ∈ g.support, g j • v j := rfl
  rw [hsumf, hsumg, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, starRingEnd_apply, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_right, mul_assoc]

variable [CompleteSpace H] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Moving both legs of an orbit inner product by the same negative power reduces the times. -/
theorem inner_unitary_zpow_sub (U : K ≃ₗᵢ[ℂ] K) (J : H →ₗᵢ[ℂ] K) (m n : ℤ) (x y : H) :
    ⟪(U ^ m) (J x), (U ^ n) (J y)⟫_ℂ = ⟪(U ^ (m - n)) (J x), J y⟫_ℂ := by
  have hleft : (U ^ (-n)) ((U ^ m) (J x)) = (U ^ (m - n)) (J x) := by
    have hmul : (U ^ (-n) * U ^ m) (J x) = (U ^ (-n)) ((U ^ m) (J x)) := by
      rw [LinearIsometryEquiv.coe_mul, Function.comp_apply]
    rw [← hmul, ← zpow_add]
    apply congrArg (fun k : ℤ => (U ^ k) (J x))
    rw [add_comm, ← sub_eq_add_neg]
  have hright : (U ^ (-n)) ((U ^ n) (J y)) = J y := by
    have hmul : (U ^ (-n) * U ^ n) (J y) = (U ^ (-n)) ((U ^ n) (J y)) := by
      rw [LinearIsometryEquiv.coe_mul, Function.comp_apply]
    rw [← hmul, ← zpow_add, neg_add_cancel, zpow_zero, LinearIsometryEquiv.coe_one]
    rfl
  calc
    ⟪(U ^ m) (J x), (U ^ n) (J y)⟫_ℂ
        = ⟪(U ^ (-n)) ((U ^ m) (J x)), (U ^ (-n)) ((U ^ n) (J y))⟫_ℂ := by
          rw [← LinearIsometryEquiv.inner_map_map (U ^ (-n))]
    _ = ⟪(U ^ (m - n)) (J x), J y⟫_ℂ := by
          rw [hleft, hright]

/-- Nonnegative and negative orbit inner products are the powers of the original contraction. -/
theorem inner_unitary_orbit_power (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (U : K ≃ₗᵢ[ℂ] K)
    (hpow : ∀ n : ℕ, ∀ x : H,
      J.toContinuousLinearMap.adjoint ((U^[n]) (J x)) = (T ^ n) x)
    (m n : ℤ) (x y : H) :
    ⟪(U ^ m) (J x), (U ^ n) (J y)⟫_ℂ =
      if 0 ≤ m - n then ⟪(T ^ (m - n).toNat) x, y⟫_ℂ
      else ⟪x, (T ^ (n - m).toNat) y⟫_ℂ := by
  rw [inner_unitary_zpow_sub]
  by_cases hmn : 0 ≤ m - n
  · rw [ite_eq_left hmn]
    have hk : (U ^ (m - n)) (J x) = (U^[((m - n).toNat)]) (J x) := by
      conv_lhs => rw [(Int.toNat_of_nonneg hmn).symm]
      rw [zpow_natCast, linearIsometryEquiv_pow_apply]
    have hJy : J.toContinuousLinearMap y = J y := by
      rw [LinearIsometry.coe_toContinuousLinearMap]
    rw [hk, ← hJy]
    rw [← adjoint_inner_left J.toContinuousLinearMap y ((U^[((m - n).toNat)]) (J x))]
    exact congrArg (fun z => ⟪z, y⟫_ℂ) (hpow (m - n).toNat x)
  · rw [ite_eq_right hmn]
    have hlt : m - n < 0 := lt_of_not_ge hmn
    have hnm : 0 < n - m := by
      rw [← neg_sub]
      exact neg_pos.mpr hlt
    have hneg : m - n = -↑((n - m).toNat) := by
      rw [Int.toNat_of_nonneg hnm.le]
      exact (neg_sub n m).symm
    rw [hneg, zpow_neg, LinearIsometryEquiv.coe_inv]
    rw [LinearIsometryEquiv.inner_map_eq_flip (U ^ ((n - m).toNat : ℤ)).symm]
    rw [LinearIsometryEquiv.symm_symm]
    have hiter : (U ^ ((n - m).toNat : ℤ)) (J y) =
        (U^[((n - m).toNat)]) (J y) := by
      rw [zpow_natCast, linearIsometryEquiv_pow_apply]
    have hJx : J.toContinuousLinearMap x = J x := by
      rw [LinearIsometry.coe_toContinuousLinearMap]
    rw [hiter, ← hJx]
    rw [← adjoint_inner_right J.toContinuousLinearMap x ((U^[((n - m).toNat)]) (J y))]
    exact congrArg (fun z => ⟪x, z⟫_ℂ) (hpow (n - m).toNat y)

variable {L : Type u} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

/-- Orbit inner products of two unitary power dilations of one contraction agree. -/
theorem inner_unitaryOrbitVec_eq (T : H →L[ℂ] H)
    (J : H →ₗᵢ[ℂ] K) (U : K ≃ₗᵢ[ℂ] K)
    (hpow : ∀ n : ℕ, ∀ x : H,
      J.toContinuousLinearMap.adjoint ((U^[n]) (J x)) = (T ^ n) x)
    (J' : H →ₗᵢ[ℂ] L) (U' : L ≃ₗᵢ[ℂ] L)
    (hpow' : ∀ n : ℕ, ∀ x : H,
      J'.toContinuousLinearMap.adjoint ((U'^[n]) (J' x)) = (T ^ n) x)
    (p q : ℤ × H) :
    ⟪unitaryOrbitVec U J p, unitaryOrbitVec U J q⟫_ℂ =
      ⟪unitaryOrbitVec U' J' p, unitaryOrbitVec U' J' q⟫_ℂ := by
  rw [unitaryOrbitVec, unitaryOrbitVec, unitaryOrbitVec, unitaryOrbitVec,
    inner_unitary_orbit_power T J U hpow p.1 q.1 p.2 q.2,
    inner_unitary_orbit_power T J' U' hpow' p.1 q.1 p.2 q.2]

/-- Finite orbit combinations of two unitary power dilations have the same inner products. -/
theorem inner_unitaryOrbit_eq (T : H →L[ℂ] H)
    (J : H →ₗᵢ[ℂ] K) (U : K ≃ₗᵢ[ℂ] K)
    (hpow : ∀ n : ℕ, ∀ x : H,
      J.toContinuousLinearMap.adjoint ((U^[n]) (J x)) = (T ^ n) x)
    (J' : H →ₗᵢ[ℂ] L) (U' : L ≃ₗᵢ[ℂ] L)
    (hpow' : ∀ n : ℕ, ∀ x : H,
      J'.toContinuousLinearMap.adjoint ((U'^[n]) (J' x)) = (T ^ n) x)
    (f g : (ℤ × H) →₀ ℂ) :
    ⟪unitaryOrbit U J f, unitaryOrbit U J g⟫_ℂ =
      ⟪unitaryOrbit U' J' f, unitaryOrbit U' J' g⟫_ℂ := by
  rw [unitaryOrbit, unitaryOrbit, inner_linearCombination_eq_sum, inner_linearCombination_eq_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [inner_unitaryOrbitVec_eq T J U hpow J' U' hpow' i j]

/-- Corresponding finite orbit combinations have equal norms. -/
theorem norm_unitaryOrbit_eq (T : H →L[ℂ] H)
    (J : H →ₗᵢ[ℂ] K) (U : K ≃ₗᵢ[ℂ] K)
    (hpow : ∀ n : ℕ, ∀ x : H,
      J.toContinuousLinearMap.adjoint ((U^[n]) (J x)) = (T ^ n) x)
    (J' : H →ₗᵢ[ℂ] L) (U' : L ≃ₗᵢ[ℂ] L)
    (hpow' : ∀ n : ℕ, ∀ x : H,
      J'.toContinuousLinearMap.adjoint ((U'^[n]) (J' x)) = (T ^ n) x)
    (c : (ℤ × H) →₀ ℂ) :
    ‖unitaryOrbit U' J' c‖ = ‖unitaryOrbit U J c‖ := by
  have hinner := inner_unitaryOrbit_eq T J U hpow J' U' hpow' c c
  have hsq : ‖unitaryOrbit U' J' c‖ ^ 2 = ‖unitaryOrbit U J c‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), hinner]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

omit [CompleteSpace H] [CompleteSpace K] in
/-- Minimality makes the linear combinations of two-sided orbit vectors dense. -/
theorem denseRange_unitaryOrbit (U : K ≃ₗᵢ[ℂ] K) (J : H →ₗᵢ[ℂ] K)
    (hmin : (span ℂ {y : K | ∃ k : ℤ, ∃ x : H, y = (U ^ k) (J x)}).topologicalClosure = ⊤) :
    DenseRange (unitaryOrbit U J) := by
  unfold DenseRange
  rw [dense_iff_closure_eq]
  have hset : {y : K | ∃ k : ℤ, ∃ x : H, y = (U ^ k) (J x)} =
      Set.range (unitaryOrbitVec U J) := by
    ext y
    constructor
    · rintro ⟨k, x, rfl⟩
      exact ⟨(k, x), rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨p.1, p.2, rfl⟩
  have hspan :
      (span ℂ (Set.range (unitaryOrbitVec U J))).topologicalClosure = ⊤ := by
    rw [← hset]
    exact hmin
  have hr : Set.range (⇑(unitaryOrbit U J)) =
      (span ℂ (Set.range (unitaryOrbitVec U J)) : Set K) := by
    rw [← LinearMap.coe_range, unitaryOrbit, Finsupp.range_linearCombination]
  rw [hr, ← topologicalClosure_coe, hspan, top_coe]

/-- The linear isometry sending each orbit combination to the combination for the second
dilation. -/
def unitaryDilationIsometry (T : H →L[ℂ] H)
    (J : H →ₗᵢ[ℂ] K) (U : K ≃ₗᵢ[ℂ] K)
    (hpow : ∀ n : ℕ, ∀ x : H,
      J.toContinuousLinearMap.adjoint ((U^[n]) (J x)) = (T ^ n) x)
    (hmin : (span ℂ {y : K | ∃ k : ℤ, ∃ x : H, y = (U ^ k) (J x)}).topologicalClosure = ⊤)
    (J' : H →ₗᵢ[ℂ] L) (U' : L ≃ₗᵢ[ℂ] L)
    (hpow' : ∀ n : ℕ, ∀ x : H,
      J'.toContinuousLinearMap.adjoint ((U'^[n]) (J' x)) = (T ^ n) x) :
    K →ₗᵢ[ℂ] L :=
  (unitaryOrbit U' J').extendOfIsometry (e := unitaryOrbit U J)
    (denseRange_unitaryOrbit U J hmin)
    (fun c => norm_unitaryOrbit_eq T J U hpow J' U' hpow' c)

/-- The orbit isometry acts as the identity on coefficients. -/
theorem unitaryDilationIsometry_apply (T : H →L[ℂ] H)
    (J : H →ₗᵢ[ℂ] K) (U : K ≃ₗᵢ[ℂ] K)
    (hpow : ∀ n : ℕ, ∀ x : H,
      J.toContinuousLinearMap.adjoint ((U^[n]) (J x)) = (T ^ n) x)
    (hmin : (span ℂ {y : K | ∃ k : ℤ, ∃ x : H, y = (U ^ k) (J x)}).topologicalClosure = ⊤)
    (J' : H →ₗᵢ[ℂ] L) (U' : L ≃ₗᵢ[ℂ] L)
    (hpow' : ∀ n : ℕ, ∀ x : H,
      J'.toContinuousLinearMap.adjoint ((U'^[n]) (J' x)) = (T ^ n) x)
    (c : (ℤ × H) →₀ ℂ) :
    unitaryDilationIsometry T J U hpow hmin J' U' hpow' (unitaryOrbit U J c) =
      unitaryOrbit U' J' c := by
  rw [unitaryDilationIsometry]
  exact LinearMap.extendOfIsometry_eq (e := unitaryOrbit U J) (unitaryOrbit U' J')
    (denseRange_unitaryOrbit U J hmin)
    (fun b => norm_unitaryOrbit_eq T J U hpow J' U' hpow' b) c

/-- The orbit isometry is surjective because its range is closed and contains a dense orbit. -/
theorem unitaryDilationIsometry_surjective (T : H →L[ℂ] H)
    (J : H →ₗᵢ[ℂ] K) (U : K ≃ₗᵢ[ℂ] K)
    (hpow : ∀ n : ℕ, ∀ x : H,
      J.toContinuousLinearMap.adjoint ((U^[n]) (J x)) = (T ^ n) x)
    (hmin : (span ℂ {y : K | ∃ k : ℤ, ∃ x : H, y = (U ^ k) (J x)}).topologicalClosure = ⊤)
    (J' : H →ₗᵢ[ℂ] L) (U' : L ≃ₗᵢ[ℂ] L)
    (hpow' : ∀ n : ℕ, ∀ x : H,
      J'.toContinuousLinearMap.adjoint ((U'^[n]) (J' x)) = (T ^ n) x)
    (hmin' : (span ℂ {y : L | ∃ k : ℤ, ∃ x : H, y = (U' ^ k) (J' x)}).topologicalClosure = ⊤) :
    Function.Surjective
      (unitaryDilationIsometry T J U hpow hmin J' U' hpow') := by
  let f := unitaryDilationIsometry T J U hpow hmin J' U' hpow'
  rw [← Set.range_eq_univ]
  have hd : Dense (Set.range f) := by
    refine Dense.mono ?_ (denseRange_unitaryOrbit U' J' hmin')
    rintro _ ⟨c, rfl⟩
    exact ⟨unitaryOrbit U J c,
      unitaryDilationIsometry_apply T J U hpow hmin J' U' hpow' c⟩
  have hc : IsClosed (Set.range f) :=
    f.antilipschitzWith.isClosed_range f.isometry.uniformContinuous
  exact hc.closure_eq.symm.trans hd.closure_eq

/-- The unitary sending one minimal unitary power dilation onto the other. -/
def unitaryDilationEquiv (T : H →L[ℂ] H)
    (J : H →ₗᵢ[ℂ] K) (U : K ≃ₗᵢ[ℂ] K)
    (hpow : ∀ n : ℕ, ∀ x : H,
      J.toContinuousLinearMap.adjoint ((U^[n]) (J x)) = (T ^ n) x)
    (hmin : (span ℂ {y : K | ∃ k : ℤ, ∃ x : H, y = (U ^ k) (J x)}).topologicalClosure = ⊤)
    (J' : H →ₗᵢ[ℂ] L) (U' : L ≃ₗᵢ[ℂ] L)
    (hpow' : ∀ n : ℕ, ∀ x : H,
      J'.toContinuousLinearMap.adjoint ((U'^[n]) (J' x)) = (T ^ n) x)
    (hmin' : (span ℂ {y : L | ∃ k : ℤ, ∃ x : H, y = (U' ^ k) (J' x)}).topologicalClosure = ⊤) :
    K ≃ₗᵢ[ℂ] L :=
  LinearIsometryEquiv.ofSurjective
    (unitaryDilationIsometry T J U hpow hmin J' U' hpow')
    (unitaryDilationIsometry_surjective T J U hpow hmin J' U' hpow' hmin')

/-- The unitary dilation equivalence acts as the identity on coefficients. -/
theorem unitaryDilationEquiv_apply (T : H →L[ℂ] H)
    (J : H →ₗᵢ[ℂ] K) (U : K ≃ₗᵢ[ℂ] K)
    (hpow : ∀ n : ℕ, ∀ x : H,
      J.toContinuousLinearMap.adjoint ((U^[n]) (J x)) = (T ^ n) x)
    (hmin : (span ℂ {y : K | ∃ k : ℤ, ∃ x : H, y = (U ^ k) (J x)}).topologicalClosure = ⊤)
    (J' : H →ₗᵢ[ℂ] L) (U' : L ≃ₗᵢ[ℂ] L)
    (hpow' : ∀ n : ℕ, ∀ x : H,
      J'.toContinuousLinearMap.adjoint ((U'^[n]) (J' x)) = (T ^ n) x)
    (hmin' : (span ℂ {y : L | ∃ k : ℤ, ∃ x : H, y = (U' ^ k) (J' x)}).topologicalClosure = ⊤)
    (c : (ℤ × H) →₀ ℂ) :
    unitaryDilationEquiv T J U hpow hmin J' U' hpow' hmin' (unitaryOrbit U J c) =
      unitaryOrbit U' J' c := by
  rw [unitaryDilationEquiv, LinearIsometryEquiv.coe_ofSurjective,
    unitaryDilationIsometry_apply]

/-- The equivalence fixes the embedded copy of the original space. -/
theorem unitaryDilationEquiv_embed (T : H →L[ℂ] H)
    (J : H →ₗᵢ[ℂ] K) (U : K ≃ₗᵢ[ℂ] K)
    (hpow : ∀ n : ℕ, ∀ x : H,
      J.toContinuousLinearMap.adjoint ((U^[n]) (J x)) = (T ^ n) x)
    (hmin : (span ℂ {y : K | ∃ k : ℤ, ∃ x : H, y = (U ^ k) (J x)}).topologicalClosure = ⊤)
    (J' : H →ₗᵢ[ℂ] L) (U' : L ≃ₗᵢ[ℂ] L)
    (hpow' : ∀ n : ℕ, ∀ x : H,
      J'.toContinuousLinearMap.adjoint ((U'^[n]) (J' x)) = (T ^ n) x)
    (hmin' : (span ℂ {y : L | ∃ k : ℤ, ∃ x : H, y = (U' ^ k) (J' x)}).topologicalClosure = ⊤)
    (x : H) :
    unitaryDilationEquiv T J U hpow hmin J' U' hpow' hmin' (J x) = J' x := by
  have hsingle : unitaryOrbit U J (Finsupp.single (0, x) 1) = J x := by
    rw [unitaryOrbit_single, one_smul, unitaryOrbitVec, zpow_zero,
      LinearIsometryEquiv.coe_one]
    rfl
  rw [← hsingle, unitaryDilationEquiv_apply, unitaryOrbit_single, one_smul, unitaryOrbitVec,
    zpow_zero, LinearIsometryEquiv.coe_one]
  rfl

/-- The equivalence intertwines the two unitary dilations. -/
theorem unitaryDilationEquiv_intertwining (T : H →L[ℂ] H)
    (J : H →ₗᵢ[ℂ] K) (U : K ≃ₗᵢ[ℂ] K)
    (hpow : ∀ n : ℕ, ∀ x : H,
      J.toContinuousLinearMap.adjoint ((U^[n]) (J x)) = (T ^ n) x)
    (hmin : (span ℂ {y : K | ∃ k : ℤ, ∃ x : H, y = (U ^ k) (J x)}).topologicalClosure = ⊤)
    (J' : H →ₗᵢ[ℂ] L) (U' : L ≃ₗᵢ[ℂ] L)
    (hpow' : ∀ n : ℕ, ∀ x : H,
      J'.toContinuousLinearMap.adjoint ((U'^[n]) (J' x)) = (T ^ n) x)
    (hmin' : (span ℂ {y : L | ∃ k : ℤ, ∃ x : H, y = (U' ^ k) (J' x)}).topologicalClosure = ⊤)
    (y : K) :
    unitaryDilationEquiv T J U hpow hmin J' U' hpow' hmin' (U y) =
      U' (unitaryDilationEquiv T J U hpow hmin J' U' hpow' hmin' y) := by
  let W := unitaryDilationEquiv T J U hpow hmin J' U' hpow' hmin'
  have hcomp : (fun z => W (U z)) ∘ (unitaryOrbit U J) =
      (fun z => U' (W z)) ∘ (unitaryOrbit U J) := by
    funext c
    rw [Function.comp_apply, Function.comp_apply, unitary_apply_unitaryOrbit,
      unitaryDilationEquiv_apply, unitaryDilationEquiv_apply, unitary_apply_unitaryOrbit]
  have hagree := DenseRange.equalizer (f := unitaryOrbit U J)
    (denseRange_unitaryOrbit U J hmin)
    (W.continuous.comp U.continuous) (U'.continuous.comp W.continuous) hcomp
  exact congr_fun hagree y

omit [CompleteSpace K] [CompleteSpace L] in
/-- Iteration of an intertwiner agrees with the intertwiner of the iterates. -/
theorem intertwining_iterate (U : K ≃ₗᵢ[ℂ] K) (U' : L ≃ₗᵢ[ℂ] L) (W : K ≃ₗᵢ[ℂ] L)
    (hW : ∀ y, W (U y) = U' (W y)) (n : ℕ) (y : K) :
    W ((U^[n]) y) = (U'^[n]) (W y) := by
  induction n generalizing y with
  | zero =>
    rw [Function.iterate_zero, Function.iterate_zero]
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hW, ih]

omit [CompleteSpace K] [CompleteSpace L] in
/-- An intertwiner commutes with the inverse unitary. -/
theorem intertwining_symm (U : K ≃ₗᵢ[ℂ] K) (U' : L ≃ₗᵢ[ℂ] L) (W : K ≃ₗᵢ[ℂ] L)
    (hW : ∀ y, W (U y) = U' (W y)) (y : K) :
    W (U.symm y) = U'.symm (W y) := by
  have h1 : W y = U' (W (U.symm y)) := by
    simpa [LinearIsometryEquiv.apply_symm_apply] using hW (U.symm y)
  have h2 := congrArg (⇑U'.symm) h1
  rw [LinearIsometryEquiv.symm_apply_apply] at h2
  exact h2.symm

omit [CompleteSpace K] [CompleteSpace L] in
/-- Iteration of the inverse intertwines as well. -/
theorem intertwining_symm_iterate (U : K ≃ₗᵢ[ℂ] K) (U' : L ≃ₗᵢ[ℂ] L) (W : K ≃ₗᵢ[ℂ] L)
    (hW : ∀ y, W (U y) = U' (W y)) (n : ℕ) (y : K) :
    W ((U.symm^[n]) y) = (U'.symm^[n]) (W y) := by
  induction n generalizing y with
  | zero =>
    rw [Function.iterate_zero, Function.iterate_zero]
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      intertwining_symm U U' W hW, ih]

omit [CompleteSpace H] [CompleteSpace K] [CompleteSpace L] in
/-- An intertwiner fixing the embedded space preserves every two-sided orbit vector. -/
theorem intertwining_orbit_vec (J : H →ₗᵢ[ℂ] K) (U : K ≃ₗᵢ[ℂ] K)
    (J' : H →ₗᵢ[ℂ] L) (U' : L ≃ₗᵢ[ℂ] L) (W : K ≃ₗᵢ[ℂ] L)
    (hJ : ∀ x, W (J x) = J' x) (hW : ∀ y, W (U y) = U' (W y))
    (k : ℤ) (x : H) :
    W ((U ^ k) (J x)) = (U' ^ k) (J' x) := by
  cases k with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast]
    rw [zpow_natCast, zpow_natCast, linearIsometryEquiv_pow_apply,
      linearIsometryEquiv_pow_apply, intertwining_iterate U U' W hW, hJ]
  | negSucc n =>
    rw [linearIsometryEquiv_zpow_negSucc, linearIsometryEquiv_zpow_negSucc,
      intertwining_symm_iterate U U' W hW, hJ]

omit [CompleteSpace H] [CompleteSpace K] [CompleteSpace L] in
/-- Every unitary intertwiner fixing the embedded space agrees on finite orbit combinations. -/
theorem intertwining_unitaryOrbit (J : H →ₗᵢ[ℂ] K) (U : K ≃ₗᵢ[ℂ] K)
    (J' : H →ₗᵢ[ℂ] L) (U' : L ≃ₗᵢ[ℂ] L) (W : K ≃ₗᵢ[ℂ] L)
    (hJ : ∀ x, W (J x) = J' x) (hW : ∀ y, W (U y) = U' (W y))
    (c : (ℤ × H) →₀ ℂ) :
    W (unitaryOrbit U J c) = unitaryOrbit U' J' c := by
  induction c using Finsupp.induction_linear with
  | zero =>
    rw [map_zero (unitaryOrbit U J), map_zero W, ← map_zero (unitaryOrbit U' J')]
  | add f g ihf ihg =>
    rw [map_add (unitaryOrbit U J), map_add W, ihf, ihg, ← map_add (unitaryOrbit U' J')]
  | single p a =>
    rw [unitaryOrbit_single, map_smul W, unitaryOrbitVec,
      intertwining_orbit_vec J U J' U' W hJ hW p.1 p.2, ← unitaryOrbitVec,
      ← unitaryOrbit_single]

/-- A unitary intertwiner is determined by the embedded space and the unitary action. -/
theorem unitaryDilationEquiv_unique (T : H →L[ℂ] H)
    (J : H →ₗᵢ[ℂ] K) (U : K ≃ₗᵢ[ℂ] K)
    (hpow : ∀ n : ℕ, ∀ x : H,
      J.toContinuousLinearMap.adjoint ((U^[n]) (J x)) = (T ^ n) x)
    (hmin : (span ℂ {y : K | ∃ k : ℤ, ∃ x : H, y = (U ^ k) (J x)}).topologicalClosure = ⊤)
    (J' : H →ₗᵢ[ℂ] L) (U' : L ≃ₗᵢ[ℂ] L)
    (hpow' : ∀ n : ℕ, ∀ x : H,
      J'.toContinuousLinearMap.adjoint ((U'^[n]) (J' x)) = (T ^ n) x)
    (hmin' : (span ℂ {y : L | ∃ k : ℤ, ∃ x : H, y = (U' ^ k) (J' x)}).topologicalClosure = ⊤)
    (W' : K ≃ₗᵢ[ℂ] L) (hJ : ∀ x, W' (J x) = J' x) (hW : ∀ y, W' (U y) = U' (W' y)) :
    W' = unitaryDilationEquiv T J U hpow hmin J' U' hpow' hmin' := by
  let W := unitaryDilationEquiv T J U hpow hmin J' U' hpow' hmin'
  have hcomp : (W' : K → L) ∘ (unitaryOrbit U J) = (W : K → L) ∘ (unitaryOrbit U J) := by
    funext c
    rw [Function.comp_apply, Function.comp_apply, intertwining_unitaryOrbit J U J' U' W' hJ hW,
      unitaryDilationEquiv_apply]
  have hagree := DenseRange.equalizer (f := unitaryOrbit U J)
    (denseRange_unitaryOrbit U J hmin) W'.continuous W.continuous hcomp
  ext y
  exact congr_fun hagree y

/-- Two minimal unitary power dilations are intertwined by a unique unitary fixing `H`. -/
theorem minimalUnitaryPowerDilation_unique_of (T : H →L[ℂ] H)
    (J : H →ₗᵢ[ℂ] K) (U : K ≃ₗᵢ[ℂ] K)
    (hpow : ∀ n : ℕ, ∀ x : H,
      J.toContinuousLinearMap.adjoint ((U^[n]) (J x)) = (T ^ n) x)
    (hmin : (span ℂ {y : K | ∃ k : ℤ, ∃ x : H, y = (U ^ k) (J x)}).topologicalClosure = ⊤)
    (J' : H →ₗᵢ[ℂ] L) (U' : L ≃ₗᵢ[ℂ] L)
    (hpow' : ∀ n : ℕ, ∀ x : H,
      J'.toContinuousLinearMap.adjoint ((U'^[n]) (J' x)) = (T ^ n) x)
    (hmin' : (span ℂ {y : L | ∃ k : ℤ, ∃ x : H, y = (U' ^ k) (J' x)}).topologicalClosure = ⊤) :
    ∃! W : K ≃ₗᵢ[ℂ] L, (∀ x, W (J x) = J' x) ∧ ∀ y, W (U y) = U' (W y) := by
  let W := unitaryDilationEquiv T J U hpow hmin J' U' hpow' hmin'
  refine ⟨W, ⟨?_, ?_⟩, ?_⟩
  · intro x
    exact unitaryDilationEquiv_embed T J U hpow hmin J' U' hpow' hmin' x
  · intro y
    exact unitaryDilationEquiv_intertwining T J U hpow hmin J' U' hpow' hmin' y
  · intro W' hW'
    exact unitaryDilationEquiv_unique T J U hpow hmin J' U' hpow' hmin' W' hW'.1 hW'.2

end CKMA
