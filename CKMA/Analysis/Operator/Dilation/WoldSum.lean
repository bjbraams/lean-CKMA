/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Operator.Dilation.WoldUnitary
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Wold's decomposition as a Hilbert sum

An isometry splits its Hilbert space into the unitary part and the orthogonal shifts of the
wandering subspace. The resulting orthogonal family is a Hilbert sum, and the coordinates of
`Vx` are the shifted coordinates of `x`. The argument is Sz.-Nagy–Foiaş–Bercovici–Kérchy,
Chapter I, Section 1.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped InnerProductSpace
open ContinuousLinearMap Submodule

universe u

variable {E : Type u} [NormedAddCommGroup E]

/-- A constant term at `none` plus a series on `ℕ` is a series on `Option ℕ`. -/
theorem hasSum_option (a : E) (g : ℕ → E) (s : E) (hg : HasSum g s) :
    HasSum (fun i : Option ℕ => match i with
      | none => a
      | some n => g n) (a + s) := by
  classical
  let fSome : Option ℕ → E
    | none => 0
    | some n => g n
  have hzero : ∀ x ∉ Set.range (some : ℕ → Option ℕ), fSome x = 0 := by
    intro x hx
    cases x with
    | none => rfl
    | some n => exact (hx ⟨n, rfl⟩).elim
  have hg' : HasSum (fun n => fSome (some n)) s := by
    simpa [fSome] using hg
  have hsome : HasSum fSome s :=
    ((Option.some_injective ℕ).hasSum_iff hzero).mp hg'
  have hnone : HasSum (fun i : Option ℕ => if i = none then a else 0) a :=
    hasSum_ite_eq none a
  have hadd := hnone.add hsome
  have hfun : (fun i : Option ℕ => (if i = none then a else 0) + fSome i) =
      fun i => match i with
        | none => a
        | some n => g n := by
    funext i
    cases i with
    | none => simp [fSome]
    | some n => simp [fSome]
  rw [← hfun]
  exact hadd

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Summands of the Wold decomposition, indexed by the unitary slot and `ℕ`. -/
@[reducible] def woldSummandNat (V : H →ₗᵢ[ℂ] H) : Option ℕ → Type u
  | none => woldUnitarySubspace V
  | some _ => woldWanderingSubspace V

/-- Each Wold summand is a normed group. -/
instance woldSummandNat.instNormedAddCommGroup (V : H →ₗᵢ[ℂ] H) (i : Option ℕ) :
    NormedAddCommGroup (woldSummandNat V i) :=
  Option.rec (inferInstanceAs (NormedAddCommGroup (woldUnitarySubspace V)))
    (fun _ => inferInstanceAs (NormedAddCommGroup (woldWanderingSubspace V))) i

/-- Each Wold summand is a complex inner product space. -/
instance woldSummandNat.instInnerProductSpace (V : H →ₗᵢ[ℂ] H) (i : Option ℕ) :
    InnerProductSpace ℂ (woldSummandNat V i) :=
  Option.rec (inferInstanceAs (InnerProductSpace ℂ (woldUnitarySubspace V)))
    (fun _ => inferInstanceAs (InnerProductSpace ℂ (woldWanderingSubspace V))) i

/-- Each Wold summand is complete. -/
instance woldSummandNat.instCompleteSpace (V : H →ₗᵢ[ℂ] H) (i : Option ℕ) :
    CompleteSpace (woldSummandNat V i) :=
  Option.rec (inferInstanceAs (CompleteSpace (woldUnitarySubspace V)))
    (fun _ => inferInstanceAs (CompleteSpace (woldWanderingSubspace V))) i

/-- Inclusion of a Wold summand: the unitary part, or the `n`-th wandering shift. -/
@[reducible] def woldSummandIncl (V : H →ₗᵢ[ℂ] H) : ∀ i, woldSummandNat V i →ₗᵢ[ℂ] H :=
  Option.rec (woldUnitarySubspace V).subtypeₗᵢ (fun n => woldShift V n)

/-- The unitary inclusion is the subtype inclusion. -/
theorem woldSummandIncl_none (V : H →ₗᵢ[ℂ] H) (u : woldUnitarySubspace V) :
    woldSummandIncl V none u = u := by
  simp [woldSummandIncl, Submodule.coe_subtypeₗᵢ]

/-- A wandering inclusion is the corresponding shift. -/
theorem woldSummandIncl_some (V : H →ₗᵢ[ℂ] H) (n : ℕ) (w : woldWanderingSubspace V) :
    woldSummandIncl V (some n) w = woldShift V n w := by
  rfl

/-- The Wold summands are pairwise orthogonal. -/
theorem woldSummand_orthogonal (V : H →ₗᵢ[ℂ] H) :
    OrthogonalFamily ℂ (woldSummandNat V) (woldSummandIncl V) := by
  intro i j hij v w
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some n =>
      rw [woldSummandIncl_none, woldSummandIncl_some, woldShift_apply]
      exact woldUnitary_inner_shift_eq_zero V (v : H) v.property n w
  | some m =>
    cases j with
    | none =>
      rw [woldSummandIncl_some, woldSummandIncl_none, woldShift_apply]
      exact inner_eq_zero_symm.mp
        (woldUnitary_inner_shift_eq_zero V (w : H) w.property m v)
    | some n =>
      have hmn : m ≠ n := by
        intro hmn
        exact hij (congrArg some hmn)
      rw [woldSummandIncl_some, woldSummandIncl_some, woldShift_apply, woldShift_apply]
      exact woldShift_inner_eq_zero V m n hmn v w

/-- Every vector is the Hilbert sum of its unitary part and its wandering shifts. -/
theorem wold_hasSum_summand (V : H →ₗᵢ[ℂ] H) (x : H) :
    ∃ f : ∀ i, woldSummandNat V i, HasSum (fun i => woldSummandIncl V i (f i)) x := by
  obtain ⟨u, hu, w, hs⟩ := wold_hasSum_decomposition V x
  let f : ∀ i, woldSummandNat V i
    | none => ⟨u, hu⟩
    | some n => w n
  refine ⟨f, ?_⟩
  have hs' : HasSum (fun n => woldSummandIncl V (some n) (f (some n))) (x - u) := by
    simpa [f, woldSummandIncl_some, woldShift_apply] using hs
  have hopt := hasSum_option (woldSummandIncl V none (f none))
    (fun n => woldSummandIncl V (some n) (f (some n))) (x - u) hs'
  have hfun : (fun i : Option ℕ => match i with
      | none => woldSummandIncl V none (f none)
      | some n => woldSummandIncl V (some n) (f (some n))) =
      fun i => woldSummandIncl V i (f i) := by
    funext i
    cases i with
    | none => rfl
    | some n => rfl
  have hsum : woldSummandIncl V none (f none) + (x - u) = x := by
    rw [woldSummandIncl_none, add_comm]
    exact sub_add_cancel x u
  rw [hfun] at hopt
  have hval : (f none : H) + (x - u) = x := by
    rw [← woldSummandIncl_none V (f none)]
    exact hsum
  simpa [hval] using hopt

/-- Wold's decomposition realises `H` as the Hilbert sum of its summands. -/
theorem wold_isHilbertSum (V : H →ₗᵢ[ℂ] H) :
    IsHilbertSum ℂ (woldSummandNat V) (woldSummandIncl V) := by
  refine IsHilbertSum.mk (woldSummand_orthogonal V) ?_
  intro x _
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  obtain ⟨f, hf⟩ := wold_hasSum_summand V x
  refine mem_closure_of_tendsto hf (Filter.Eventually.of_forall fun s => ?_)
  refine sum_mem fun i _ => ?_
  exact mem_iSup_of_mem i (LinearMap.mem_range_self _ (f i))

/-- A summand coefficient is the inner product against that summand. -/
theorem inner_woldSummandIncl (V : H →ₗᵢ[ℂ] H) (x : H) (i : Option ℕ)
    (v : woldSummandNat V i) :
    ⟪woldSummandIncl V i v, x⟫_ℂ =
      ⟪v, (wold_isHilbertSum V).linearIsometryEquiv x i⟫_ℂ := by
  let Φ := (wold_isHilbertSum V).linearIsometryEquiv
  let f := Φ x
  have hx : Φ.symm f = x := Φ.symm_apply_apply x
  have hs := (wold_isHilbertSum V).hasSum_linearIsometryEquiv_symm f
  have hsum : HasSum (fun j => ⟪woldSummandIncl V i v, woldSummandIncl V j (f j)⟫_ℂ)
      ⟪woldSummandIncl V i v, x⟫_ℂ := by
    rw [← hx]
    simpa [innerSL_apply_apply] using
      (innerSL ℂ (woldSummandIncl V i v)).hasSum hs
  have hterm : ∀ j, ⟪woldSummandIncl V i v, woldSummandIncl V j (f j)⟫_ℂ =
      if j = i then ⟪v, f i⟫_ℂ else 0 := by
    intro j
    by_cases hji : j = i
    · rw [ite_eq_left hji, hji]
      exact (woldSummandIncl V i).inner_map_map v (f i)
    · rw [ite_eq_right hji]
      exact woldSummand_orthogonal V (Ne.symm hji) v (f j)
  have hsingle : HasSum (fun j => ⟪woldSummandIncl V i v, woldSummandIncl V j (f j)⟫_ℂ)
      ⟪v, f i⟫_ℂ := by
    have hfun : (fun j => ⟪woldSummandIncl V i v, woldSummandIncl V j (f j)⟫_ℂ) =
        fun j => if j = i then ⟪v, f i⟫_ℂ else 0 := by
      funext j
      exact hterm j
    rw [hfun]
    exact hasSum_ite_eq i _
  exact hsum.unique hsingle

/-- `Vx` has no new wandering component at time zero. -/
theorem wold_coord_zero (V : H →ₗᵢ[ℂ] H) (x : H) :
    (wold_isHilbertSum V).linearIsometryEquiv (V x) (some 0) = 0 := by
  apply ext_inner_left (𝕜 := ℂ)
  intro w
  rw [inner_zero_right, ← inner_woldSummandIncl V (V x) (some 0) w]
  rw [woldSummandIncl_some, woldShift_apply]
  simp [pow_zero]
  rw [← LinearIsometry.coe_toContinuousLinearMap V]
  have hadj := (adjoint_inner_left V.toContinuousLinearMap x (w : H)).symm
  rw [hadj]
  have hw : V.toContinuousLinearMap.adjoint (w : H) = 0 := by
    have hker := w.property
    simpa [woldWanderingSubspace, LinearMap.mem_ker] using hker
  rw [hw, inner_zero_left]

/-- Applying the isometry shifts wandering coefficients one step to the right. -/
theorem wold_coord_succ (V : H →ₗᵢ[ℂ] H) (x : H) (n : ℕ) :
    (wold_isHilbertSum V).linearIsometryEquiv (V x) (some (n + 1)) =
      (wold_isHilbertSum V).linearIsometryEquiv x (some n) := by
  apply ext_inner_left (𝕜 := ℂ)
  intro w
  rw [← inner_woldSummandIncl V (V x) (some (n + 1)) w,
    ← inner_woldSummandIncl V x (some n) w]
  rw [woldSummandIncl_some, woldSummandIncl_some, woldShift_apply, woldShift_apply]
  rw [← isometry_pow_apply, ← isometry_pow_apply]
  have hpow : (V ^ (n + 1)) (w : H) = V ((V ^ n) (w : H)) := by
    rw [pow_succ', LinearIsometry.mul_def, LinearIsometry.coe_comp, Function.comp_apply]
  rw [hpow]
  exact V.inner_map_map ((V ^ n) (w : H)) x

/-- Applying the isometry acts on the unitary coordinate by the restricted unitary. -/
theorem wold_coord_unitary (V : H →ₗᵢ[ℂ] H) (x : H) :
    (wold_isHilbertSum V).linearIsometryEquiv (V x) none =
      woldUnitaryEquiv V ((wold_isHilbertSum V).linearIsometryEquiv x none) := by
  apply ext_inner_left (𝕜 := ℂ)
  intro u
  have hleft : ⟪u, (wold_isHilbertSum V).linearIsometryEquiv (V x) none⟫_ℂ =
      ⟪(u : H), V x⟫_ℂ := by
    rw [← inner_woldSummandIncl V (V x) none u, woldSummandIncl_none]
  have hmid : ⟪(u : H), V x⟫_ℂ =
      ⟪((woldUnitaryEquiv V).symm u : H), x⟫_ℂ := by
    rw [coe_woldUnitaryEquiv_symm]
    exact (adjoint_inner_left V.toContinuousLinearMap x (u : H)).symm
  have hright : ⟪((woldUnitaryEquiv V).symm u : H), x⟫_ℂ =
      ⟪(woldUnitaryEquiv V).symm u,
        (wold_isHilbertSum V).linearIsometryEquiv x none⟫_ℂ := by
    rw [← inner_woldSummandIncl V x none ((woldUnitaryEquiv V).symm u), woldSummandIncl_none]
  have hunit : ⟪(woldUnitaryEquiv V).symm u,
      (wold_isHilbertSum V).linearIsometryEquiv x none⟫_ℂ =
      ⟪u, woldUnitaryEquiv V
        ((wold_isHilbertSum V).linearIsometryEquiv x none)⟫_ℂ := by
    have hmap := (woldUnitaryEquiv V).inner_map_map ((woldUnitaryEquiv V).symm u)
      ((wold_isHilbertSum V).linearIsometryEquiv x none)
    rw [LinearIsometryEquiv.apply_symm_apply] at hmap
    exact hmap.symm
  rw [hleft, hmid, hright, hunit]

end CKMA
