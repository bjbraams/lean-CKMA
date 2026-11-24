/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.CStarAlgebra.OperatorClosures.Bicommutant

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Kaplansky
import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
import TauCeti.Analysis.VonNeumannAlgebra.Bicommutant
import TauCeti.Analysis.InnerProductSpace.Amplification

/-!
# Kaplansky density for nondegenerate operator algebras

Kaplansky density allows nonunital star subalgebras but explicitly assumes a nondegenerate
action on the Hilbert space. The self-adjoint unit-ball statement is proved first, and the
full unit ball is reduced to it by an off-diagonal corner on the Hilbert sum of two copies.
Inner products follow Mathlib's convention of linearity in the second variable.
Sources: GAPS 23.22.

The self-adjoint strong closure is TauCeti's
`StarSubalgebra.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint`. The Kaplansky
function, its difference identity, and the norm bound are `TauCeti.kaplanskyFun`,
`TauCeti.cfc_kaplanskyFun_sub_cfc_kaplanskyFun`, and `TauCeti.norm_cfc_kaplanskyFun_le`.
Nondegeneracy along an increasing approximate unit is
`NonUnitalStarAlgHom.isNondegenerate_iff_tendsto`. These TauCeti modules are imported
directly: the arguments are operator-algebraic and do not factor through another CKMA
section's `Basic` file.

## Main results

* `CKMA.kaplansky_density_selfAdjoint`: strong density of the self-adjoint unit ball.
* `CKMA.kaplansky_density`: Kaplansky density theorem (**23.22**).
-/

public section

noncomputable section

namespace CKMA

open Filter Topology
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open ContinuousLinearMap TauCeti

/-- The Kaplansky difference identity, applied to one vector and bounded by the operator norms of
`ρ` and `σ`. -/
private theorem norm_sub_cfc_kaplanskyFun_apply_le {a b : H →L[ℂ] H} (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) (v : H) :
    ‖(cfc kaplanskyFun a - cfc kaplanskyFun b) v‖ ≤
      2 * ‖(a - b) (cfc (fun t : ℝ => (1 + t ^ 2)⁻¹) b v)‖ +
        ‖(a - b) (cfc (fun t : ℝ => t / (1 + t ^ 2)) b v)‖ := by
  set w₁ : H := cfc (fun t : ℝ => (1 + t ^ 2)⁻¹) b v
  set w₂ : H := cfc (fun t : ℝ => t / (1 + t ^ 2)) b v
  have key : cfc kaplanskyFun a v - cfc kaplanskyFun b v = (2 : ℝ) •
      (cfc (fun t : ℝ => (1 + t ^ 2)⁻¹) a ((a - b) w₁) +
        cfc (fun t : ℝ => t / (1 + t ^ 2)) a ((b - a) w₂)) := by
    rw [← sub_apply, cfc_kaplanskyFun_sub_cfc_kaplanskyFun ha hb]
    simp [w₁, w₂]
  have hneg : (b - a) w₂ = -((a - b) w₂) := by simp [neg_sub]
  rw [sub_apply, key, norm_smul, Real.norm_two]
  calc 2 * ‖cfc (fun t : ℝ => (1 + t ^ 2)⁻¹) a ((a - b) w₁) +
          cfc (fun t : ℝ => t / (1 + t ^ 2)) a ((b - a) w₂)‖
      ≤ 2 * (‖cfc (fun t : ℝ => (1 + t ^ 2)⁻¹) a ((a - b) w₁)‖ +
          ‖cfc (fun t : ℝ => t / (1 + t ^ 2)) a ((b - a) w₂)‖) := by
        gcongr
        exact norm_add_le _ _
    _ ≤ 2 * (‖(a - b) w₁‖ + (1 / 2) * ‖(b - a) w₂‖) := by
        gcongr
        · exact (le_of_opNorm_le _ (norm_cfc_inv_one_add_sq_le a) _).trans_eq (one_mul _)
        · exact le_of_opNorm_le _ (norm_cfc_div_one_add_sq_le a) _
    _ = 2 * ‖(a - b) w₁‖ + ‖(a - b) w₂‖ := by
        rw [hneg, norm_neg]
        ring

/-- A self-adjoint operator in the bicommutant is a strong limit of self-adjoint elements of the
unital star algebra, by TauCeti's self-adjoint strong bicommutant theorem. -/
private theorem exists_mem_selfAdjoint_forall_norm_sub_apply_lt
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) {x : H →L[ℂ] H}
    (hx : x ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer) (hxsa : IsSelfAdjoint x)
    {ι : Type*} [Finite ι] (v : ι → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ S, IsSelfAdjoint s ∧ ∀ i, ‖(s - x) (v i)‖ < ε := by
  let q := toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
  have hmem : q x ∈ closure
      (q '' ((S : Set (H →L[ℂ] H)) ∩ selfAdjoint (H →L[ℂ] H))) := by
    rw [S.closure_image_toPointwiseConvergenceCLM_inter_selfAdjoint]
    exact ⟨x, ⟨hx, hxsa⟩, rfl⟩
  let U : Set (H →Lₚₜ[ℂ] H) := {f | ∀ i, ‖(f - q x) (v i)‖ < ε}
  have hc (i : ι) : Continuous (fun f : H →Lₚₜ[ℂ] H => ‖(f - q x) (v i)‖) :=
    ((continuous_eval_const (v i)).sub continuous_const).norm
  have hU : IsOpen U := by
    simp only [U, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (hc i) continuous_const
  have hqx : q x ∈ U := by
    intro i
    simp [norm_zero, hε]
  obtain ⟨y, hyU, s, hs, rfl⟩ := (mem_closure_iff.mp hmem) U hU hqx
  obtain ⟨hsS, hssa⟩ := hs
  refine ⟨s, hsS, selfAdjoint.mem_iff.mp hssa, fun i => ?_⟩
  exact hyU i

/-- Passing to the norm closure does not change the bicommutant. -/
private theorem centralizer_centralizer_topologicalClosure
    (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    (A.topologicalClosure : Set (H →L[ℂ] H)).centralizer.centralizer =
      (A : Set (H →L[ℂ] H)).centralizer.centralizer := by
  let Sset : Set (H →L[ℂ] H) := A
  have hcoe : (A.topologicalClosure : Set (H →L[ℂ] H)) = closure Sset := rfl
  have hBA : closure Sset ⊆ Sset.centralizer.centralizer :=
    closure_minimal (Set.subset_centralizer_centralizer (S := Sset))
      (Set.isClosed_centralizer Sset.centralizer)
  have hquad : Sset.centralizer.centralizer.centralizer.centralizer =
      Sset.centralizer.centralizer :=
    Set.centralizer_centralizer_centralizer Sset.centralizer
  have h1 : (closure Sset).centralizer.centralizer ⊆ Sset.centralizer.centralizer := by
    rw [← hquad]
    exact Set.centralizer_subset (Set.centralizer_subset hBA)
  have h2 : Sset.centralizer.centralizer ⊆ (closure Sset).centralizer.centralizer :=
    Set.centralizer_subset (Set.centralizer_subset subset_closure)
  rw [hcoe]
  exact subset_antisymm h1 h2

/-- The unitization of a non-unital star algebra of operators has the same commutant: scalars of
the identity commute with every operator. -/
private theorem centralizer_adjoin_nonUnitalStarSubalgebra
    (B : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    (StarAlgebra.adjoin ℂ (B : Set (H →L[ℂ] H)) : Set _).centralizer =
      (B : Set (H →L[ℂ] H)).centralizer := by
  apply subset_antisymm
  · intro x hx a ha
    exact hx a (StarAlgebra.subset_adjoin ℂ (B : Set (H →L[ℂ] H)) ha)
  · intro x hx s hs
    have hsmod : s ∈ (StarAlgebra.adjoin ℂ (B : Set _)).toSubalgebra.toSubmodule := hs
    rw [StarAlgebra.adjoin_nonUnitalStarSubalgebra_eq_span] at hsmod
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hsmod
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hzB : (z : H →L[ℂ] H) ∈ B := hz
    have hzcomm : z * x = x * z := hx z hzB
    rw [mul_add, add_mul, hzcomm]
    congr 1
    simp [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]

/-- A self-adjoint element of the unitization splits as a real multiple of the identity plus a
self-adjoint element of the original algebra. -/
private theorem exists_selfAdjoint_eq_add_smul_one
    {B : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)} {s : H →L[ℂ] H}
    (hs : s ∈ StarAlgebra.adjoin ℂ (B : Set (H →L[ℂ] H))) (hsa : IsSelfAdjoint s) :
    ∃ c : ℂ, ∃ a : H →L[ℂ] H, IsSelfAdjoint c ∧ a ∈ B ∧ IsSelfAdjoint a ∧ s = a + c • 1 := by
  have hsmod : s ∈ (StarAlgebra.adjoin ℂ (B : Set _)).toSubalgebra.toSubmodule := hs
  rw [StarAlgebra.adjoin_nonUnitalStarSubalgebra_eq_span] at hsmod
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hsmod
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
  have hsum : s = c • (1 : H →L[ℂ] H) + z := by simpa [hc, add_comm] using hyz.symm
  let c' : ℂ := (2⁻¹ : ℂ) * (c + star c)
  let a : H →L[ℂ] H := (2⁻¹ : ℂ) • (z + star z)
  have hc' : IsSelfAdjoint c' := by
    simp [c', isSelfAdjoint_iff, star_mul, star_inv₀, star_add, add_comm, mul_comm]
  have ha : a ∈ B := SMulMemClass.smul_mem _ (add_mem hz (star_mem hz))
  have hasa : IsSelfAdjoint a := by
    have h2 : IsSelfAdjoint (2⁻¹ : ℂ) := by simp [isSelfAdjoint_iff, star_inv₀]
    exact h2.smul (by simp [isSelfAdjoint_iff, star_add, add_comm])
  have heq : s = a + c' • 1 := by
    have hhalf : (2⁻¹ : ℂ) • (s + star s) = s := by
      rw [hsa.star_eq, ← two_smul ℂ s, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    have hregroup : c • (1 : H →L[ℂ] H) + z + (star c • 1 + star z) =
        (c + star c) • 1 + (z + star z) := by
      rw [add_add_add_comm, ← add_smul]
    calc s = (2⁻¹ : ℂ) • (s + star s) := hhalf.symm
      _ = (2⁻¹ : ℂ) • (c • 1 + z + star (c • 1 + z)) := by rw [hsum]
      _ = (2⁻¹ : ℂ) • (c • 1 + z + (star c • 1 + star z)) := by
          simp [star_add, star_smul, star_one]
      _ = (2⁻¹ : ℂ) • ((c + star c) • 1 + (z + star z)) := by rw [hregroup]
      _ = c' • 1 + a := by simp [c', a, smul_add, smul_smul]
      _ = a + c' • 1 := add_comm _ _
  exact ⟨c', a, hc', ha, hasa, heq⟩

/-- Norm closure in the self-adjoint part of the unit ball can be taken inside the original
algebra. -/
private theorem exists_unitBall_selfAdjoint_norm_lt
    (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) {u : H →L[ℂ] H}
    (hu : u ∈ closure (A : Set (H →L[ℂ] H))) (husa : IsSelfAdjoint u) (hub : ‖u‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ a : H →L[ℂ] H, a ∈ A ∧ ‖a‖ ≤ 1 ∧ IsSelfAdjoint a ∧ ‖a - u‖ < δ := by
  obtain ⟨a1, ha1, ha1u⟩ := Metric.mem_closure_iff.mp hu (δ / 2) (half_pos hδ)
  rw [dist_eq_norm, norm_sub_rev] at ha1u
  let a2 : H →L[ℂ] H := (2⁻¹ : ℂ) • (a1 + star a1)
  have ha2mem : a2 ∈ A := SMulMemClass.smul_mem _ (add_mem ha1 (star_mem ha1))
  have ha2sa : IsSelfAdjoint a2 := by
    have h2 : IsSelfAdjoint (2⁻¹ : ℂ) := by simp [isSelfAdjoint_iff, star_inv₀]
    exact h2.smul (by simp [isSelfAdjoint_iff, star_add, add_comm])
  have hform : (2⁻¹ : ℂ) • ((a1 - u) + star (a1 - u)) = a2 - u := by
    have hstar : star (a1 - u) = star a1 - u := by rw [star_sub, husa.star_eq]
    have hhalf : (2⁻¹ : ℂ) • (u + u) = u := by
      rw [← two_smul ℂ u, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    have hsum : a1 - u + (star a1 - u) = a1 + star a1 - (u + u) := by
      rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add, add_add_add_comm]
    rw [hstar, hsum, smul_sub, hhalf]
  have hnorm2 : ‖(2⁻¹ : ℂ)‖ = (2⁻¹ : ℝ) := by
    rw [norm_inv, Complex.norm_two]
  have ha2u : ‖a2 - u‖ ≤ ‖a1 - u‖ := by
    rw [← hform, norm_smul, hnorm2]
    calc (2⁻¹ : ℝ) * ‖(a1 - u) + star (a1 - u)‖
        ≤ (2⁻¹ : ℝ) * (‖a1 - u‖ + ‖star (a1 - u)‖) := by
          gcongr
          exact norm_add_le _ _
      _ = ‖a1 - u‖ := by rw [norm_star]; ring
  by_cases hle : ‖a2‖ ≤ 1
  · exact ⟨a2, ha2mem, hle, ha2sa, (ha2u.trans_lt ha1u).trans (half_lt_self hδ)⟩
  · have hgt : 1 < ‖a2‖ := lt_of_not_ge hle
    let r : ℝ := ‖a2‖⁻¹
    let a : H →L[ℂ] H := (r : ℂ) • a2
    have ha2_pos : 0 < ‖a2‖ := zero_lt_one.trans hgt
    have ha_mem : a ∈ A := SMulMemClass.smul_mem (r : ℂ) ha2mem
    have hr : IsSelfAdjoint (r : ℂ) := by
      simp [isSelfAdjoint_iff, Complex.conj_ofReal]
    have ha_sa : IsSelfAdjoint a := hr.smul ha2sa
    have ha_norm : ‖a‖ ≤ 1 := by
      apply le_of_eq
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha2_pos)]
      exact inv_mul_cancel₀ ha2_pos.ne'
    have hrlt : r - 1 < 0 := sub_neg.mpr (inv_lt_one_of_one_lt₀ hgt)
    have hdiff : ‖a - a2‖ = ‖a2‖ - 1 := by
      have hsub : a - a2 = ((r : ℂ) - 1) • a2 := by rw [sub_smul, one_smul]
      rw [hsub, norm_smul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_neg hrlt, neg_sub]
      have hr1 : r * ‖a2‖ = 1 := inv_mul_cancel₀ ha2_pos.ne'
      calc (1 - r) * ‖a2‖ = ‖a2‖ - r * ‖a2‖ := by ring
        _ = ‖a2‖ - 1 := by rw [hr1]
    have hshrink : ‖a2‖ - 1 ≤ ‖a2 - u‖ := by
      have htri : ‖a2‖ ≤ ‖a2 - u‖ + ‖u‖ := by
        simpa [sub_add_cancel] using norm_add_le (a2 - u) u
      linarith [hub, htri]
    have hau : ‖a - u‖ < δ := by
      have hlt : ‖a2 - u‖ < δ / 2 := ha2u.trans_lt ha1u
      calc ‖a - u‖ = ‖(a - a2) + (a2 - u)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖a - a2‖ + ‖a2 - u‖ := norm_add_le _ _
        _ = (‖a2‖ - 1) + ‖a2 - u‖ := by rw [hdiff]
        _ ≤ ‖a2 - u‖ + ‖a2 - u‖ := by linarith [hshrink]
        _ < δ := by linarith [hlt]
    exact ⟨a, ha_mem, ha_norm, ha_sa, hau⟩

/-- The set of vectors `a y` agrees with the union of the ranges of the inclusion representation.
-/
private theorem actionSet_eq_iUnion_range (B : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    {x : H | ∃ a ∈ B, ∃ y : H, a y = x} =
      ⋃ a : B, Set.range (NonUnitalStarSubalgebraClass.subtype B a) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_range,
    NonUnitalStarSubalgebraClass.subtype_apply]
  constructor
  · rintro ⟨a, ha, y, rfl⟩
    exact ⟨⟨a, ha⟩, y, rfl⟩
  · rintro ⟨a, y, rfl⟩
    exact ⟨a, a.2, y, rfl⟩

/-- The self-adjoint unit-ball version of Kaplansky density. -/
theorem kaplansky_density_selfAdjoint (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (hd : Dense (Submodule.span ℂ {x : H | ∃ a ∈ A, ∃ y : H, a y = x} : Set H))
    (T : H →L[ℂ] H) (hT : T ∈ boundedOperatorCommutant
      (boundedOperatorCommutant (A : Set (H →L[ℂ] H)))) (hbound : ‖T‖ ≤ 1)
    (hsa : IsSelfAdjoint T) :
    IsStrongOperatorApproximable {a | a ∈ A ∧ ‖a‖ ≤ 1 ∧ IsSelfAdjoint a} T := by
  let B := A.topologicalClosure
  have : IsClosed (B : Set (H →L[ℂ] H)) := A.isClosed_topologicalClosure
  let S := StarAlgebra.adjoin ℂ (B : Set (H →L[ℂ] H))
  have hcomm1 : (S : Set (H →L[ℂ] H)).centralizer =
      (B : Set (H →L[ℂ] H)).centralizer :=
    centralizer_adjoin_nonUnitalStarSubalgebra B
  have hcommS : (S : Set (H →L[ℂ] H)).centralizer.centralizer =
      (B : Set (H →L[ℂ] H)).centralizer.centralizer := by
    rw [hcomm1]
  have hTB : T ∈ (B : Set (H →L[ℂ] H)).centralizer.centralizer := by
    unfold B
    rw [centralizer_centralizer_topologicalClosure]
    exact hT
  let Bset : Set (H →L[ℂ] H) := B
  let M : StarSubalgebra ℂ (H →L[ℂ] H) :=
    StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ Bset : Set (H →L[ℂ] H))
  have hM : (M : Set (H →L[ℂ] H)) = Bset.centralizer.centralizer := by
    rw [StarSubalgebra.coe_centralizer_centralizer, StarMemClass.star_coe_eq B,
      Set.union_self]
  have : IsClosed (M : Set (H →L[ℂ] H)) := by
    rw [hM]
    exact Set.isClosed_centralizer _
  have hTM : T ∈ M := by
    rw [← SetLike.mem_coe, hM]
    exact hTB
  let h0 : H →L[ℂ] H := cfc kaplanskyFunInv T
  have hh0M : h0 ∈ M := cfc_mem kaplanskyFunInv hTM
  have hh0sa : IsSelfAdjoint h0 := IsSelfAdjoint.cfc
  have hh0S : h0 ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer := by
    rw [hcommS, ← hM]
    exact hh0M
  have hrec : cfc kaplanskyFun h0 = T :=
    IsSelfAdjoint.cfc_kaplanskyFun_cfc_kaplanskyFunInv hsa hbound
  have hdB : Dense (Submodule.span ℂ {x : H | ∃ a ∈ B, ∃ y : H, a y = x} : Set H) :=
    hd.mono <| Submodule.span_mono fun x hx => by
      obtain ⟨a, ha, y, rfl⟩ := hx
      exact ⟨a, A.le_topologicalClosure ha, y, rfl⟩
  let π := NonUnitalStarSubalgebraClass.subtype B
  have hπ : π.IsNondegenerate := by
    rw [NonUnitalStarAlgHom.isNondegenerate_iff_dense, ← actionSet_eq_iUnion_range]
    exact hdB
  let := CStarAlgebra.spectralOrder B
  have := CStarAlgebra.spectralOrderedRing B
  have hl : (CStarAlgebra.approximateUnit B).IsIncreasingApproximateUnit :=
    CStarAlgebra.increasingApproximateUnit B
  have htend : ∀ ξ, Tendsto (fun e => π e ξ) (CStarAlgebra.approximateUnit B) (𝓝 ξ) :=
    (π.isNondegenerate_iff_tendsto hl.eventually_norm hl.tendsto_mul_right).1 hπ
  intro n v ε hε
  let w : Fin n × Fin 2 → H := fun p =>
    if p.2 = 0 then cfc (fun t : ℝ => (1 + t ^ 2)⁻¹) h0 (v p.1)
    else cfc (fun t : ℝ => t / (1 + t ^ 2)) h0 (v p.1)
  have hε12 : 0 < ε / 12 := div_pos hε (by norm_num)
  obtain ⟨s, hsS, hssa, hsapprox⟩ :=
    exists_mem_selfAdjoint_forall_norm_sub_apply_lt S hh0S hh0sa w hε12
  obtain ⟨c, a0, hc, ha0, ha0sa, hs_eq⟩ := exists_selfAdjoint_eq_add_smul_one hsS hssa
  set δe : ℝ := (ε / 12) / (‖c‖ + 1) with hδedef
  have hδe : 0 < δe := by positivity
  have hev : ∀ᶠ (e : B) in CStarAlgebra.approximateUnit B,
      (∀ p, ‖(e : H →L[ℂ] H) (w p) - w p‖ < δe) ∧ IsSelfAdjoint e := by
    refine (eventually_all.mpr fun p => ?_).and hl.eventually_isSelfAdjoint
    have hdist := (Metric.tendsto_nhds.mp (htend (w p))) δe hδe
    simpa [π, NonUnitalStarSubalgebraClass.subtype_apply, dist_eq_norm] using hdist
  obtain ⟨e, he_close, he_sa⟩ := hev.exists
  have hxe : IsSelfAdjoint (e : H →L[ℂ] H) := congrArg Subtype.val he_sa.star_eq
  let x : H →L[ℂ] H := a0 + c • (e : H →L[ℂ] H)
  have hxsa : IsSelfAdjoint x := ha0sa.add (hc.smul hxe)
  have hxmem : x ∈ B := add_mem ha0 (SMulMemClass.smul_mem c (SetLike.coe_mem e))
  have hxs (p : Fin n × Fin 2) : ‖(x - s) (w p)‖ < ε / 12 := by
    have hdiff : (x - s) (w p) = c • ((e : H →L[ℂ] H) (w p) - w p) := by
      have hxapply : x (w p) = a0 (w p) + c • (e : H →L[ℂ] H) (w p) := by
        simp [x, add_apply, smul_apply]
      have hsapply : s (w p) = a0 (w p) + c • w p := by
        rw [hs_eq, add_apply, smul_apply, one_apply_eq_self]
      rw [sub_apply, hxapply, hsapply, add_sub_add_comm, sub_self, zero_add, ← smul_sub]
    rw [hdiff, norm_smul]
    have hprod : ‖c‖ * δe < ε / 12 := by
      rw [hδedef, mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [hε]
    calc ‖c‖ * ‖(e : H →L[ℂ] H) (w p) - w p‖
        ≤ ‖c‖ * δe := mul_le_mul_of_nonneg_left (he_close p).le (norm_nonneg _)
      _ < ε / 12 := hprod
  have hxh (p : Fin n × Fin 2) : ‖(x - h0) (w p)‖ < ε / 6 := by
    calc ‖(x - h0) (w p)‖ = ‖(x - s) (w p) + (s - h0) (w p)‖ := by
          rw [← sub_add_sub_cancel x s h0, add_apply]
      _ ≤ ‖(x - s) (w p)‖ + ‖(s - h0) (w p)‖ := norm_add_le _ _
      _ < ε / 12 + ε / 12 := add_lt_add (hxs p) (hsapprox p)
      _ = ε / 6 := by ring
  let u : H →L[ℂ] H := cfc kaplanskyFun x
  have hu_sa : IsSelfAdjoint u := IsSelfAdjoint.cfc
  have hub : ‖u‖ ≤ 1 := norm_cfc_kaplanskyFun_le x
  have huB : u ∈ B := by
    have hfun0 : kaplanskyFun 0 = 0 := by
      rw [kaplanskyFun_def]
      simp
    unfold u
    rw [← cfcₙ_eq_cfc (hf := continuous_kaplanskyFun.continuousOn) (hf0 := hfun0)]
    exact cfcₙ_mem kaplanskyFun hxmem
  have huT (i : Fin n) : ‖(u - T) (v i)‖ < ε / 2 := by
    have hboundv := norm_sub_cfc_kaplanskyFun_apply_le hxsa hh0sa (v i)
    rw [hrec] at hboundv
    have hw0 : w (i, 0) = cfc (fun t : ℝ => (1 + t ^ 2)⁻¹) h0 (v i) := by simp [w]
    have hw1 : w (i, 1) = cfc (fun t : ℝ => t / (1 + t ^ 2)) h0 (v i) := by
      simp [w]
    have hd0 : ‖(x - h0) (w (i, 0))‖ < ε / 6 := hxh (i, 0)
    have hd1 : ‖(x - h0) (w (i, 1))‖ < ε / 6 := hxh (i, 1)
    calc ‖(u - T) (v i)‖ ≤ 2 * ‖(x - h0) (w (i, 0))‖ + ‖(x - h0) (w (i, 1))‖ := by
          simpa [u, hw0, hw1] using hboundv
      _ < 2 * (ε / 6) + ε / 6 := by gcongr
      _ = ε / 2 := by ring
  let C : ℝ := ∑ i, ‖v i‖
  set δ : ℝ := ε / (2 * (C + 1))
  have hδ : 0 < δ := by positivity
  have hucl : u ∈ closure (A : Set (H →L[ℂ] H)) := by
    have hBclosure : (B : Set (H →L[ℂ] H)) = closure (A : Set (H →L[ℂ] H)) := rfl
    rw [← hBclosure, SetLike.mem_coe]
    exact huB
  obtain ⟨a, ha, ha_norm, ha_sa, hau⟩ :=
    exists_unitBall_selfAdjoint_norm_lt A hucl hu_sa hub hδ
  refine ⟨a, ⟨ha, ha_norm, ha_sa⟩, fun i => ?_⟩
  have hvi : ‖v i‖ ≤ C := Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have hδv : δ * ‖v i‖ ≤ ε / 2 := by
    calc δ * ‖v i‖ ≤ δ * C := mul_le_mul_of_nonneg_left hvi (le_of_lt hδ)
      _ = ε * C / (2 * (C + 1)) := by
          unfold δ
          rw [div_mul_eq_mul_div₀]
      _ ≤ ε / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  calc ‖(a - T) (v i)‖ = ‖(a - u) (v i) + (u - T) (v i)‖ := by
        rw [← sub_add_sub_cancel a u T, add_apply]
    _ ≤ ‖(a - u) (v i)‖ + ‖(u - T) (v i)‖ := norm_add_le _ _
    _ ≤ ‖a - u‖ * ‖v i‖ + ‖(u - T) (v i)‖ := by
        gcongr
        exact (a - u).le_opNorm (v i)
    _ < ‖a - u‖ * ‖v i‖ + ε / 2 := by gcongr; exact huT i
    _ ≤ δ * ‖v i‖ + ε / 2 := by gcongr
    _ ≤ ε / 2 + ε / 2 := by gcongr
    _ = ε := by ring

-- Notation, rather than an abbreviation: an abbreviation is not unfolded during typeclass search.
local notation "twoCopy" => PiLp 2 (fun _ : Fin 2 => H)

section

omit [CompleteSpace H]

/-- The inner product against a vector supported on one summand is the corresponding component. -/
private theorem inner_piLp_single_left (i : Fin 2) (h : H) (w : twoCopy) :
    ⟪PiLp.single 2 i h, w⟫_ℂ = ⟪h, w i⟫_ℂ := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  by_cases hi : i = 0
  · subst hi
    simp [inner_zero_left]
  · have hi1 : i = 1 := Fin.eq_one_of_ne_zero i hi
    subst hi1
    simp [inner_zero_left]

/-- The inner product of a vector against one supported on a single summand. -/
private theorem inner_piLp_single_right (j : Fin 2) (h : H) (w : twoCopy) :
    ⟪w, PiLp.single 2 j h⟫_ℂ = ⟪w j, h⟫_ℂ := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  by_cases hj : j = 0
  · subst hj
    simp [inner_zero_right]
  · have hj1 : j = 1 := Fin.eq_one_of_ne_zero j hj
    subst hj1
    simp [inner_zero_right]

end

/-- The adjoint of a coordinate projection inserts a vector into that summand. -/
private theorem adjoint_proj_apply (i : Fin 2) (z : H) :
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => H) i).adjoint z =
      PiLp.single (β := fun _ : Fin 2 => H) 2 i z := by
  refine ext_inner_left ℂ fun w => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, PiLp.proj_apply, ← inner_piLp_single_right]

/-- The operator on the Hilbert sum sending the `j`-th summand into the `i`-th summand by `a`. -/
private def corner (i j : Fin 2) (a : H →L[ℂ] H) : twoCopy →L[ℂ] twoCopy :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => H) i).adjoint ∘L a ∘L
    PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => H) j

/-- A corner acts by applying `a` to the `j`-th component and placing the result at index `i`. -/
@[simp] private theorem corner_apply (i j : Fin 2) (a : H →L[ℂ] H) (w : twoCopy) :
    corner i j a w = PiLp.single (β := fun _ : Fin 2 => H) 2 i (a (w j)) := by
  simp [corner, comp_apply, adjoint_proj_apply, PiLp.proj_apply]

/-- Starring a corner swaps its indices and stars the coefficient. -/
private theorem star_corner (i j : Fin 2) (a : H →L[ℂ] H) :
    star (corner i j a) = corner j i (star a) := by
  unfold corner
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.star_eq_adjoint]

/-- Matrix entries of a corner are `a` in position `(i, j)` and zero elsewhere. -/
private theorem piLpEntry_corner (a : H →L[ℂ] H) (i j p q : Fin 2) :
    (corner i j a).piLpEntry p q = if p = i ∧ q = j then a else 0 := by
  ext h
  rw [piLpEntry_apply, corner_apply]
  by_cases hp : p = i <;> by_cases hq : q = j
  · subst hp
    subst hq
    simp
  · subst hp
    simp [hq, map_zero, PiLp.single_eq_same]
  · simp [hp, PiLp.single_eq_of_ne]
  · simp [hp, PiLp.single_eq_of_ne]

section

omit [CompleteSpace H]

/-- The zero operator has zero matrix entries. -/
@[simp] private theorem piLpEntry_zero (i j : Fin 2) :
    (0 : twoCopy →L[ℂ] twoCopy).piLpEntry i j = 0 := by
  ext
  simp [piLpEntry_apply]

/-- Matrix entries are additive. -/
private theorem piLpEntry_add (S T : twoCopy →L[ℂ] twoCopy) (i j : Fin 2) :
    (S + T).piLpEntry i j = S.piLpEntry i j + T.piLpEntry i j := by
  ext
  simp [piLpEntry_apply, add_apply]

/-- Matrix entries commute with scalar multiplication. -/
private theorem piLpEntry_smul (c : ℂ) (T : twoCopy →L[ℂ] twoCopy) (i j : Fin 2) :
    (c • T).piLpEntry i j = c • T.piLpEntry i j := by
  ext
  simp [piLpEntry_apply, smul_apply]

end

section

omit [CompleteSpace H]

/-- The matrix entries of a product are the row-column products of the entries. -/
private theorem piLpEntry_mul (S T : twoCopy →L[ℂ] twoCopy) (i k : Fin 2) :
    (S * T).piLpEntry i k = ∑ j : Fin 2, S.piLpEntry i j * T.piLpEntry j k := by
  ext h
  rw [piLpEntry_apply, mul_apply_eq_comp, apply_eq_sum_piLpEntry]
  have hsum : (∑ j : Fin 2, S.piLpEntry i j * T.piLpEntry j k) h =
      ∑ j : Fin 2, (S.piLpEntry i j * T.piLpEntry j k) h := by
    let φ : (H →L[ℂ] H) →+ H → H := FunLike.coeAddMonoidHom (H →L[ℂ] H) H H
    have hφ := congr_fun (map_sum φ
      (fun j : Fin 2 => S.piLpEntry i j * T.piLpEntry j k) Finset.univ) h
    rw [FunLike.coeAddMonoidHom_apply] at hφ
    rw [Finset.sum_apply] at hφ
    exact hφ
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_apply_eq_comp, ← piLpEntry_apply]

end

/-- Starring an operator on the Hilbert sum transposes and stars its matrix entries. -/
private theorem piLpEntry_star (T : twoCopy →L[ℂ] twoCopy) (i j : Fin 2) :
    (star T).piLpEntry i j = star (T.piLpEntry j i) := by
  ext ξ
  refine ext_inner_left ℂ fun h => ?_
  calc ⟪h, (star T).piLpEntry i j ξ⟫_ℂ
      = ⟪h, (ContinuousLinearMap.adjoint T (PiLp.single 2 j ξ)) i⟫_ℂ := by
        rw [ContinuousLinearMap.star_eq_adjoint, piLpEntry_apply]
    _ = ⟪PiLp.single 2 i h, ContinuousLinearMap.adjoint T (PiLp.single 2 j ξ)⟫_ℂ := by
        rw [← inner_piLp_single_left]
    _ = ⟪T (PiLp.single 2 i h), PiLp.single 2 j ξ⟫_ℂ :=
        ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = ⟪(T (PiLp.single 2 i h)) j, ξ⟫_ℂ := inner_piLp_single_right _ _ _
    _ = ⟪T.piLpEntry j i h, ξ⟫_ℂ := by rw [piLpEntry_apply]
    _ = ⟪h, ContinuousLinearMap.adjoint (T.piLpEntry j i) ξ⟫_ℂ := by
        rw [← ContinuousLinearMap.adjoint_inner_right]
    _ = ⟪h, star (T.piLpEntry j i) ξ⟫_ℂ := by rw [← ContinuousLinearMap.star_eq_adjoint]

/-- Operators on two copies of `H` whose four corners lie in `A`. -/
private def matrixTwo (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)) :
    NonUnitalStarSubalgebra ℂ (twoCopy →L[ℂ] twoCopy) where
  carrier := {T | ∀ i j, T.piLpEntry i j ∈ A}
  zero_mem' := by
    intro i j
    simp
  add_mem' {S T} hS hT := by
    intro i j
    rw [piLpEntry_add]
    exact add_mem (hS i j) (hT i j)
  mul_mem' {S T} hS hT := by
    intro i k
    rw [piLpEntry_mul, Fin.sum_univ_two]
    exact add_mem (mul_mem (hS i 0) (hT 0 k)) (mul_mem (hS i 1) (hT 1 k))
  smul_mem' c _ hT := by
    intro i j
    rw [piLpEntry_smul]
    exact SMulMemClass.smul_mem c (hT i j)
  star_mem' {T} hT := by
    intro i j
    rw [piLpEntry_star]
    exact star_mem (hT j i)

/-- Membership in `matrixTwo` is membership of every matrix entry. -/
@[simp] private theorem mem_matrixTwo_iff (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    {T : twoCopy →L[ℂ] twoCopy} : T ∈ matrixTwo A ↔ ∀ i j, T.piLpEntry i j ∈ A :=
  Iff.rfl

/-- Each corner of an element of `A` lies in `matrixTwo A`. -/
private theorem corner_mem_matrixTwo (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    {a : H →L[ℂ] H} (ha : a ∈ A) (i j : Fin 2) : corner i j a ∈ matrixTwo A := by
  intro p q
  rw [piLpEntry_corner]
  split_ifs with hpq
  · exact ha
  · exact zero_mem _

/-- Right multiplication by every element of a nondegenerate algebra forces the factor to vanish.
-/
private theorem eq_zero_of_mul_right {A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)}
    (hd : Dense (Submodule.span ℂ {x : H | ∃ a ∈ A, ∃ y : H, a y = x} : Set H))
    {X : H →L[ℂ] H} (hX : ∀ a ∈ A, X * a = 0) : X = 0 := by
  apply ContinuousLinearMap.ext_on hd
  intro x hx
  obtain ⟨a, ha, y, rfl⟩ := hx
  simpa [mul_apply_eq_comp] using congr_fun (congrArg DFunLike.coe (hX a ha)) y

/-- Left multiplication by every element of a nondegenerate algebra forces the factor to vanish. -/
private theorem eq_zero_of_mul_left {A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H)}
    (hd : Dense (Submodule.span ℂ {x : H | ∃ a ∈ A, ∃ y : H, a y = x} : Set H))
    {X : H →L[ℂ] H} (hX : ∀ a ∈ A, a * X = 0) : X = 0 := by
  have hstar : star X = 0 := eq_zero_of_mul_right hd fun a ha => by
    simpa [star_mul, star_star, star_zero] using congrArg star (hX (star a) (star_mem ha))
  simpa [star_star] using congrArg star hstar

/-- Entries of `corner i j a * R` are `a` times row `j` of `R`, in row `i`. -/
private theorem piLpEntry_corner_mul (R : twoCopy →L[ℂ] twoCopy) (a : H →L[ℂ] H)
    (i j p k : Fin 2) : (corner i j a * R).piLpEntry p k =
      if p = i then a * R.piLpEntry j k else 0 := by
  ext h
  rw [piLpEntry_apply, mul_apply_eq_comp, corner_apply]
  by_cases hp : p = i
  · subst hp
    rw [PiLp.single_eq_same, ← piLpEntry_apply, ite_eq_left rfl, mul_apply_eq_comp]
  · rw [PiLp.single_eq_of_ne 2 hp, ite_eq_right hp, zero_apply]

/-- Entries of `R * corner i j a` are column `i` of `R` times `a`, in column `j`. -/
private theorem piLpEntry_mul_corner (R : twoCopy →L[ℂ] twoCopy) (a : H →L[ℂ] H)
    (i j p k : Fin 2) : (R * corner i j a).piLpEntry p k =
      if k = j then R.piLpEntry p i * a else 0 := by
  ext h
  rw [piLpEntry_apply, mul_apply_eq_comp, corner_apply]
  by_cases hk : k = j
  · rw [hk]
    have hinner : (PiLp.single (β := fun _ : Fin 2 => H) 2 j h) j = h := by
      rw [PiLp.single_eq_same]
    rw [hinner, apply_eq_sum_piLpEntry]
    have hsingle : ∑ q : Fin 2, (R.piLpEntry p q)
        ((PiLp.single (β := fun _ : Fin 2 => H) 2 i (a h)) q) =
        (R.piLpEntry p i) (a h) := by
      rw [Finset.sum_eq_single i]
      · rw [PiLp.single_eq_same]
      · intro q _ hq
        rw [PiLp.single_eq_of_ne 2 hq, map_zero]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    rw [hsingle, ite_eq_left rfl, mul_apply_eq_comp]
  · rw [PiLp.single_eq_of_ne 2 (Ne.symm hk), map_zero]
    have hzero : PiLp.single (β := fun _ : Fin 2 => H) 2 i (0 : H) = 0 :=
      (PiLp.single_eq_zero_iff 2 i).mpr rfl
    rw [hzero, map_zero, PiLp.zero_apply, ite_eq_right hk, zero_apply]

section

omit [CompleteSpace H]

/-- Two operators on the Hilbert sum with the same matrix entries are equal. -/
private theorem ext_piLpEntry {S T : twoCopy →L[ℂ] twoCopy}
    (h : ∀ i j, S.piLpEntry i j = T.piLpEntry i j) : S = T := by
  ext w i
  rw [apply_eq_sum_piLpEntry, apply_eq_sum_piLpEntry]
  exact Finset.sum_congr rfl fun j _ => by rw [h]

end

/-- The commutant of `matrixTwo A` consists of the diagonal amplifications of the commutant of
`A`. Nondegeneracy kills the off-diagonal entries. -/
private theorem mem_centralizer_matrixTwo_iff (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (hd : Dense (Submodule.span ℂ {x : H | ∃ a ∈ A, ∃ y : H, a y = x} : Set H))
    (R : twoCopy →L[ℂ] twoCopy) :
    R ∈ (matrixTwo A : Set (twoCopy →L[ℂ] twoCopy)).centralizer ↔
      ∃ B : H →L[ℂ] H, B ∈ boundedOperatorCommutant (A : Set (H →L[ℂ] H)) ∧
        R = PiLp.diagStarAlgHom ℂ H (Fin 2) B := by
  constructor
  · intro hR
    rw [Set.mem_centralizer_iff] at hR
    have hent (a : H →L[ℂ] H) (ha : a ∈ A) (i j p k : Fin 2) :
        (corner i j a * R).piLpEntry p k = (R * corner i j a).piLpEntry p k :=
      congrArg (fun S => S.piLpEntry p k)
        (hR (corner i j a) (corner_mem_matrixTwo A ha i j))
    have hoff {j k : Fin 2} (hjk : j ≠ k) : R.piLpEntry j k = 0 := by
      refine eq_zero_of_mul_left hd fun a ha => ?_
      have h := hent a ha j j j k
      rw [piLpEntry_corner_mul, piLpEntry_mul_corner, ite_eq_left rfl,
        ite_eq_right (Ne.symm hjk)] at h
      exact h
    have hdiag (i : Fin 2) (a : H →L[ℂ] H) (ha : a ∈ A) :
        a * R.piLpEntry i i = R.piLpEntry i i * a := by
      have h := hent a ha i i i i
      simpa [piLpEntry_corner_mul, piLpEntry_mul_corner] using h
    have heqdiag : R.piLpEntry 1 1 = R.piLpEntry 0 0 := by
      refine eq_of_sub_eq_zero (eq_zero_of_mul_left hd fun a ha => ?_)
      have h := hent a ha 0 1 0 1
      rw [piLpEntry_corner_mul, piLpEntry_mul_corner, ite_eq_left rfl, ite_eq_left rfl] at h
      rw [← hdiag 0 a ha] at h
      rw [mul_sub, h, sub_self]
    refine ⟨R.piLpEntry 0 0, ?_, ?_⟩
    · rw [mem_boundedOperatorCommutant_iff]
      intro a ha
      exact (commute_iff_eq _ _).mpr (hdiag 0 a ha).symm
    · refine ext_piLpEntry fun i j => ?_
      rw [piLpEntry_diagStarAlgHom]
      by_cases hij : i = j
      · subst hij
        rw [ite_eq_left rfl]
        by_cases hi : i = 0
        · subst hi
          rfl
        · have hi1 : i = 1 := Fin.eq_one_of_ne_zero i hi
          subst hi1
          exact heqdiag
      · rw [ite_eq_right hij]
        exact hoff hij
  · rintro ⟨B, hB, rfl⟩
    rw [Set.mem_centralizer_iff]
    intro M hM
    ext w i
    rw [mul_apply_eq_comp, mul_apply_eq_comp, apply_eq_sum_piLpEntry,
      PiLp.diagStarAlgHom_apply, apply_eq_sum_piLpEntry, map_sum]
    simp only [PiLp.diagStarAlgHom_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hentry : M.piLpEntry i j ∈ A := hM i j
    have hcomm : M.piLpEntry i j * B = B * M.piLpEntry i j :=
      ((mem_boundedOperatorCommutant_iff.mp hB) _ hentry).eq.symm
    have happly := congr_fun (congrArg DFunLike.coe hcomm) (w j)
    rw [mul_apply_eq_comp, mul_apply_eq_comp] at happly
    exact happly

/-- The self-adjoint off-diagonal operator with corners `star T` and `T`. -/
private def offDiagonal (T : H →L[ℂ] H) : twoCopy →L[ℂ] twoCopy :=
  corner 0 1 (star T) + corner 1 0 T

/-- The off-diagonal corner operator is self-adjoint. -/
private theorem offDiagonal_isSelfAdjoint (T : H →L[ℂ] H) : IsSelfAdjoint (offDiagonal T) := by
  rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint, offDiagonal, map_add,
    ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint, star_corner,
    star_corner, star_star, add_comm]

/-- The off-diagonal corner is a contraction whenever `T` is. -/
private theorem norm_offDiagonal_le (T : H →L[ℂ] H) : ‖offDiagonal T‖ ≤ ‖T‖ := by
  refine opNorm_le_bound _ (norm_nonneg T) fun w => ?_
  have happly : offDiagonal T w =
      PiLp.single 2 0 ((star T) (w 1)) + PiLp.single 2 1 (T (w 0)) := by
    simp [offDiagonal, corner_apply]
  have h0 : (PiLp.single (β := fun _ : Fin 2 => H) 2 0 ((star T) (w 1)) +
      PiLp.single (β := fun _ : Fin 2 => H) 2 1 (T (w 0))) 0 = (star T) (w 1) := by
    simp [PiLp.add_apply, PiLp.single_eq_same, PiLp.single_eq_of_ne]
  have h1 : (PiLp.single (β := fun _ : Fin 2 => H) 2 0 ((star T) (w 1)) +
      PiLp.single (β := fun _ : Fin 2 => H) 2 1 (T (w 0))) 1 = T (w 0) := by
    simp [PiLp.add_apply, PiLp.single_eq_same, PiLp.single_eq_of_ne]
  have hsq : ‖offDiagonal T w‖ ^ 2 = ‖(star T) (w 1)‖ ^ 2 + ‖T (w 0)‖ ^ 2 := by
    rw [happly, PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => H), Fin.sum_univ_two, h0, h1]
  have h0le : ‖T (w 0)‖ ≤ ‖T‖ * ‖w 0‖ := T.le_opNorm (w 0)
  have h1le : ‖(star T) (w 1)‖ ≤ ‖T‖ * ‖w 1‖ := by
    simpa [norm_star] using (star T).le_opNorm (w 1)
  have h0sq : ‖T (w 0)‖ ^ 2 ≤ (‖T‖ * ‖w 0‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h0le
  have h1sq : ‖(star T) (w 1)‖ ^ 2 ≤ (‖T‖ * ‖w 1‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h1le
  have hw : ‖w‖ ^ 2 = ‖w 0‖ ^ 2 + ‖w 1‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => H), Fin.sum_univ_two]
  have hsqT : ‖offDiagonal T w‖ ^ 2 ≤ (‖T‖ * ‖w‖) ^ 2 := by
    rw [hsq]
    calc ‖(star T) (w 1)‖ ^ 2 + ‖T (w 0)‖ ^ 2
        ≤ (‖T‖ * ‖w 1‖) ^ 2 + (‖T‖ * ‖w 0‖) ^ 2 := add_le_add h1sq h0sq
      _ = ‖T‖ ^ 2 * (‖w 0‖ ^ 2 + ‖w 1‖ ^ 2) := by ring
      _ = ‖T‖ ^ 2 * ‖w‖ ^ 2 := by rw [hw]
      _ = (‖T‖ * ‖w‖) ^ 2 := by ring
  exact le_of_sq_le_sq hsqT (mul_nonneg (norm_nonneg T) (norm_nonneg w))

/-- The commutant of a star-closed set of operators is star-closed. -/
private theorem star_mem_boundedOperatorCommutant {S : Set (H →L[ℂ] H)}
    (hS : ∀ a ∈ S, star a ∈ S) {b : H →L[ℂ] H} (hb : b ∈ boundedOperatorCommutant S) :
    star b ∈ boundedOperatorCommutant S := by
  rw [mem_boundedOperatorCommutant_iff] at hb ⊢
  intro a ha
  have h := congrArg star ((hb (star a) (hS a ha)).eq)
  simp only [star_mul, star_star] at h
  exact (commute_iff_eq _ _).mpr h.symm

/-- The off-diagonal corner of an element of the bicommutant lies in the bicommutant of the
amplified algebra. -/
private theorem offDiagonal_mem_bicommutant (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (hd : Dense (Submodule.span ℂ {x : H | ∃ a ∈ A, ∃ y : H, a y = x} : Set H))
    {T : H →L[ℂ] H} (hT : T ∈ boundedOperatorCommutant
      (boundedOperatorCommutant (A : Set (H →L[ℂ] H)))) :
    offDiagonal T ∈ boundedOperatorCommutant
      (boundedOperatorCommutant (matrixTwo A : Set (twoCopy →L[ℂ] twoCopy))) := by
  rw [mem_boundedOperatorCommutant_iff]
  intro R hR
  obtain ⟨B, hB, rfl⟩ := (mem_centralizer_matrixTwo_iff A hd R).mp hR
  have hTB : Commute T B := (mem_boundedOperatorCommutant_iff.mp hT) B hB
  have hstarB : star B ∈ boundedOperatorCommutant (A : Set _) :=
    star_mem_boundedOperatorCommutant (fun a ha => star_mem ha) hB
  have hTstarB : Commute T (star B) :=
    (mem_boundedOperatorCommutant_iff.mp hT) (star B) hstarB
  have hstarTB : Commute (star T) B := by
    have h := congrArg star hTstarB.eq
    simp only [star_mul, star_star] at h
    exact (commute_iff_eq _ _).mpr h.symm
  apply (commute_iff_eq _ _).mpr
  ext w
  have hL : (offDiagonal T * PiLp.diagStarAlgHom ℂ H (Fin 2) B) w =
      PiLp.single 2 0 ((star T) (B (w 1))) + PiLp.single 2 1 (T (B (w 0))) := by
    simp [offDiagonal, corner_apply, mul_apply_eq_comp, PiLp.diagStarAlgHom_apply]
  have hR : (PiLp.diagStarAlgHom ℂ H (Fin 2) B * offDiagonal T) w =
      PiLp.single 2 0 (B ((star T) (w 1))) + PiLp.single 2 1 (B (T (w 0))) := by
    have hw : offDiagonal T w =
        PiLp.single 2 0 ((star T) (w 1)) + PiLp.single 2 1 (T (w 0)) := by
      simp [offDiagonal, corner_apply]
    rw [mul_apply_eq_comp, hw, map_add, PiLp.diagStarAlgHom_apply_single,
      PiLp.diagStarAlgHom_apply_single]
  have h0 : T (B (w 0)) = B (T (w 0)) := by
    simpa [mul_apply_eq_comp] using congr_fun (congrArg DFunLike.coe hTB.eq) (w 0)
  have h1 : (star T) (B (w 1)) = B ((star T) (w 1)) := by
    simpa [mul_apply_eq_comp] using congr_fun (congrArg DFunLike.coe hstarTB.eq) (w 1)
  rw [hL, hR, h0, h1]

/-- The inclusion of one summand of the Hilbert sum, as a bounded operator. -/
private def singleCLM (i : Fin 2) : H →L[ℂ] twoCopy :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => H)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℂ (fun _ : Fin 2 => H) i

section

omit [CompleteSpace H]

/-- `singleCLM` agrees with `PiLp.single`. -/
@[simp] private theorem singleCLM_apply (i : Fin 2) (h : H) :
    singleCLM i h = PiLp.single (β := fun _ : Fin 2 => H) 2 i h := rfl

end

/-- Images of the action span under inclusion of a summand lie in the action span of
`matrixTwo`. -/
private theorem singleCLM_mem_span_matrixTwo (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (i : Fin 2) {z : H}
    (hz : z ∈ Submodule.span ℂ {x : H | ∃ a ∈ A, ∃ y : H, a y = x}) :
    singleCLM i z ∈ Submodule.span ℂ
      {x : twoCopy | ∃ m ∈ matrixTwo A, ∃ y : twoCopy, m y = x} := by
  refine Submodule.span_induction ?mem ?zero ?add ?smul hz
  · intro x hx
    obtain ⟨a, ha, y, rfl⟩ := hx
    apply Submodule.subset_span
    exact ⟨corner i i a, corner_mem_matrixTwo A ha i i, singleCLM i y,
      by simp [corner_apply, singleCLM_apply]⟩
  · have h0 : singleCLM i (0 : H) = 0 := by
      simp [singleCLM_apply, PiLp.single_eq_zero_iff]
    rw [h0]
    exact Submodule.zero_mem _
  · intro y z _ _ hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz
  · intro c y _ hy
    rw [map_smul]
    exact Submodule.smul_mem _ c hy

/-- Nondegeneracy of `A` implies nondegeneracy of its amplification `matrixTwo A`. -/
private theorem matrixTwo_nondegenerate (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (hd : Dense (Submodule.span ℂ {x : H | ∃ a ∈ A, ∃ y : H, a y = x} : Set H)) :
    Dense (Submodule.span ℂ
      {x : twoCopy | ∃ m ∈ matrixTwo A, ∃ y : twoCopy, m y = x} : Set twoCopy) := by
  rw [Metric.dense_iff]
  intro w ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hw0 : w 0 ∈ closure
      (Submodule.span ℂ {x : H | ∃ a ∈ A, ∃ y : H, a y = x} : Set H) := by
    rw [hd.closure_eq]
    exact Set.mem_univ _
  have hw1 : w 1 ∈ closure
      (Submodule.span ℂ {x : H | ∃ a ∈ A, ∃ y : H, a y = x} : Set H) := by
    rw [hd.closure_eq]
    exact Set.mem_univ _
  obtain ⟨z0, hz0, hdz0⟩ := Metric.mem_closure_iff.mp hw0 (ε / 2) hε2
  obtain ⟨z1, hz1, hdz1⟩ := Metric.mem_closure_iff.mp hw1 (ε / 2) hε2
  rw [dist_eq_norm] at hdz0 hdz1
  let z : twoCopy := singleCLM 0 z0 + singleCLM 1 z1
  have hzcomp0 : z 0 = z0 := by
    simp [z, singleCLM_apply]
  have hzcomp1 : z 1 = z1 := by
    simp [z, singleCLM_apply]
  have hsq : ‖w - z‖ ^ 2 = ‖w 0 - z0‖ ^ 2 + ‖w 1 - z1‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => H), Fin.sum_univ_two, PiLp.sub_apply,
      PiLp.sub_apply, hzcomp0, hzcomp1]
  have h0sq : ‖w 0 - z0‖ ^ 2 < (ε / 2) ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg _) hε2.le).mpr hdz0
  have h1sq : ‖w 1 - z1‖ ^ 2 < (ε / 2) ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg _) hε2.le).mpr hdz1
  have hquad : (ε / 2) ^ 2 + (ε / 2) ^ 2 < ε ^ 2 := by
    nlinarith [hε]
  have hlt : ‖w - z‖ ^ 2 < ε ^ 2 := by
    rw [hsq]
    exact (add_lt_add h0sq h1sq).trans hquad
  refine ⟨z, Set.mem_inter ?_ ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
    exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hlt
  · exact Submodule.add_mem _ (singleCLM_mem_span_matrixTwo A 0 hz0)
      (singleCLM_mem_span_matrixTwo A 1 hz1)

section

omit [CompleteSpace H]

/-- A matrix entry of an operator is bounded by the operator norm. -/
private theorem norm_piLpEntry_le {M : twoCopy →L[ℂ] twoCopy} {C : ℝ} (hC : 0 ≤ C)
    (hM : ‖M‖ ≤ C) (i j : Fin 2) : ‖M.piLpEntry i j‖ ≤ C := by
  refine opNorm_le_bound (M.piLpEntry i j) hC fun y => ?_
  let s : twoCopy := PiLp.single (β := fun _ : Fin 2 => H) 2 j y
  have happly : M.piLpEntry i j y = (M s) i := by
    rw [piLpEntry_apply]
  rw [happly]
  have hcomp : ‖(M s) i‖ ≤ ‖M s‖ := PiLp.norm_apply_le _ _
  have hop : ‖M s‖ ≤ ‖M‖ * ‖s‖ := M.le_opNorm s
  have hnorm : ‖s‖ = ‖y‖ :=
    PiLp.norm_single (p := 2) (β := fun _ : Fin 2 => H) j y
  have hscale : ‖M‖ * ‖s‖ ≤ C * ‖y‖ := by
    rw [hnorm]
    exact mul_le_mul_of_nonneg_right hM (norm_nonneg _)
  exact hcomp.trans (hop.trans hscale)

end

/-- **23.22**, Kaplansky density for a possibly nonunital, nondegenerately represented
star algebra of operators; norm closedness is not needed. Nondegeneracy is stated by density
of the linear action span. -/
theorem kaplansky_density (A : NonUnitalStarSubalgebra ℂ (H →L[ℂ] H))
    (hd : Dense (Submodule.span ℂ {x : H | ∃ a ∈ A, ∃ y : H, a y = x} : Set H))
    (T : H →L[ℂ] H) (hT : T ∈ boundedOperatorCommutant
      (boundedOperatorCommutant (A : Set (H →L[ℂ] H)))) (hbound : ‖T‖ ≤ 1) :
    IsStrongOperatorApproximable {a | a ∈ A ∧ ‖a‖ ≤ 1} T := by
  intro n x ε hε
  have hnorm : ‖offDiagonal T‖ ≤ 1 := (norm_offDiagonal_le T).trans hbound
  have hmem : offDiagonal T ∈ boundedOperatorCommutant
      (boundedOperatorCommutant (matrixTwo A : Set _)) :=
    offDiagonal_mem_bicommutant A hd hT
  obtain ⟨M, hM, hclose⟩ := kaplansky_density_selfAdjoint (H := twoCopy) (matrixTwo A)
    (matrixTwo_nondegenerate A hd) (offDiagonal T) hmem hnorm (offDiagonal_isSelfAdjoint T) n
    (fun i => PiLp.single 2 0 (x i)) ε hε
  obtain ⟨hMA, hMnorm, -⟩ := hM
  refine ⟨M.piLpEntry 1 0, ⟨hMA 1 0, norm_piLpEntry_le zero_le_one hMnorm 1 0⟩, fun i => ?_⟩
  have heq : ((M - offDiagonal T) (PiLp.single 2 0 (x i))) 1 =
      (M.piLpEntry 1 0 - T) (x i) := by
    rw [sub_apply, PiLp.sub_apply]
    have hS : offDiagonal T (PiLp.single (β := fun _ : Fin 2 => H) 2 0 (x i)) =
        PiLp.single (β := fun _ : Fin 2 => H) 2 1 (T (x i)) := by
      simp [offDiagonal, corner_apply, map_zero, PiLp.single_eq_same, PiLp.single_eq_of_ne]
    rw [hS, PiLp.single_eq_same, ← piLpEntry_apply, ← sub_apply]
  have hle : ‖((M - offDiagonal T) (PiLp.single 2 0 (x i))) 1‖ < ε :=
    (PiLp.norm_apply_le _ _).trans_lt (hclose i)
  rw [← heq]
  exact hle


end CKMA
