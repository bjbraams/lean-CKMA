/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Topology.ContinuousMap.Units
import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
import TauCeti.Analysis.Complex.InfiniteProd
import TauCeti.Analysis.Complex.MittagLeffler
import TauCeti.Analysis.Complex.Pompeiu.Discretization

/-!
# Plane approximation and prescribed analytic data

Discrete subsets of plane sets, in the sense of Mathlib's `codiscreteWithin`, support the
prescribed-singularity and prescribed-divisor theorems. Great Picard describes essential
singularities.
Runge approximation permits specified poles in bounded complementary components;
Mergelyan approximation permits compact sets with empty interior. Mittag–Leffler
principal parts and positive zero divisors are realized by meromorphic and holomorphic
functions, respectively.

Sources: GAPS 40.29 and 40.60–40.64.

The Runge proof uses TauCeti's discretization of the Cauchy–Pompeiu formula. It adapts the
closed-subalgebra argument of TauCeti's `Runge.SimpleFraction` to rational restrictions with
the prescribed poles, using Mathlib's spectral lemmas about complementary components.

## Main definitions

* `CKMA.IsLocallyFiniteIn`: relative local finiteness on compact subsets, equivalent on open sets
  to `Aᶜ ∈ codiscreteWithin Ω`.
* `CKMA.HasEssentialSingularityAt`: isolated essential singularity.
* `CKMA.MeetsBoundedComplementaryComponents`: pole set condition for Runge's theorem.
* `CKMA.finitePrincipalPart`: polynomial in `(z - a)⁻¹`.

## Main results

* `CKMA.IsLocallyFiniteIn.mono`, `CKMA.isLocallyFiniteIn_of_finite`: basic properties of relative
  local finiteness.
* `CKMA.IsLocallyFiniteIn.countable`: countability of a locally finite set in an open domain.
* `CKMA.isLocallyFiniteIn_iff_compl_mem_codiscreteWithin`: the comparison with Mathlib's
  `codiscreteWithin` on open sets.
* `CKMA.great_picard`: Great Picard theorem for essential singularities.
* `CKMA.runge_approximation`: Runge's rational approximation theorem.
* `CKMA.mergelyan_approximation`: Mergelyan's polynomial approximation theorem.
* `CKMA.exists_mittagLeffler`: Mittag–Leffler theorem on prescribed principal parts.
* `CKMA.exists_holomorphic_prescribed_zeros`: Weierstrass theorem on prescribed zeros.

The Mittag–Leffler theorem is the polynomial case of TauCeti's
`TauCeti.exists_meromorphic_prescribed_principal_parts`. The prescribed-zero
proof uses TauCeti's elementary Weierstrass factors and locally uniform infinite-product theorems.
-/

public section

noncomputable section

namespace CKMA

open Filter Topology Polynomial
open scoped BigOperators

/-- Local finiteness relative to an open set, formulated on all compact subsets. -/
@[expose]
def IsLocallyFiniteIn (s Ω : Set ℂ) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → (s ∩ K).Finite

/-- Local finiteness asks for finitely many points in every compact subset of `Ω`. -/
theorem isLocallyFiniteIn_iff {s Ω : Set ℂ} :
    IsLocallyFiniteIn s Ω ↔ ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → (s ∩ K).Finite :=
  Iff.rfl

/-- On an open set, local finiteness of `A` is Mathlib's `Aᶜ ∈ codiscreteWithin Ω`. -/
theorem isLocallyFiniteIn_iff_compl_mem_codiscreteWithin {A Ω : Set ℂ} (hΩ : IsOpen Ω) :
    IsLocallyFiniteIn A Ω ↔ Aᶜ ∈ codiscreteWithin Ω := by
  rw [codiscreteWithin_iff_locallyFiniteComplementWithin]
  constructor
  · intro hA z hz
    obtain ⟨K, hK, hzK, hKΩ⟩ := exists_compact_subset hΩ hz
    refine ⟨K, mem_interior_iff_mem_nhds.mp hzK, (hA K hK hKΩ).subset ?_⟩
    exact fun _ hz' ↦ ⟨by simpa only [Set.mem_compl_iff, not_not] using hz'.2.2, hz'.1⟩
  · intro hA K hK hKΩ
    choose U hU hfin using fun z (hz : z ∈ K) ↦ hA z (hKΩ hz)
    obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' U hU
    refine (t.finite_toSet.biUnion fun z _ ↦ hfin z z.2).subset ?_
    rintro x ⟨hxA, hxK⟩
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (ht hxK)
    exact Set.mem_iUnion₂.mpr ⟨z, hz, hxz, hKΩ hxK, not_not.mpr hxA⟩

/-- Restricting a locally finite set preserves local finiteness. -/
theorem IsLocallyFiniteIn.mono {s t Ω : Set ℂ} (hs : IsLocallyFiniteIn s Ω) (ht : t ⊆ s) :
    IsLocallyFiniteIn t Ω := by
  intro K hK hKΩ
  exact (hs K hK hKΩ).subset (Set.inter_subset_inter_left K ht)

/-- Finite sets are locally finite in any plane region. -/
theorem isLocallyFiniteIn_of_finite {s Ω : Set ℂ} (hs : s.Finite) :
    IsLocallyFiniteIn s Ω := by
  intro K hK hKΩ
  exact hs.inter_of_left K

/-- A locally finite subset of an open plane set is countable. -/
theorem IsLocallyFiniteIn.countable {A Ω : Set ℂ} (hA : IsLocallyFiniteIn A Ω)
    (hΩ : IsOpen Ω) (hAΩ : A ⊆ Ω) : A.Countable := by
  let : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  let K (n : ℕ) : Set ℂ := Subtype.val '' compactCovering Ω n
  have hKΩ (n : ℕ) : K n ⊆ Ω := fun _ ⟨z, _, hz⟩ ↦ hz ▸ z.property
  have hcover : A ⊆ ⋃ n : ℕ, A ∩ K n := by
    intro z hz
    have h : (⟨z, hAΩ hz⟩ : Ω) ∈ ⋃ n, compactCovering Ω n := by
      rw [iUnion_compactCovering]
      exact Set.mem_univ _
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    exact Set.mem_iUnion.mpr ⟨n, hz, ⟨⟨z, hAΩ hz⟩, hn, rfl⟩⟩
  exact (Set.countable_iUnion fun n ↦
    (hA _ ((isCompact_compactCovering Ω n).image continuous_subtype_val) (hKΩ n)).countable).mono
    hcover

/-- An essential isolated singularity, with the function holomorphic on its punctured disk. -/
@[expose]
def HasEssentialSingularityAt (f : ℂ → ℂ) (a : ℂ) (R : ℝ) : Prop :=
  0 < R ∧ DifferentiableOn ℂ f {z | 0 < ‖z - a‖ ∧ ‖z - a‖ < R} ∧ ¬ MeromorphicAt f a

/-- An essential singularity: holomorphy on the punctured disk and no meromorphic germ. -/
theorem hasEssentialSingularityAt_iff {f : ℂ → ℂ} {a : ℂ} {R : ℝ} :
    HasEssentialSingularityAt f a R ↔
      0 < R ∧ DifferentiableOn ℂ f {z | 0 < ‖z - a‖ ∧ ‖z - a‖ < R} ∧ ¬ MeromorphicAt f a :=
  Iff.rfl

/-- **40.29**, holomorphic Great Picard: all but at most one finite value have infinitely
many preimages in every punctured neighborhood. Stated for holomorphic `f`; the meromorphic
version with two exceptional values is not covered. -/
theorem great_picard {f : ℂ → ℂ} {a : ℂ} {R : ℝ}
    (hf : HasEssentialSingularityAt f a R) :
    ∃ exceptional : ℂ, ∀ w : ℂ, w ≠ exceptional → ∀ r : ℝ, 0 < r → r < R →
      {z : ℂ | 0 < ‖z - a‖ ∧ ‖z - a‖ < r ∧ f z = w}.Infinite := by
  sorry

/-- Prescribed finite poles meet every bounded complementary component; the polynomial part
is allowed, which is the same as permitting a pole at infinity. -/
@[expose]
def MeetsBoundedComplementaryComponents (P K : Set ℂ) : Prop :=
  P ⊆ Kᶜ ∧ ∀ z ∈ Kᶜ, Bornology.IsBounded (connectedComponentIn Kᶜ z) →
    (P ∩ connectedComponentIn Kᶜ z).Nonempty

/-- The pole set lies off `K` and meets every bounded component of `Kᶜ`. -/
theorem meetsBoundedComplementaryComponents_iff {P K : Set ℂ} :
    MeetsBoundedComplementaryComponents P K ↔ P ⊆ Kᶜ ∧ ∀ z ∈ Kᶜ,
      Bornology.IsBounded (connectedComponentIn Kᶜ z) →
        (P ∩ connectedComponentIn Kᶜ z).Nonempty :=
  Iff.rfl

/-- **40.60**: Runge approximation when infinity is an allowed pole.
Every zero of the approximant's denominator lies in the prescribed finite-pole set. -/
theorem runge_approximation {K U P : Set ℂ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hP : MeetsBoundedComplementaryComponents P K)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ (∀ z : ℂ, q.eval z = 0 → z ∈ P) ∧
      ∀ z ∈ K, q.eval z ≠ 0 ∧ ‖f z - p.eval z / q.eval z‖ < ε := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, 1, one_ne_zero, by simp, by simp⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hqK (q : ℂ[X]) (hq : ∀ z, q.eval z = 0 → z ∈ P) (z : K) : q.eval (z : ℂ) ≠ 0 :=
    fun hz ↦ hP.1 (hq z hz) z.property
  let R : Subalgebra ℂ C(K, ℂ) :=
    { carrier := {g | ∃ p q : ℂ[X], (∀ z, q.eval z = 0 → z ∈ P) ∧
          ∀ z : K, g z = p.eval (z : ℂ) / q.eval (z : ℂ)}
      algebraMap_mem' c := ⟨C c, 1, by simp, by simp⟩
      zero_mem' := ⟨0, 1, by simp, by simp⟩
      one_mem' := ⟨1, 1, by simp, by simp⟩
      add_mem' := by
        rintro g h ⟨p, q, hq, hg⟩ ⟨r, s, hs, hh⟩
        refine ⟨p * s + q * r, q * s, fun z hz ↦ ?_, fun z ↦ ?_⟩
        · rcases mul_eq_zero.mp (by simpa only [eval_mul] using hz) with hz | hz
          · exact hq z hz
          · exact hs z hz
        · rw [ContinuousMap.add_apply, hg, hh, div_add_div _ _ (hqK q hq z) (hqK s hs z)]
          simp only [eval_add, eval_mul]
      mul_mem' := by
        rintro g h ⟨p, q, hq, hg⟩ ⟨r, s, hs, hh⟩
        refine ⟨p * r, q * s, fun z hz ↦ ?_, fun z ↦ ?_⟩
        · rcases mul_eq_zero.mp (by simpa only [eval_mul] using hz) with hz | hz
          · exact hq z hz
          · exact hs z hz
        · rw [ContinuousMap.mul_apply, hg, hh, div_mul_div_comm]
          simp only [eval_mul] }
  let S := R.topologicalClosure
  let : IsClosed (S : Set C(K, ℂ)) := R.isClosed_topologicalClosure
  let x : S := ⟨⟨Subtype.val, continuous_subtype_val⟩,
    R.le_topologicalClosure ⟨X, 1, by simp, by simp⟩⟩
  have hxval (z : K) : (x : C(K, ℂ)) z = (z : ℂ) := rfl
  have hx : spectrum ℂ (x : C(K, ℂ)) = K := by
    rw [ContinuousMap.spectrum_eq_range]
    exact Subtype.range_coe
  let pole (a : ℂ) (ha : a ∉ K) : C(K, ℂ) :=
    ⟨fun z ↦ ((z : ℂ) - a)⁻¹, (continuous_subtype_val.sub continuous_const).inv₀ fun z ↦
      sub_ne_zero.mpr fun hz ↦ ha (by simpa only [← hz] using z.property)⟩
  have hspecP (b : ℂ) (hb : b ∈ P) : b ∉ spectrum ℂ x := by
    have hbK : b ∉ K := hP.1 hb
    have hpole : -pole b hbK ∈ R := by
      refine ⟨C (-1), X - C b, fun z hz ↦ ?_, fun z ↦ ?_⟩
      · have hz' : z - b = 0 := by simpa only [eval_sub, eval_X, eval_C] using hz
        exact sub_eq_zero.mp hz' ▸ hb
      · simp [pole, neg_div]
    rw [spectrum.notMem_iff, isUnit_iff_exists_inv]
    refine ⟨⟨_, R.le_topologicalClosure hpole⟩, ?_⟩
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    simp only [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one,
      Subalgebra.coe_algebraMap, ContinuousMap.mul_apply, ContinuousMap.sub_apply,
      ContinuousMap.one_apply, _root_.algebraMap_apply, smul_eq_mul, mul_one, hxval,
      ContinuousMap.neg_apply, pole, ContinuousMap.coe_mk]
    rw [← neg_sub, neg_mul_neg]
    exact mul_inv_cancel₀ (sub_ne_zero.mpr fun hz ↦ hbK (by simpa only [← hz] using z.property))
  -- An extra spectral point would put its whole bounded complementary component in the spectrum.
  have hspec (a : ℂ) (ha : a ∉ K) : a ∉ spectrum ℂ x := by
    intro haspec
    have hbounded := Subalgebra.spectrum_isBounded_connectedComponentIn S x haspec
    rw [hx] at hbounded
    obtain ⟨b, hbP, hbComp⟩ := hP.2 a ha hbounded
    apply hspecP b hbP
    rw [Subalgebra.spectrum_sUnion_connectedComponentIn S x]
    exact Or.inr <| Set.mem_biUnion ⟨haspec, by rwa [hx]⟩ <| by rwa [hx]
  have hpoleS (a : ℂ) (ha : a ∉ K) : pole a ha ∈ S := by
    have hu : IsUnit (x - algebraMap ℂ S a) := by
      have h := (spectrum.notMem_iff.mp (hspec a ha)).neg
      simpa only [neg_sub] using h
    let v : S := ↑hu.unit⁻¹
    suffices (v : C(K, ℂ)) = pole a ha by
      rw [← this]
      exact v.property
    apply ContinuousMap.ext
    intro z
    apply eq_inv_of_mul_eq_one_left
    have h := congrArg (fun g : S ↦ (g : C(K, ℂ)) z) hu.unit.inv_mul
    simpa only [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one,
      Subalgebra.coe_algebraMap, ContinuousMap.mul_apply, ContinuousMap.sub_apply,
      ContinuousMap.one_apply, _root_.algebraMap_apply, smul_eq_mul, mul_one, IsUnit.unit_spec,
      hxval] using h
  let target : C(K, ℂ) :=
    ⟨f ∘ Subtype.val, continuousOn_iff_continuous_domRestrict.mp (hf.continuousOn.mono hKU)⟩
  obtain ⟨V, hV, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨M₀, hM₀⟩ := hVc.bddAbove_image (hf.continuousOn.mono hVU).norm
  let M := max M₀ 1
  have hM : 0 < M := zero_lt_one.trans_le (le_max_right _ _)
  have hbound (z : ℂ) (hz : z ∈ V) : ‖f z‖ ≤ M :=
    (hM₀ ⟨z, subset_closure hz, rfl⟩).trans (le_max_left _ _)
  have htarget : target ∈ S := by
    have hS_eq : closure (S : Set C(K, ℂ)) = S := R.isClosed_topologicalClosure.closure_eq
    suffices target ∈ closure (S : Set C(K, ℂ)) by rwa [hS_eq] at this
    refine Metric.mem_closure_iff.mpr fun δ hδ ↦ ?_
    obtain ⟨N, ζ, c, hζ, happ⟩ :=
      hK.exists_norm_sub_sum_mul_sub_inv_smul_le hV hKV
        (ε := δ / 2 / M) (div_pos (half_pos hδ) hM)
    let g : C(K, ℂ) := ∑ j : Fin N, (c j * f (ζ j)) • pole (ζ j) (hζ j).2
    have hg : g ∈ S :=
      S.sum_mem fun j _ ↦ S.smul_mem (hpoleS (ζ j) (hζ j).2) _
    refine ⟨g, hg, ?_⟩
    rw [dist_eq_norm]
    refine ((ContinuousMap.norm_le (target - g) (half_pos hδ).le).2 fun z ↦ ?_).trans_lt
      (half_lt_self hδ)
    have hz := happ f M (hf.mono (subset_closure.trans hVU)) hbound z z.property
    rw [div_mul_cancel₀ _ hM.ne'] at hz
    convert hz using 2
    simp only [target, g, ContinuousMap.sub_apply, ContinuousMap.coe_mk,
      ContinuousMap.sum_apply, ContinuousMap.smul_apply, pole, smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  obtain ⟨g, ⟨p, q, hq, hvalues⟩, hdist⟩ := Metric.mem_closure_iff.mp htarget ε hε
  have hqne : q ≠ 0 := by
    obtain ⟨z, hz⟩ := hKne
    exact fun he ↦ hqK q hq ⟨z, hz⟩ (by simp [he])
  refine ⟨p, q, hqne, hq, fun z hz ↦ ⟨hqK q hq ⟨z, hz⟩, ?_⟩⟩
  rw [← hvalues ⟨z, hz⟩]
  exact ((target - g).norm_coe_le_norm ⟨z, hz⟩).trans_lt
    (by simpa only [dist_eq_norm] using hdist)

/-- **40.62**: Mergelyan approximation, including compact sets with empty interior. -/
theorem mergelyan_approximation {K : Set ℂ} (hK : IsCompact K)
    (hconn : IsPreconnected Kᶜ) {f : ℂ → ℂ} (hc : ContinuousOn f K)
    (hf : DifferentiableOn ℂ f (interior K)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  sorry

/-- A finite principal part centered at a point, polynomial in the reciprocal coordinate.
A constant term is allowed; it is analytic at the center. -/
@[expose]
def finitePrincipalPart (a : ℂ) (p : ℂ[X]) (z : ℂ) : ℂ := p.eval ((z - a)⁻¹)

/-- The principal part evaluates `p` at `(z - a)⁻¹`. -/
theorem finitePrincipalPart_def (a : ℂ) (p : ℂ[X]) (z : ℂ) :
    finitePrincipalPart a p z = p.eval ((z - a)⁻¹) :=
  rfl

/-- **40.63**: arbitrary principal parts on a discrete subset of a plane set are realized by one
meromorphic function; neither openness nor connectedness is needed. Equality to the principal
part is modulo an analytic germ. -/
theorem exists_mittagLeffler {Ω A : Set ℂ} (hAΩ : A ⊆ Ω) (hA : Aᶜ ∈ codiscreteWithin Ω)
    (p : A → ℂ[X]) :
    ∃ f : ℂ → ℂ, MeromorphicOn f Ω ∧ DifferentiableOn ℂ f (Ω \ A) ∧
      ∀ a : A, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a.1 ∧
        ∀ᶠ z in 𝓝[≠] a.1, f z - finitePrincipalPart a.1 (p a) z = g z := by
  obtain ⟨f, hf, hsing, hdiff⟩ := TauCeti.exists_meromorphic_prescribed_principal_parts hAΩ hA
    (fun a ↦ finitePrincipalPart a.1 (p a)) fun a ↦ (p a).meromorphicAt_eval_inv_sub a.1
  exact ⟨f, hf, hdiff, hsing⟩

/-- The distance to the complement used for the plane canonical product, with a positive
constant for the whole plane. -/
private def zeroFactorBoundaryDistance (Ω : Set ℂ) : ℂ → ℝ := by
  classical
  exact if Ωᶜ.Nonempty then fun z ↦ Metric.infDist z Ωᶜ else fun _ ↦ 1

/-- The boundary distance is continuous. -/
private theorem continuous_zeroFactorBoundaryDistance (Ω : Set ℂ) :
    Continuous (zeroFactorBoundaryDistance Ω) := by
  by_cases h : Ωᶜ.Nonempty
  · simpa only [zeroFactorBoundaryDistance, ite_eq_left h] using Metric.continuous_infDist_pt Ωᶜ
  · simpa only [zeroFactorBoundaryDistance, ite_eq_right h] using
      (continuous_const (X := ℂ) (y := (1 : ℝ)))

/-- The boundary distance is positive precisely in the open set. -/
private theorem zeroFactorBoundaryDistance_pos_iff {Ω : Set ℂ} (hΩ : IsOpen Ω) {z : ℂ} :
    0 < zeroFactorBoundaryDistance Ω z ↔ z ∈ Ω := by
  by_cases h : Ωᶜ.Nonempty
  · simpa only [zeroFactorBoundaryDistance, ite_eq_left h, Set.mem_compl_iff, not_not] using
      (hΩ.isClosed_compl.notMem_iff_infDist_pos h : z ∉ Ωᶜ ↔ 0 < Metric.infDist z Ωᶜ).symm
  · have hz : z ∈ Ω := by
      by_contra hz
      exact h ⟨z, hz⟩
    simp only [zeroFactorBoundaryDistance, ite_eq_right h, zero_lt_one, hz]

/-- An affine coordinate sending its distinguished point to one. -/
private def zeroFactorAffine (a : ℂ) : ℂ → ℂ :=
  if a = 0 then fun z ↦ 1 - z else fun z ↦ z / a

/-- The affine coordinate is holomorphic. -/
private theorem differentiable_zeroFactorAffine (a : ℂ) :
    Differentiable ℂ (zeroFactorAffine a) := by
  by_cases ha : a = 0
  · simpa only [zeroFactorAffine, ite_eq_left ha] using
      (by fun_prop : Differentiable ℂ (fun z : ℂ ↦ 1 - z))
  · simpa only [zeroFactorAffine, ite_eq_right ha] using
      (differentiable_id.div_const a : Differentiable ℂ (fun z : ℂ ↦ z / a))

/-- The affine coordinate takes value one exactly at its distinguished point. -/
private theorem zeroFactorAffine_eq_one {a z : ℂ} : zeroFactorAffine a z = 1 ↔ z = a := by
  obtain rfl | ha := eq_or_ne a 0
  · simp [zeroFactorAffine, eq_comm (a := z)]
  · rw [zeroFactorAffine, ite_eq_right ha, div_eq_iff ha, one_mul]

/-- The derivative of the affine coordinate is nonzero. -/
private theorem deriv_zeroFactorAffine_ne_zero (a z : ℂ) :
    deriv (zeroFactorAffine a) z ≠ 0 := by
  by_cases ha : a = 0
  · have hd : HasDerivAt (zeroFactorAffine a) (-1) z := by
      simpa only [zeroFactorAffine, ite_eq_left ha, id_eq] using (hasDerivAt_id z).const_sub 1
    rw [hd.deriv]
    exact neg_ne_zero.mpr one_ne_zero
  · have hd : HasDerivAt (zeroFactorAffine a) (1 / a) z := by
      simpa only [zeroFactorAffine, ite_eq_right ha, id_eq] using (hasDerivAt_id z).div_const a
    rw [hd.deriv]
    exact div_ne_zero one_ne_zero ha

/-- For a fixed exterior pole a reciprocal coordinate assumes one exactly at its distinguished
point. -/
private theorem zeroFactorReciprocal_eq_one {a b z : ℂ} (hbz : z ≠ b) :
    (a - b) / (z - b) = 1 ↔ z = a := by
  rw [div_eq_iff (sub_ne_zero.mpr hbz), one_mul, sub_left_inj]
  exact eq_comm

/-- The reciprocal coordinate has nonzero derivative at its distinguished point. -/
private theorem deriv_zeroFactorReciprocal_ne_zero {a b : ℂ} (hab : a ≠ b) :
    deriv (fun z : ℂ ↦ (a - b) / (z - b)) a ≠ 0 := by
  have h := (hasDerivAt_const a (a - b)).fun_div ((hasDerivAt_id a).sub_const b)
    (sub_ne_zero.mpr hab)
  have hd : HasDerivAt (fun z : ℂ ↦ (a - b) / (z - b))
      (-(a - b) / (a - b) ^ 2) a := by
    simpa only [id_eq, zero_mul, mul_one, zero_sub] using h
  rw [hd.deriv]
  exact div_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr hab))
    (pow_ne_zero _ (sub_ne_zero.mpr hab))

/-- Points close to the finite boundary use a reciprocal coordinate. -/
private def UsesZeroFactorPole (Ω : Set ℂ) (a : ℂ) : Prop :=
  Ωᶜ.Nonempty ∧ zeroFactorBoundaryDistance Ω a ≤ (‖a‖ + 1)⁻¹

/-- The normalized coordinate about each root, with a reciprocal coordinate near the boundary. -/
private def zeroFactorCoordinate {A Ω : Set ℂ}
    (pole : (a : A) → UsesZeroFactorPole Ω a → ℂ) (a : A) : ℂ → ℂ := by
  classical
  exact if h : UsesZeroFactorPole Ω a then fun z ↦ ((a : ℂ) - pole a h) / (z - pole a h)
    else zeroFactorAffine a

/-- A locally finite set eventually leaves each bounded set of fixed positive boundary distance. -/
private theorem eventually_escapes_zeroFactorCompact {A Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hA : IsLocallyFiniteIn A Ω) (R : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ a : A in cofinite, ¬ (‖(a : ℂ)‖ ≤ R ∧ η ≤ zeroFactorBoundaryDistance Ω a) := by
  let L : Set ℂ := Metric.closedBall 0 R ∩ {z | η ≤ zeroFactorBoundaryDistance Ω z}
  have hL : IsCompact L := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const (continuous_zeroFactorBoundaryDistance Ω))
  have hLΩ : L ⊆ Ω := fun z hz ↦
    (zeroFactorBoundaryDistance_pos_iff hΩ).mp (hη.trans_le hz.2)
  let e : A ↪ ℂ := ⟨Subtype.val, Subtype.val_injective⟩
  have hfin := (hA L hL hLΩ).preimage_embedding e
  filter_upwards [hfin.compl_mem_cofinite] with a ha ha'
  have haL : (a : ℂ) ∈ L := ⟨by
    simpa only [Metric.mem_closedBall, dist_zero_right] using ha'.1, ha'.2⟩
  exact ha ⟨a.property, haL⟩

/-- Outside finitely many roots, their coordinates take values in the half disk on a fixed
compact subset of the open domain. -/
private theorem eventually_small_zeroFactorCoordinate {A Ω K : Set ℂ} (hΩ : IsOpen Ω)
    (hA : IsLocallyFiniteIn A Ω)
    (pole : (a : A) → UsesZeroFactorPole Ω a → ℂ)
    (hpole : ∀ a h, pole a h ∉ Ω ∧ ‖(a : ℂ) - pole a h‖ = zeroFactorBoundaryDistance Ω a)
    (hKΩ : K ⊆ Ω) (hK : IsCompact K) :
    ∀ᶠ a : A in cofinite, ∀ z ∈ K, ‖zeroFactorCoordinate pole a z‖ ≤ 1 / 2 := by
  let d := zeroFactorBoundaryDistance Ω
  rcases K.eq_empty_or_nonempty with rfl | hKn
  · exact Eventually.of_forall fun _ z hz ↦ False.elim hz
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKn
    (continuous_zeroFactorBoundaryDistance Ω).continuousOn
  let δ := d z₀
  have hδ : 0 < δ := (zeroFactorBoundaryDistance_pos_iff hΩ).mpr (hKΩ hz₀)
  have hdmin (z : ℂ) (hz : z ∈ K) : δ ≤ d z := hmin hz
  obtain ⟨C, hC'⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  have hC (z : ℂ) (hz : z ∈ K) : ‖z‖ ≤ C := hC' z hz
  let R := max (2 / δ) (2 * C)
  have hR : 0 ≤ R := (div_nonneg (by norm_num) hδ.le).trans (le_max_left _ _)
  let η := min (δ / 2) (R + 1)⁻¹
  have hη : 0 < η := lt_min (half_pos hδ) (inv_pos.mpr (by linarith))
  filter_upwards [eventually_escapes_zeroFactorCompact hΩ hA R hη] with a ha
  intro z hz
  by_contra! hlarge
  apply ha
  by_cases h : UsesZeroFactorPole Ω a
  · have hden : δ ≤ ‖z - pole a h‖ := (hdmin z hz).trans (by
      simpa only [d, zeroFactorBoundaryDistance, ite_eq_left h.1, dist_eq_norm] using
        Metric.infDist_le_dist_of_mem (x := z) (hpole a h).1)
    simp only [zeroFactorCoordinate, dite_eq_left h, norm_div, (hpole a h).2] at hlarge
    have hda : δ / 2 ≤ d a := by
      have hb := (lt_div_iff₀ (hδ.trans_le hden)).mp hlarge
      linarith
    have hbound := (le_div_iff₀ (by positivity : 0 < ‖(a : ℂ)‖ + 1)).mp
      (by simpa only [one_div] using hda.trans h.2 : δ / 2 ≤ 1 / (‖(a : ℂ)‖ + 1))
    refine ⟨(le_div_iff₀ hδ).mpr ?_ |>.trans (le_max_left _ _),
      (min_le_left _ _).trans hda⟩
    nlinarith
  · have hbound : ‖(a : ℂ)‖ ≤ R := by
      by_cases ha₀ : (a : ℂ) = 0
      · simpa only [ha₀, norm_zero] using hR
      · simp only [zeroFactorCoordinate, dite_eq_right h, zeroFactorAffine, ite_eq_right ha₀,
          norm_div] at hlarge
        have hb := (lt_div_iff₀ (norm_pos_iff.mpr ha₀)).mp hlarge
        exact (by linarith [hC z hz] : ‖(a : ℂ)‖ ≤ 2 * C).trans (le_max_right _ _)
    refine ⟨hbound, (min_le_right _ _).trans ?_⟩
    by_cases h' : Ωᶜ.Nonempty
    · have hd : (‖(a : ℂ)‖ + 1)⁻¹ < d a := lt_of_not_ge fun hle ↦ h ⟨h', hle⟩
      exact (inv_anti₀ (by positivity) (add_le_add_left hbound 1)).trans hd.le
    · simpa only [d, zeroFactorBoundaryDistance, ite_eq_right h'] using
        (inv_le_one_of_one_le₀ (by linarith : 1 ≤ R + 1))

/-- A locally finite family of roots has normalized holomorphic coordinates which are eventually
bounded by one half on each compact subset of the open domain. -/
private theorem exists_zeroFactorCoordinates {A Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hAΩ : A ⊆ Ω) (hA : IsLocallyFiniteIn A Ω) :
    ∃ w : A → ℂ → ℂ, (∀ a, DifferentiableOn ℂ (w a) Ω) ∧
      (∀ a z, z ∈ Ω → (w a z = 1 ↔ z = (a : ℂ))) ∧
      (∀ a, deriv (w a) a ≠ 0) ∧
      ∀ K ⊆ Ω, IsCompact K → ∀ᶠ a : A in cofinite, ∀ z ∈ K, ‖w a z‖ ≤ 1 / 2 := by
  classical
  let d := zeroFactorBoundaryDistance Ω
  have hex (a : A) (h : UsesZeroFactorPole Ω a) : ∃ b : ℂ, b ∉ Ω ∧ ‖(a : ℂ) - b‖ = d a := by
    obtain ⟨b, hb, hdb⟩ := hΩ.isClosed_compl.exists_infDist_eq_dist h.1 (a : ℂ)
    exact ⟨b, hb, by simpa only [d, zeroFactorBoundaryDistance, ite_eq_left h.1, dist_eq_norm] using
      hdb.symm⟩
  let pole (a : A) (h : UsesZeroFactorPole Ω a) : ℂ := (hex a h).choose
  have hpole (a : A) (h : UsesZeroFactorPole Ω a) : pole a h ∉ Ω ∧ ‖(a : ℂ) - pole a h‖ = d a :=
    (hex a h).choose_spec
  refine ⟨zeroFactorCoordinate pole, ?_, ?_, ?_,
    fun K hKΩ hK ↦ eventually_small_zeroFactorCoordinate hΩ hA pole hpole hKΩ hK⟩
  · intro a
    by_cases h : UsesZeroFactorPole Ω a
    · simp only [zeroFactorCoordinate, dite_eq_left h]
      intro z hz
      have hne : z ≠ pole a h := fun he ↦ (hpole a h).1 (he ▸ hz)
      have hd : DifferentiableAt ℂ (fun z : ℂ ↦ z - pole a h) z :=
        differentiableAt_id.sub_const _
      exact ((differentiableAt_const (c := (a : ℂ) - pole a h)).fun_div hd
        (sub_ne_zero.mpr hne)).differentiableWithinAt
    · simp only [zeroFactorCoordinate, dite_eq_right h]
      exact (differentiable_zeroFactorAffine a).differentiableOn
  · intro a z hz
    by_cases h : UsesZeroFactorPole Ω a
    · simp only [zeroFactorCoordinate, dite_eq_left h]
      exact zeroFactorReciprocal_eq_one fun he ↦ (hpole a h).1 (he ▸ hz)
    · simp only [zeroFactorCoordinate, dite_eq_right h]
      exact zeroFactorAffine_eq_one
  · intro a
    by_cases h : UsesZeroFactorPole Ω a
    · simp only [zeroFactorCoordinate, dite_eq_left h]
      exact deriv_zeroFactorReciprocal_ne_zero fun he ↦ (hpole a h).1 (he ▸ hAΩ a.property)
    · simp only [zeroFactorCoordinate, dite_eq_right h]
      exact deriv_zeroFactorAffine_ne_zero _ _

/-- On the half disk, increasing the genus by the multiplicity controls powers of elementary
factors by an unweighted geometric term. -/
private theorem norm_weierstrassFactor_pow_sub_one_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2)
    (n m : ℕ) : ‖Complex.weierstrassFactor (n + m) z ^ m - 1‖ ≤ (1 / 2 : ℝ) ^ n := by
  let u := Complex.weierstrassFactor (n + m) z
  have hh : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hhalf : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hu : ‖u - 1‖ ≤ (1 / 2 : ℝ) ^ (n + m) := by
    calc
      ‖u - 1‖ ≤ ‖z‖ ^ (n + m + 1) :=
        Complex.norm_weierstrassFactor_sub_one_le _ (hz.trans hhalf)
      _ ≤ (1 / 2 : ℝ) ^ (n + m + 1) := pow_le_pow_left₀ (norm_nonneg _) hz _
      _ ≤ (1 / 2 : ℝ) ^ (n + m) := pow_le_pow_of_le_one hh hhalf (by omega)
  have hu₂ : ‖u‖ ≤ 2 := by
    calc ‖u‖ = ‖u - 1 + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖u - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 := by
        rw [norm_one]
        linarith [hu.trans (pow_le_one₀ hh hhalf)]
  have hpow : ‖u ^ m - 1‖ ≤ ((2 : ℝ) ^ m - 1) * ‖u - 1‖ := by
    have hsum : (∑ i ∈ Finset.range m, (2 : ℝ) ^ i) = 2 ^ m - 1 := by
      have htwo : (2 : ℝ) - 1 = 1 := by norm_num
      simpa only [htwo, mul_one] using geom_sum_mul (2 : ℝ) m
    rw [← geom_sum_mul, norm_mul, ← hsum]
    refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans ?_) (norm_nonneg _)
    exact Finset.sum_le_sum fun i _ ↦ by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hu₂ i
  calc
    ‖u ^ m - 1‖ ≤ ((2 : ℝ) ^ m - 1) * ‖u - 1‖ := hpow
    _ ≤ (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ (n + m) := by
      exact mul_le_mul (sub_le_self _ zero_le_one) hu (norm_nonneg _) (by positivity)
    _ = (1 / 2 : ℝ) ^ n := by
      rw [pow_add, mul_left_comm, ← mul_pow]
      norm_num

/-- The elementary factor in a holomorphic coordinate has the specified order. -/
private theorem analyticOrderAt_weierstrassFactor_comp_pow {w : ℂ → ℂ} {z : ℂ}
    (hw : AnalyticAt ℂ w z) (hderiv : deriv w z ≠ 0) (hz : w z = 1) (p m : ℕ) :
    analyticOrderAt (fun v ↦ Complex.weierstrassFactor p (w v) ^ m) z = m := by
  have h := (Complex.analyticAt_weierstrassFactor p (w z)).comp hw
  have horder : analyticOrderAt (Complex.weierstrassFactor p ∘ w) z = 1 := by
    rw [analyticOrderAt_comp_of_deriv_ne_zero hw hderiv, hz,
      Complex.analyticOrderAt_weierstrassFactor_one]
  have hp : (fun v ↦ Complex.weierstrassFactor p (w v) ^ m) =
      (Complex.weierstrassFactor p ∘ w) ^ m := rfl
  rw [hp, analyticOrderAt_pow h, horder, nsmul_eq_mul, mul_one]

/-- **40.64**: every positive zero divisor on a discrete subset of an open plane set is
realized; connectedness is not needed.
Orders use Mathlib's analytic order, not a separate multiplicity convention. -/
theorem exists_holomorphic_prescribed_zeros {Ω A : Set ℂ} (hΩ : IsOpen Ω)
    (hAΩ : A ⊆ Ω) (hA' : Aᶜ ∈ codiscreteWithin Ω) (m : A → ℕ) (hm : ∀ a, 0 < m a) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Ω ∧
      (∀ z ∈ Ω, f z = 0 ↔ z ∈ A) ∧
      ∀ a : A, analyticOrderAt f a.1 = (m a : ℕ∞) := by
  classical
  have hA := (isLocallyFiniteIn_iff_compl_mem_codiscreteWithin hΩ).2 hA'
  let : Countable A := (hA.countable hΩ hAΩ).to_subtype
  obtain ⟨ι, hι⟩ := exists_injective_nat A
  obtain ⟨w, hwd, hw₁, hw', hwsmall⟩ := exists_zeroFactorCoordinates hΩ hAΩ hA
  -- The summable geometric majorant uses the injection into ℕ as part of the genus.
  let F (a : A) (z : ℂ) := Complex.weierstrassFactor (ι a + m a) (w a z) ^ m a
  let u (a : A) (z : ℂ) := F a z - 1
  have hF (a : A) : DifferentiableOn ℂ (F a) Ω :=
    ((Complex.differentiable_weierstrassFactor _).comp_differentiableOn (hwd a)).pow _
  have hud (a : A) : DifferentiableOn ℂ (u a) Ω := (hF a).sub_const 1
  have htail (K : Set ℂ) (hKΩ : K ⊆ Ω) (hK : IsCompact K) :
      SummableUniformlyOn (fun a z ↦ ‖u a z‖) K := by
    have hs : Summable fun a : A ↦ (1 / 2 : ℝ) ^ ι a :=
      (summable_geometric_of_norm_lt_one (x := (1 / 2 : ℝ)) (by norm_num)).comp_injective hι
    apply (HasSumUniformlyOn.of_norm_le_summable_eventually hs ?_).summableUniformlyOn
    filter_upwards [hwsmall K hKΩ hK] with a ha z hz
    rw [Real.norm_eq_abs, abs_norm]
    exact norm_weierstrassFactor_pow_sub_one_le (ha z hz) _ _
  let f (z : ℂ) := ∏' a : A, (1 + u a z)
  have hf := TauCeti.analyticOnNhd_tprod_one_add hΩ hud htail
  have hnorm (a : A) (z : ℂ) : 1 + u a z = F a z := by
    simp only [u, add_comm (1 : ℂ), sub_add_cancel]
  have hzero (a : A) (z : ℂ) (hz : z ∈ Ω) : F a z = 0 ↔ z = (a : ℂ) := by
    simp only [F, pow_eq_zero_iff (Nat.ne_of_gt (hm a)),
      Complex.weierstrassFactor_eq_zero_iff, hw₁ a z hz]
  refine ⟨f, hf.differentiableOn, ?_, ?_⟩
  · intro z hz
    dsimp only [f]
    rw [(htail {z} (Set.singleton_subset_iff.mpr hz) isCompact_singleton)
        |>.tprod_one_add_eq_zero_iff (Set.mem_singleton z)]
    constructor
    · rintro ⟨a, ha⟩
      exact ((hzero a z hz).mp ((hnorm a z).symm ▸ ha)) ▸ a.property
    · intro hzA
      exact ⟨⟨z, hzA⟩, (hnorm _ _).trans ((hzero _ _ hz).mpr rfl)⟩
  · intro a
    have ha : (a : ℂ) ∈ Ω := hAΩ a.property
    have horder : analyticOrderAt f a =
        ∑' b : A, analyticOrderAt (fun z ↦ 1 + u b z) a :=
      TauCeti.analyticOrderAt_tprod_one_add hΩ hud htail ha
    rw [horder, tsum_eq_single a, funext (hnorm a)]
    · exact analyticOrderAt_weierstrassFactor_comp_pow
        ((hwd a).analyticOnNhd hΩ _ ha) (hw' a) ((hw₁ a a ha).mpr rfl) _ _
    · intro b hab
      rw [funext (hnorm b)]
      exact ((hF b).analyticOnNhd hΩ _ ha).analyticOrderAt_eq_zero.mpr (fun hb ↦
        hab (Subtype.ext ((hzero b a ha).mp hb).symm))

end CKMA
