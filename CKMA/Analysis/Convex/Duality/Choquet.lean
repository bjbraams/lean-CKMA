/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.Algebra.ContinuousAffineMap
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Topology.ContinuousMap.Ordered
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Choquet representation on compact metrizable convex sets

A point of a compact metrizable convex set in a locally convex Hausdorff space is the
barycenter of a probability measure carried by the extreme points. The test maps are
continuous affine scalar functions, so the identity of the ambient space is not assumed
Bochner-integrable. A singleton is a Dirac mass. Otherwise a countable separating family
produces a continuous strictly convex series, the barycentric functional on the span of
that series and the ambient affine restrictions is dominated by the concave envelope, and
the Riesz measure of a positive extension is the representing measure.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Set
open scoped CompactlySupported

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V] [T2Space V]

/-- An affine scalar map preserves convex combinations. -/
private lemma affine_combo (a : V →ᴬ[ℝ] ℝ) {s t : ℝ} (hst : s + t = 1) (p q : V) :
    a (s • p + t • q) = s * a p + t * a q := by
  have ht : t = 1 - s := by linarith
  have hline : s • p + t • q = AffineMap.lineMap q p s := by
    rw [ht, AffineMap.lineMap_apply_module, add_comm]
  rw [hline]
  have happly :=
    AffineMap.apply_lineMap (a : V →ᵃ[ℝ] ℝ) q p s
  rw [show a (AffineMap.lineMap q p s) =
      (a : V →ᵃ[ℝ] ℝ) (AffineMap.lineMap q p s) from rfl, happly,
    AffineMap.lineMap_apply_ring, ht]
  simp only [ContinuousAffineMap.coe_toAffineMap]
  ring

/-- A singleton compact convex set is represented by the Dirac mass at its point. -/
private theorem exists_choquet_dirac (K : Set V) (_hK : IsCompact K) (_hc : Convex ℝ K)
    [TopologicalSpace.MetrizableSpace K] [MeasurableSpace K] [BorelSpace K] (x : K)
    (hsub : Subsingleton K) :
    ∃ μ : Measure K, IsProbabilityMeasure μ ∧
      μ {y : K | y.1 ∉ K.extremePoints ℝ} = 0 ∧
      ∀ a : V →ᴬ[ℝ] ℝ, (∫ y : K, a y.1 ∂μ) = a x.1 := by
  refine ⟨Measure.dirac x, inferInstance, ?_, ?_⟩
  · have hempty : {y : K | y.1 ∉ K.extremePoints ℝ} = ∅ := by
      ext y
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_not]
      rw [mem_extremePoints_iff_left]
      refine ⟨y.2, ?_⟩
      intro x1 hx1 x2 _hx2 _hseg
      exact congrArg Subtype.val
        (Subsingleton.elim (⟨x1, hx1⟩ : K) (⟨y.1, y.2⟩ : K))
    rw [hempty]
    exact measure_empty
  · intro a
    exact integral_dirac (fun y : K => a y.1) x

/-- Restriction of a continuous affine scalar map to the subtype `K`. -/
private def affRestrict {K : Set V} (a : V →ᴬ[ℝ] ℝ) : C(K, ℝ) :=
  ⟨fun y => a y.1, a.continuous.comp continuous_subtype_val⟩

/-- The restriction of continuous affine scalar maps is linear. -/
private def affRestrictLM (K : Set V) : (V →ᴬ[ℝ] ℝ) →ₗ[ℝ] C(K, ℝ) where
  toFun := affRestrict
  map_add' a b := by
    ext y
    simp [affRestrict, ContinuousAffineMap.add_apply, ContinuousMap.add_apply]
  map_smul' c a := by
    ext y
    simp [affRestrict, ContinuousAffineMap.smul_apply, ContinuousMap.smul_apply,
      smul_eq_mul]

/-- Distinct points of a compact metrizable set are separated by a countable family of
continuous linear functionals. -/
private lemma exists_separatingSeq {K : Set V} [CompactSpace K]
    [TopologicalSpace.MetrizableSpace K] :
    ∃ ell : ℕ → StrongDual ℝ V,
      ∀ ⦃p q : K⦄, p ≠ q → ∃ n, ell n p.1 ≠ ell n q.1 := by
  let off : Set (K × K) := {pq | pq.1 ≠ pq.2}
  let U : StrongDual ℝ V → Set (K × K) :=
    fun ell => {pq | ell pq.1.1 ≠ ell pq.2.1}
  have hUo : ∀ ell, IsOpen (U ell) := by
    intro ell
    have hclosed : IsClosed {pq : K × K | ell pq.1.1 = ell pq.2.1} :=
      isClosed_eq
        (ell.continuous.comp (continuous_subtype_val.comp continuous_fst))
        (ell.continuous.comp (continuous_subtype_val.comp continuous_snd))
    have hcompl : U ell = {pq : K × K | ell pq.1.1 = ell pq.2.1}ᶜ := by
      ext pq
      simp [U]
    rw [hcompl]
    exact hclosed.isOpen_compl
  have hcover : off ⊆ ⋃ ell, U ell := by
    intro pq hpq
    have hne : pq.1.1 ≠ pq.2.1 := by
      intro h
      exact hpq (Subtype.ext h)
    obtain ⟨ell, hell⟩ :=
      SeparatingDual.exists_separating_of_ne (R := ℝ) hne
    exact mem_iUnion.mpr ⟨ell, hell⟩
  obtain ⟨idx, hidx⟩ :=
    @IsLindelof.indexed_countable_subcover (K × K) _ off (StrongDual ℝ V) ⟨0⟩
      (HereditarilyLindelofSpace.isLindelof off) U hUo hcover
  refine ⟨idx, ?_⟩
  intro p q hpq
  have hmem : (p, q) ∈ ⋃ n, U (idx n) := hidx hpq
  simp only [mem_iUnion] at hmem
  obtain ⟨n, hn⟩ := hmem
  exact ⟨n, hn⟩

/-- The least upper bound of the absolute values of a continuous linear functional on `K`. -/
private def supAbs {K : Set V} [CompactSpace K] (ell : StrongDual ℝ V) : ℝ :=
  sSup (range fun y : K => |ell y.1|)

/-- Absolute values on `K` do not exceed `supAbs`. -/
private lemma abs_le_supAbs {K : Set V} [CompactSpace K] (ell : StrongDual ℝ V) (y : K) :
    |ell y.1| ≤ supAbs (K := K) ell := by
  let f : K → ℝ := fun z => |ell z.1|
  have hcont : Continuous f :=
    continuous_abs.comp
      (ell.continuous.comp (continuous_subtype_val : Continuous (fun z : K => (z : V))))
  exact le_csSup (isCompact_range hcont).bddAbove (mem_range_self (f := f) y)

/-- `supAbs` is nonnegative whenever `K` has a point. -/
private lemma supAbs_nonneg {K : Set V} [CompactSpace K] (ell : StrongDual ℝ V) (y : K) :
    0 ≤ supAbs (K := K) ell :=
  (abs_nonneg _).trans (abs_le_supAbs (K := K) ell y)

/-- The normalizing denominator `1 + supAbs`. -/
private def denom {K : Set V} [CompactSpace K] (ell : StrongDual ℝ V) : ℝ :=
  1 + supAbs (K := K) ell

/-- The denominator is positive. -/
private lemma denom_pos {K : Set V} [CompactSpace K] (ell : StrongDual ℝ V) (y : K) :
    0 < denom (K := K) ell := by
  have h0 : 0 ≤ supAbs (K := K) ell := supAbs_nonneg ell y
  dsimp [denom]
  linarith

/-- A continuous linear functional normalized to take values in `[-1, 1]` on `K`. -/
private def normalized {K : Set V} [CompactSpace K] (ell : StrongDual ℝ V) (y : K) : ℝ :=
  ell y.1 / denom (K := K) ell

/-- Normalized values have absolute value at most one. -/
private lemma abs_normalized_le {K : Set V} [CompactSpace K] (ell : StrongDual ℝ V)
    (y : K) : |normalized ell y| ≤ 1 := by
  have hd : 0 < denom (K := K) ell := denom_pos ell y
  rw [normalized, abs_div, abs_of_pos hd, div_le_one hd]
  have h := abs_le_supAbs (K := K) ell y
  dsimp [denom] at h ⊢
  linarith

/-- Normalized functionals preserve convex combinations. -/
private lemma normalized_combo {K : Set V} [CompactSpace K] (ell : StrongDual ℝ V)
    {s t : ℝ} (p q z : K) (hz : z.1 = s • p.1 + t • q.1) :
    normalized ell z = s * normalized ell p + t * normalized ell q := by
  have hd : denom (K := K) ell ≠ 0 := (denom_pos ell p).ne'
  simp only [normalized, hz, map_add, map_smul, smul_eq_mul]
  field_simp [hd]

/-- Geometric weights for the strictly convex series. -/
private def coeff (n : ℕ) : ℝ := ((1 : ℝ) / 2) ^ n

/-- One summand of the strictly convex series. -/
private def term {K : Set V} [CompactSpace K] (ell : ℕ → StrongDual ℝ V) (n : ℕ)
    (y : K) : ℝ :=
  coeff n * (normalized (ell n) y) ^ 2

/-- Each summand is nonnegative. -/
private lemma term_nonneg {K : Set V} [CompactSpace K] (ell : ℕ → StrongDual ℝ V)
    (n : ℕ) (y : K) : 0 ≤ term ell n y := by
  dsimp [term, coeff]
  positivity

/-- Each summand is bounded by its geometric weight. -/
private lemma norm_term_le {K : Set V} [CompactSpace K] (ell : ℕ → StrongDual ℝ V)
    (n : ℕ) (y : K) : ‖term ell n y‖ ≤ coeff n := by
  have hsq : (normalized (ell n) y) ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg _) (abs_normalized_le (ell n) y)
  have hc : 0 ≤ coeff n := by dsimp [coeff]; positivity
  have hterm : term ell n y ≤ coeff n := by
    dsimp [term]
    calc
      coeff n * (normalized (ell n) y) ^ 2 ≤ coeff n * 1 :=
        mul_le_mul_of_nonneg_left hsq hc
      _ = coeff n := mul_one _
  rw [Real.norm_eq_abs, abs_of_nonneg (term_nonneg ell n y)]
  exact hterm

/-- The geometric weights are summable. -/
private lemma summable_coeff : Summable coeff :=
  summable_geometric_two

/-- Each pointwise series of summands converges. -/
private lemma summable_term {K : Set V} [CompactSpace K] (ell : ℕ → StrongDual ℝ V)
    (y : K) : Summable fun n => term ell n y :=
  Summable.of_norm_bounded summable_coeff fun n => norm_term_le ell n y

/-- Each summand is continuous. -/
private lemma continuous_term {K : Set V} [CompactSpace K] (ell : ℕ → StrongDual ℝ V)
    (n : ℕ) : Continuous fun y : K => term ell n y := by
  have hlin : Continuous fun y : K => (ell n) y.1 :=
    (ell n).continuous.comp continuous_subtype_val
  unfold term normalized
  exact continuous_const.mul ((hlin.div_const (denom (K := K) (ell n))).pow 2)

/-- The sum of the series is continuous. -/
private lemma continuous_series {K : Set V} [CompactSpace K] (ell : ℕ → StrongDual ℝ V) :
    Continuous fun y : K => ∑' n, term ell n y :=
  continuous_tsum (fun n => continuous_term ell n) summable_coeff
    fun n y => norm_term_le ell n y

/-- The continuous strictly convex series built from a separating sequence. -/
private def fStrict {K : Set V} [CompactSpace K] (ell : ℕ → StrongDual ℝ V) : C(K, ℝ) :=
  ⟨fun y => ∑' n, term ell n y, continuous_series ell⟩

/-- Evaluation of the strictly convex series. -/
private lemma fStrict_apply {K : Set V} [CompactSpace K] (ell : ℕ → StrongDual ℝ V)
    (y : K) : fStrict ell y = ∑' n, term ell n y :=
  rfl

/-- The series is nonnegative. -/
private lemma fStrict_nonneg {K : Set V} [CompactSpace K] (ell : ℕ → StrongDual ℝ V)
    (y : K) : 0 ≤ fStrict ell y := by
  rw [fStrict_apply]
  exact tsum_nonneg fun n => term_nonneg ell n y

/-- The algebraic defect of a square under a convex combination. -/
private lemma sq_defect {s t a b : ℝ} (hst : s + t = 1) :
    s * a ^ 2 + t * b ^ 2 - (s * a + t * b) ^ 2 = s * t * (a - b) ^ 2 := by
  have ht : t = 1 - s := by linarith
  rw [ht]
  ring

/-- The defect of one summand on a convex combination. -/
private lemma term_defect {K : Set V} [CompactSpace K] (ell : ℕ → StrongDual ℝ V)
    (n : ℕ) {s t : ℝ} (hst : s + t = 1) (p q z : K)
    (hz : z.1 = s • p.1 + t • q.1) :
    s * term ell n p + t * term ell n q - term ell n z =
      coeff n * s * t *
        (normalized (ell n) p - normalized (ell n) q) ^ 2 := by
  have hnorm := normalized_combo (ell n) p q z hz
  simp only [term, hnorm]
  have ht : t = 1 - s := by linarith
  rw [ht]
  ring

/-- The series is strictly convex along nontrivial segments that the sequence separates. -/
private lemma fStrict_strict {K : Set V} [CompactSpace K] (ell : ℕ → StrongDual ℝ V)
    (hell : ∀ ⦃p q : K⦄, p ≠ q → ∃ n, ell n p.1 ≠ ell n q.1)
    {p q z : K} (hpq : p ≠ q) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t = 1)
    (hz : z.1 = s • p.1 + t • q.1) :
    fStrict ell z < s * fStrict ell p + t * fStrict ell q := by
  obtain ⟨n, hn⟩ := hell hpq
  have hne : normalized (ell n) p ≠ normalized (ell n) q := by
    intro h
    apply hn
    have hd : denom (K := K) (ell n) ≠ 0 := (denom_pos (ell n) p).ne'
    simp only [normalized] at h
    field_simp [hd] at h
    exact h
  let defect : ℕ → ℝ :=
    fun m => s * term ell m p + t * term ell m q - term ell m z
  have hdef_nonneg : ∀ m, 0 ≤ defect m := by
    intro m
    dsimp only [defect]
    rw [term_defect ell m hst p q z hz]
    have hc : 0 ≤ coeff m := by unfold coeff; positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg hc hs.le) ht.le) (sq_nonneg _)
  have hdef_pos : 0 < defect n := by
    dsimp only [defect]
    rw [term_defect ell n hst p q z hz]
    have hc : 0 < coeff n := by unfold coeff; positivity
    have hsq : 0 < (normalized (ell n) p - normalized (ell n) q) ^ 2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
    exact mul_pos (mul_pos (mul_pos hc hs) ht) hsq
  have hsummable : Summable defect :=
    (((summable_term ell p).mul_left s).add ((summable_term ell q).mul_left t)).sub
      (summable_term ell z)
  have htsum_pos : 0 < ∑' m, defect m := hsummable.tsum_pos hdef_nonneg n hdef_pos
  have hhas : HasSum defect
      (s * fStrict ell p + t * fStrict ell q - fStrict ell z) := by
    have hbase :=
      (((summable_term ell p).hasSum.mul_left s).add
        ((summable_term ell q).hasSum.mul_left t)).sub (summable_term ell z).hasSum
    simpa [defect, fStrict_apply] using hbase
  have htsum := hhas.tsum_eq
  linarith

/-- The series is not the restriction of a continuous affine scalar map. -/
private lemma fStrict_not_mem_range {K : Set V} [CompactSpace K] (hc : Convex ℝ K)
    (hns : ¬ Subsingleton K) (ell : ℕ → StrongDual ℝ V)
    (hell : ∀ ⦃p q : K⦄, p ≠ q → ∃ n, ell n p.1 ≠ ell n q.1) :
    fStrict ell ∉ LinearMap.range (affRestrictLM K) := by
  intro hmem
  obtain ⟨p, q, hpq⟩ :=
    @exists_pair_ne K (not_subsingleton_iff_nontrivial.mp hns)
  obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hmem
  have hs : (0 : ℝ) < 2⁻¹ := by positivity
  have hst : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 := by ring
  have hzmem : (2 : ℝ)⁻¹ • p.1 + (2 : ℝ)⁻¹ • q.1 ∈ K :=
    (convex_iff_add_mem.mp hc) p.2 q.2 (le_of_lt hs) (le_of_lt hs) hst
  let z : K := ⟨_, hzmem⟩
  have hstrict := fStrict_strict ell hell hpq hs hs hst (z := z) rfl
  have haff := affine_combo a hst p.1 q.1
  have hcoe : ∀ y : K, fStrict ell y = a y.1 := by
    intro y
    have happ : (affRestrictLM K a) y = a y.1 := by
      simp [affRestrictLM, affRestrict]
    exact (DFunLike.congr_fun ha y).symm.trans happ
  have heq : fStrict ell z = a z.1 := hcoe z
  have hp : fStrict ell p = a p.1 := hcoe p
  have hq : fStrict ell q = a q.1 := hcoe q
  have hza : a z.1 = 2⁻¹ * a p.1 + 2⁻¹ * a q.1 := by
    simpa [z] using haff
  have heq' : fStrict ell z =
      2⁻¹ * fStrict ell p + 2⁻¹ * fStrict ell q := by
    rw [heq, hp, hq, hza]
  exact lt_irrefl _ (hstrict.trans_eq heq'.symm)

/-- Continuous affine scalar maps that dominate a continuous function on `K`. -/
private def majorants {K : Set V} (g : C(K, ℝ)) : Set (V →ᴬ[ℝ] ℝ) :=
  {a | ∀ y : K, g y ≤ a y.1}

/-- Values at `z` of the affine majorants of `g`. -/
private def valueAt {K : Set V} (g : C(K, ℝ)) (z : K) : Set ℝ :=
  (fun a => a z.1) '' majorants g

/-- A continuous function on compact `K` is bounded above. -/
private lemma exists_upper_bound {K : Set V} [CompactSpace K] (g : C(K, ℝ)) :
    ∃ M : ℝ, ∀ y : K, g y ≤ M := by
  refine ⟨‖g‖, fun y => ?_⟩
  calc
    g y ≤ |g y| := le_abs_self _
    _ = ‖g y‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖g‖ := ContinuousMap.norm_coe_le_norm g y

/-- Every continuous function on compact `K` admits a constant affine majorant. -/
private lemma majorants_nonempty {K : Set V} [CompactSpace K] (g : C(K, ℝ)) :
    (majorants g).Nonempty := by
  obtain ⟨M, hM⟩ := exists_upper_bound g
  refine ⟨ContinuousAffineMap.const ℝ V M, ?_⟩
  intro y
  simpa [ContinuousAffineMap.coe_const] using hM y

/-- The set of majorant values is nonempty. -/
private lemma valueAt_nonempty {K : Set V} [CompactSpace K] (g : C(K, ℝ)) (z : K) :
    (valueAt g z).Nonempty := by
  obtain ⟨a, ha⟩ := majorants_nonempty g
  exact ⟨a z.1, a, ha, rfl⟩

/-- The set of majorant values is bounded below by the function. -/
private lemma valueAt_bddBelow {K : Set V} (g : C(K, ℝ)) (z : K) :
    BddBelow (valueAt g z) := by
  refine ⟨g z, ?_⟩
  intro r hr
  obtain ⟨a, ha, rfl⟩ := hr
  exact ha z

/-- The concave envelope is the infimum of the affine majorants. -/
private def envelope {K : Set V} [CompactSpace K] (g : C(K, ℝ)) (z : K) : ℝ :=
  sInf (valueAt g z)

/-- A continuous function lies under its envelope. -/
private lemma le_envelope {K : Set V} [CompactSpace K] (g : C(K, ℝ)) (z : K) :
    g z ≤ envelope g z := by
  refine le_csInf (valueAt_nonempty g z) ?_
  intro r hr
  obtain ⟨a, ha, rfl⟩ := hr
  exact ha z

/-- Each affine majorant lies over the envelope. -/
private lemma envelope_le_of_majorant {K : Set V} [CompactSpace K] (g : C(K, ℝ)) (z : K)
    {a : V →ᴬ[ℝ] ℝ} (ha : a ∈ majorants g) : envelope g z ≤ a z.1 :=
  csInf_le (valueAt_bddBelow g z) ⟨a, ha, rfl⟩

/-- Some affine majorant nearly attains the envelope. -/
private lemma exists_majorant_lt {K : Set V} [CompactSpace K] (g : C(K, ℝ)) (z : K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : V →ᴬ[ℝ] ℝ, a ∈ majorants g ∧ a z.1 < envelope g z + ε := by
  by_contra h
  push Not at h
  have hle : envelope g z + ε ≤ envelope g z := by
    refine le_csInf (valueAt_nonempty g z) ?_
    intro r hr
    obtain ⟨a, ha, rfl⟩ := hr
    exact h a ha
  linarith

/-- The envelope is subadditive. -/
private lemma envelope_add_le {K : Set V} [CompactSpace K] (g h : C(K, ℝ)) (z : K) :
    envelope (g + h) z ≤ envelope g z + envelope h z := by
  rw [le_iff_forall_pos_lt_add]
  intro ε hε
  obtain ⟨a, ha, haε⟩ := exists_majorant_lt g z (half_pos hε)
  obtain ⟨b, hb, hbε⟩ := exists_majorant_lt h z (half_pos hε)
  have hmaj : a + b ∈ majorants (g + h) := by
    intro y
    simp only [ContinuousMap.add_apply, ContinuousAffineMap.add_apply]
    linarith [ha y, hb y]
  have hle := envelope_le_of_majorant (g + h) z hmaj
  have hadd : (a + b) z.1 = a z.1 + b z.1 := by
    simp [ContinuousAffineMap.add_apply]
  linarith

/-- The envelope is positively homogeneous. -/
private lemma envelope_smul {K : Set V} [CompactSpace K] (g : C(K, ℝ)) (z : K)
    {c : ℝ} (hc : 0 < c) : envelope (c • g) z = c * envelope g z := by
  apply le_antisymm
  · rw [le_iff_forall_pos_lt_add]
    intro ε hε
    obtain ⟨a, ha, haε⟩ := exists_majorant_lt g z (div_pos hε hc)
    have hmaj : c • a ∈ majorants (c • g) := by
      intro y
      simp only [ContinuousMap.smul_apply, ContinuousAffineMap.smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (ha y) hc.le
    have hle := envelope_le_of_majorant (c • g) z hmaj
    have hval : (c • a) z.1 = c * a z.1 := by
      simp [ContinuousAffineMap.smul_apply, smul_eq_mul]
    have hcmp : c * a z.1 < c * envelope g z + ε := by
      have hlt : a z.1 < envelope g z + ε / c := haε
      have hmul := mul_lt_mul_of_pos_left hlt hc
      have hrew : c * (envelope g z + ε / c) = c * envelope g z + ε := by
        field_simp
      linarith
    linarith
  · refine le_csInf (valueAt_nonempty (c • g) z) ?_
    intro r hr
    obtain ⟨b, hb, rfl⟩ := hr
    have hmaj : c⁻¹ • b ∈ majorants g := by
      intro y
      have hby : c * g y ≤ b y.1 := by
        simpa [ContinuousMap.smul_apply, smul_eq_mul] using hb y
      simp only [ContinuousAffineMap.smul_apply, smul_eq_mul]
      rw [mul_comm] at hby
      rw [← div_eq_inv_mul, le_div_iff₀ hc]
      exact hby
    have henv := envelope_le_of_majorant g z hmaj
    simp only [ContinuousAffineMap.smul_apply, smul_eq_mul] at henv
    have hmul := mul_le_mul_of_nonneg_left henv hc.le
    have hcancel : c * (c⁻¹ * b z.1) = b z.1 := by
      rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    linarith

/-- On a convex combination, the envelope of the series is concave. -/
private lemma envelope_concave {K : Set V} [CompactSpace K] (ell : ℕ → StrongDual ℝ V)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) {p q z : K}
    (hz : z.1 = s • p.1 + t • q.1) :
    s * envelope (fStrict ell) p + t * envelope (fStrict ell) q ≤
      envelope (fStrict ell) z := by
  refine le_csInf (valueAt_nonempty (fStrict ell) z) ?_
  intro r hr
  obtain ⟨a, ha, rfl⟩ := hr
  have hsplit : a z.1 = s * a p.1 + t * a q.1 := by
    rw [hz]
    exact affine_combo a hst p.1 q.1
  have hp := envelope_le_of_majorant (fStrict ell) p ha
  have hq := envelope_le_of_majorant (fStrict ell) q ha
  nlinarith

/-- A non-extreme point is a point of strict inequality for the series and its envelope. -/
private lemma fStrict_lt_envelope_of_not_extreme {K : Set V} [CompactSpace K]
    (_hc : Convex ℝ K) (ell : ℕ → StrongDual ℝ V)
    (hell : ∀ ⦃p q : K⦄, p ≠ q → ∃ n, ell n p.1 ≠ ell n q.1) {y : K}
    (hy : y.1 ∉ K.extremePoints ℝ) :
    fStrict ell y < envelope (fStrict ell) y := by
  have hnot : ¬ (y.1 ∈ K ∧ ∀ x1, x1 ∈ K → ∀ x2, x2 ∈ K →
      y.1 ∈ openSegment ℝ x1 x2 → x1 = y.1) := by
    simpa [mem_extremePoints_iff_left] using hy
  have hnot' := (not_and.mp hnot) y.2
  simp only [not_forall] at hnot'
  obtain ⟨x1, hx1, x2, hx2, hseg, hne⟩ := hnot'
  have hseg' : ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ s + t = 1 ∧ s • x1 + t • x2 = y.1 := by
    simpa [openSegment] using hseg
  obtain ⟨s, t, hs, ht, hst, hcomb⟩ := hseg'
  have hx12 : x1 ≠ x2 := by
    intro h
    have : y.1 ∈ openSegment ℝ x1 x1 := by simpa [h] using hseg
    rw [openSegment_same, mem_singleton_iff] at this
    exact hne this.symm
  let p : K := ⟨x1, hx1⟩
  let q : K := ⟨x2, hx2⟩
  have hpq : p ≠ q := by
    intro h
    exact hx12 (congrArg Subtype.val h)
  have hstrict := fStrict_strict ell hell hpq hs ht hst (z := y) hcomb.symm
  have hle_p : fStrict ell p ≤ envelope (fStrict ell) p := le_envelope _ _
  have hle_q : fStrict ell q ≤ envelope (fStrict ell) q := le_envelope _ _
  have hconc :=
    envelope_concave ell hs.le ht.le hst (p := p) (q := q) (z := y) hcomb.symm
  have hmid : s * fStrict ell p + t * fStrict ell q ≤
      s * envelope (fStrict ell) p + t * envelope (fStrict ell) q := by
    have hp' := mul_le_mul_of_nonneg_left hle_p hs.le
    have hq' := mul_le_mul_of_nonneg_left hle_q ht.le
    linarith
  exact (hstrict.trans_le hmid).trans_le hconc

/-- The direct sum of an affine restriction and a multiple of the series. -/
private def seriesDecomp {K : Set V} [CompactSpace K] (ell : ℕ → StrongDual ℝ V) :
    LinearMap.range (affRestrictLM K) × ℝ →ₗ[ℝ] C(K, ℝ) :=
  (LinearMap.range (affRestrictLM K)).subtype.coprod
    (LinearMap.toSpanSingleton ℝ C(K, ℝ) (fStrict ell))

/-- Pointwise value of an affine restriction plus a multiple of the series. -/
private lemma seriesDecomp_apply {K : Set V} [CompactSpace K]
    (ell : ℕ → StrongDual ℝ V)
    (pr : LinearMap.range (affRestrictLM K) × ℝ) (y : K) :
    seriesDecomp ell pr y = (pr.1 : C(K, ℝ)) y + pr.2 * fStrict ell y := by
  rw [seriesDecomp, LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply]
  simp [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]

/-- A range element coming from an affine map evaluates as that map. -/
private lemma range_apply {K : Set V} {a : V →ᴬ[ℝ] ℝ}
    {φ : LinearMap.range (affRestrictLM K)}
    (hφ : affRestrictLM K a = (φ : C(K, ℝ))) (y : K) :
    (φ : C(K, ℝ)) y = a y.1 := by
  have hcoe : (affRestrictLM K a) y = a y.1 := by
    simp [affRestrictLM, affRestrict]
  rw [hφ] at hcoe
  exact hcoe

/-- The decomposition is injective when the series is not affine. -/
private lemma seriesDecomp_injective {K : Set V} [CompactSpace K] (hc : Convex ℝ K)
    (hns : ¬ Subsingleton K) (ell : ℕ → StrongDual ℝ V)
    (hell : ∀ ⦃p q : K⦄, p ≠ q → ∃ n, ell n p.1 ≠ ell n q.1) :
    Function.Injective (seriesDecomp (K := K) ell) := by
  refine (LinearMap.ker_eq_bot (f := seriesDecomp (K := K) ell)).mp ?_
  refine (LinearMap.ker_eq_bot' (f := seriesDecomp (K := K) ell)).mpr ?_
  intro pr hpr
  have hzero : (pr.1 : C(K, ℝ)) + pr.2 • fStrict ell = 0 := by
    rw [seriesDecomp, LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply] at hpr
    exact hpr
  by_cases hr : pr.2 = 0
  · have hφ : (pr.1 : C(K, ℝ)) = 0 := by
      rw [hr, zero_smul, add_zero] at hzero
      exact hzero
    exact Prod.ext (Subtype.ext hφ) hr
  · have hφ : (pr.1 : C(K, ℝ)) = -pr.2 • fStrict ell := by
      rw [neg_smul, eq_neg_iff_add_eq_zero]
      exact hzero
    have hf : fStrict ell = (-pr.2)⁻¹ • (pr.1 : C(K, ℝ)) := by
      calc
        fStrict ell = (1 : ℝ) • fStrict ell := (one_smul _ _).symm
        _ = ((-pr.2)⁻¹ * -pr.2) • fStrict ell :=
          congrArg (fun t => t • fStrict ell)
            (inv_mul_cancel₀ (neg_ne_zero.mpr hr)).symm
        _ = (-pr.2)⁻¹ • (-pr.2 • fStrict ell) := (smul_smul _ _ _).symm
        _ = (-pr.2)⁻¹ • (pr.1 : C(K, ℝ)) :=
          congrArg (fun t => (-pr.2)⁻¹ • t) hφ.symm
    obtain ⟨a, ha⟩ := (pr.1).2
    have hmem : fStrict ell ∈ LinearMap.range (affRestrictLM K) := by
      refine ⟨(-pr.2)⁻¹ • a, ?_⟩
      calc
        affRestrictLM K ((-pr.2)⁻¹ • a) = (-pr.2)⁻¹ • affRestrictLM K a :=
          LinearMap.map_smul _ _ _
        _ = (-pr.2)⁻¹ • (pr.1 : C(K, ℝ)) :=
          congrArg (fun t => (-pr.2)⁻¹ • t) ha
        _ = fStrict ell := hf.symm
    exact (fStrict_not_mem_range hc hns ell hell hmem).elim

/-- Barycentric evaluation on an affine restriction plus a multiple of the series. -/
private def pairEval {K : Set V} [CompactSpace K] (x0 : K) (ell : ℕ → StrongDual ℝ V) :
    LinearMap.range (affRestrictLM K) × ℝ →ₗ[ℝ] ℝ where
  toFun pr := (pr.1 : C(K, ℝ)) x0 + pr.2 * envelope (fStrict ell) x0
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, ContinuousMap.add_apply,
      add_mul]
    ring
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, ContinuousMap.smul_apply,
      smul_eq_mul, RingHom.id_apply, mul_add]
    ring

/-- The barycentric value of a series element does not exceed the envelope. -/
private lemma pairEval_le_envelope {K : Set V} [CompactSpace K]
    (ell : ℕ → StrongDual ℝ V) (x0 : K)
    (pr : LinearMap.range (affRestrictLM K) × ℝ) :
    pairEval x0 ell pr ≤ envelope (seriesDecomp ell pr) x0 := by
  by_cases hr : pr.2 < 0
  · have hfle : fStrict ell x0 ≤ envelope (fStrict ell) x0 := le_envelope _ _
    have hmul : pr.2 * envelope (fStrict ell) x0 ≤ pr.2 * fStrict ell x0 :=
      mul_le_mul_of_nonpos_left hfle hr.le
    have hpoint : seriesDecomp ell pr x0 =
        (pr.1 : C(K, ℝ)) x0 + pr.2 * fStrict ell x0 := by
      simp [seriesDecomp, LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply,
        ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
    have hge : seriesDecomp ell pr x0 ≤ envelope (seriesDecomp ell pr) x0 :=
      le_envelope _ _
    dsimp [pairEval]
    linarith
  · push Not at hr
    obtain ⟨aφ, haφ⟩ := (pr.1).2
    by_cases hr0 : pr.2 = 0
    · have hψ : seriesDecomp ell pr = pr.1 := by
        ext y
        rw [seriesDecomp_apply, hr0, zero_mul, add_zero]
      have hself : aφ ∈ majorants (seriesDecomp ell pr) := by
        intro y
        have heq : (seriesDecomp ell pr) y = aφ y.1 := by
          rw [hψ, range_apply haφ y]
        simp [heq]
      have hval : aφ x0.1 = (pr.1 : C(K, ℝ)) x0 := (range_apply haφ x0).symm
      have hge : aφ x0.1 ≤ envelope (seriesDecomp ell pr) x0 := by
        rw [← range_apply haφ x0, ← hψ]
        exact le_envelope _ _
      dsimp [pairEval]
      rw [hr0, zero_mul, add_zero, ← hval]
      exact hge
    · have hrpos : 0 < pr.2 := lt_of_le_of_ne hr (Ne.symm hr0)
      have hle_all : ∀ b ∈ majorants (seriesDecomp ell pr),
          pairEval x0 ell pr ≤ b x0.1 := by
        intro b hb
        have hdom : ∀ y : K, pr.2 * fStrict ell y ≤ (b - aφ) y.1 := by
          intro y
          have hby := hb y
          have hψ : seriesDecomp ell pr y =
              (pr.1 : C(K, ℝ)) y + pr.2 * fStrict ell y :=
            seriesDecomp_apply ell pr y
          have hφ : (pr.1 : C(K, ℝ)) y = aφ y.1 := range_apply haφ y
          simp only [ContinuousAffineMap.sub_apply] at *
          linarith
        have hmaj : pr.2⁻¹ • (b - aφ) ∈ majorants (fStrict (K := K) ell) := by
          intro y
          simp only [ContinuousAffineMap.smul_apply, smul_eq_mul]
          have hmul : fStrict ell y * pr.2 ≤ (b - aφ) y.1 := by
            rw [mul_comm]
            exact hdom y
          rw [← div_eq_inv_mul, le_div_iff₀ hrpos]
          exact hmul
        have henv := envelope_le_of_majorant (fStrict (K := K) ell) x0 hmaj
        simp only [ContinuousAffineMap.smul_apply, smul_eq_mul,
          ContinuousAffineMap.sub_apply] at henv
        have hscaled : pr.2 * envelope (fStrict (K := K) ell) x0 ≤
            b x0.1 - aφ x0.1 := by
          have hmul := mul_le_mul_of_nonneg_left henv hrpos.le
          rw [← mul_assoc, mul_inv_cancel₀ hrpos.ne', one_mul] at hmul
          exact hmul
        have hφx : aφ x0.1 = (pr.1 : C(K, ℝ)) x0 := (range_apply haφ x0).symm
        have hsum : (pr.1 : C(K, ℝ)) x0 +
            pr.2 * envelope (fStrict (K := K) ell) x0 ≤ b x0.1 := by
          rw [← hφx, add_comm, ← le_sub_iff_add_le]
          exact hscaled
        dsimp [pairEval]
        exact hsum
      refine le_csInf (valueAt_nonempty _ x0) ?_
      intro r hr
      obtain ⟨b, hb, rfl⟩ := hr
      exact hle_all b hb

/-- The envelope is upper semicontinuous. -/
private lemma envelope_upperSemicontinuous {K : Set V} [CompactSpace K] (g : C(K, ℝ)) :
    UpperSemicontinuous (envelope g) := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro c
  have hset : envelope g ⁻¹' Iio c =
      ⋃ a ∈ majorants g, {z : K | a z.1 < c} := by
    ext z
    simp only [mem_preimage, mem_Iio, mem_iUnion, mem_ofPred_eq]
    constructor
    · intro hz
      have hε : 0 < c - envelope g z := sub_pos.mpr hz
      obtain ⟨a, ha, haε⟩ := exists_majorant_lt g z hε
      refine ⟨a, ha, ?_⟩
      linarith
    · intro ⟨a, ha, hlt⟩
      exact lt_of_le_of_lt (envelope_le_of_majorant g z ha) hlt
  rw [hset]
  exact isOpen_biUnion fun a _ =>
    isOpen_lt (a.continuous.comp continuous_subtype_val) continuous_const

/-- The series is bounded by its supremum norm. -/
private lemma fStrict_le_norm {K : Set V} [CompactSpace K] (ell : ℕ → StrongDual ℝ V)
    (y : K) : fStrict (K := K) ell y ≤ ‖fStrict (K := K) ell‖ := by
  have hnn := fStrict_nonneg ell y
  calc
    fStrict ell y = |(fStrict ell) y| := by rw [abs_of_nonneg hnn]
    _ = ‖(fStrict ell) y‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fStrict (K := K) ell‖ :=
      ContinuousMap.norm_coe_le_norm (fStrict (K := K) ell) y

/-- The envelope of the series is bounded by the supremum norm of the series. -/
private lemma abs_envelope_le {K : Set V} [CompactSpace K] (ell : ℕ → StrongDual ℝ V)
    (z : K) : |envelope (fStrict (K := K) ell) z| ≤ ‖fStrict (K := K) ell‖ := by
  have h0 : 0 ≤ envelope (fStrict (K := K) ell) z :=
    (fStrict_nonneg ell z).trans (le_envelope _ _)
  rw [abs_of_nonneg h0]
  exact envelope_le_of_majorant (fStrict (K := K) ell) z
    (a := ContinuousAffineMap.const ℝ V ‖fStrict (K := K) ell‖) <| by
    intro y
    rw [ContinuousAffineMap.coe_const]
    exact fStrict_le_norm ell y

/-- Choquet representation when `K` has at least two points. -/
private theorem exists_choquet_bonsall (K : Set V) (hK : IsCompact K) (hc : Convex ℝ K)
    [TopologicalSpace.MetrizableSpace K] [MeasurableSpace K] [BorelSpace K]
    (hns : ¬ Subsingleton K) (x0 : K) :
    ∃ μ : Measure K, IsProbabilityMeasure μ ∧
      μ {y : K | y.1 ∉ K.extremePoints ℝ} = 0 ∧
      ∀ a : V →ᴬ[ℝ] ℝ, (∫ y : K, a y.1 ∂μ) = a x0.1 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨ell, hell⟩ := exists_separatingSeq (K := K)
  let decomp := seriesDecomp (K := K) ell
  have hinj : Function.Injective decomp := seriesDecomp_injective hc hns ell hell
  let equiv := LinearEquiv.ofInjective decomp hinj
  let pmap : C(K, ℝ) →ₗ.[ℝ] ℝ :=
    { domain := LinearMap.range decomp
      toFun := (pairEval x0 ell).comp equiv.symm.toLinearMap }
  have hdom : ∀ x : pmap.domain, pmap x ≤ envelope (x : C(K, ℝ)) x0 := by
    intro x
    let pre := equiv.symm x
    have hcoe : decomp pre = (x : C(K, ℝ)) :=
      LinearEquiv.ofInjective_symm_apply (f := decomp) (h := hinj) x
    have happ : pmap x = pairEval x0 ell pre := by
      change (pairEval x0 ell) (equiv.symm x) = pairEval x0 ell pre
      rfl
    rw [happ]
    have hle := pairEval_le_envelope ell x0 pre
    rw [show seriesDecomp ell pre = (x : C(K, ℝ)) from hcoe] at hle
    exact hle
  have hhom : ∀ c : ℝ, 0 < c → ∀ g : C(K, ℝ),
      envelope (c • g) x0 = c * envelope g x0 :=
    fun c hc g => envelope_smul g x0 hc
  have hadd : ∀ g h : C(K, ℝ),
      envelope (g + h) x0 ≤ envelope g x0 + envelope h x0 :=
    fun g h => envelope_add_le g h x0
  obtain ⟨L, hL, hN⟩ :=
    exists_extension_of_le_sublinear pmap (fun g => envelope g x0) hhom hadd hdom
  have hpos : ∀ g : C(K, ℝ), 0 ≤ g → 0 ≤ L g := by
    intro g hg
    have hmaj : ContinuousAffineMap.const ℝ V 0 ∈ majorants (-g) := by
      intro y
      have hgy : 0 ≤ g y := by
        rw [ContinuousMap.le_def] at hg
        simpa using hg y
      simp [ContinuousAffineMap.coe_const, ContinuousMap.neg_apply]
      linarith
    have henv : envelope (-g) x0 ≤ 0 := by
      simpa [ContinuousAffineMap.coe_const] using envelope_le_of_majorant (-g) x0 hmaj
    have hneg : L (-g) ≤ 0 := (hN (-g)).trans henv
    rw [map_neg] at hneg
    exact neg_nonpos.mp hneg
  have hpair : ∀ pr, L (decomp pr) = pairEval x0 ell pr := by
    intro pr
    have hagree := hL (equiv pr)
    have hlhs : (equiv pr : C(K, ℝ)) = decomp pr :=
      (LinearEquiv.ofInjective_apply (f := decomp) (h := hinj) pr).symm
    have hrhs : pmap (equiv pr) = pairEval x0 ell pr := by
      change pairEval x0 ell (equiv.symm (equiv pr)) = pairEval x0 ell pr
      rw [LinearEquiv.symm_apply_apply]
    rw [← hlhs, hagree, hrhs]
  have hconst : L 1 = 1 := by
    let a1 := ContinuousAffineMap.const ℝ V (1 : ℝ)
    let φ : LinearMap.range (affRestrictLM K) :=
      ⟨affRestrictLM K a1, LinearMap.mem_range_self _ a1⟩
    have hdec : decomp (φ, 0) = 1 := by
      ext y
      rw [show (decomp (φ, 0)) y = seriesDecomp ell (φ, 0) y from rfl,
        seriesDecomp_apply ell (φ, 0) y, zero_mul, add_zero]
      simp [a1, φ, affRestrictLM, affRestrict, ContinuousAffineMap.coe_const,
        ContinuousMap.one_apply]
    have heval : pairEval x0 ell (φ, 0) = 1 := by
      dsimp [pairEval]
      rw [zero_mul, add_zero]
      simp [a1, φ, affRestrictLM, affRestrict, ContinuousAffineMap.coe_const]
    rw [← hdec, hpair (φ, 0), heval]
  have haff : ∀ a : V →ᴬ[ℝ] ℝ, L (affRestrictLM K a) = a x0.1 := by
    intro a
    let φ : LinearMap.range (affRestrictLM K) :=
      ⟨affRestrictLM K a, LinearMap.mem_range_self _ a⟩
    have hdec : decomp (φ, 0) = affRestrictLM K a := by
      ext y
      rw [show (decomp (φ, 0)) y = seriesDecomp ell (φ, 0) y from rfl,
        seriesDecomp_apply ell (φ, 0) y, zero_mul, add_zero]
    have heval : pairEval x0 ell (φ, 0) = a x0.1 := by
      dsimp [pairEval]
      rw [zero_mul, add_zero]
      simp [φ, affRestrictLM, affRestrict]
    rw [← hdec, hpair, heval]
  have hfL : L (fStrict ell) = envelope (fStrict ell) x0 := by
    let φ0 : LinearMap.range (affRestrictLM K) := 0
    have hdec : decomp (φ0, 1) = fStrict ell := by
      ext y
      rw [show (decomp (φ0, 1)) y = seriesDecomp ell (φ0, 1) y from rfl,
        seriesDecomp_apply ell (φ0, 1) y, Submodule.coe_zero, one_mul]
      simp [ContinuousMap.zero_apply, zero_add]
    have heval : pairEval x0 ell (φ0, 1) = envelope (fStrict ell) x0 := by
      dsimp [pairEval]
      rw [Submodule.coe_zero, one_mul]
      simp [ContinuousMap.zero_apply, zero_add]
    have hLde : L (decomp (φ0, 1)) = envelope (fStrict ell) x0 := by
      rw [hpair, heval]
    rw [hdec] at hLde
    exact hLde
  let ccToC : C_c(K, ℝ) →ₗ[ℝ] C(K, ℝ) :=
    { toFun := fun f => f.toContinuousMap
      map_add' := fun f g => by
        ext y
        simp
      map_smul' := fun c f => by
        ext y
        simp [smul_eq_mul] }
  let Λ : C_c(K, ℝ) →ₚ[ℝ] ℝ :=
    PositiveLinearMap.mk₀ (L.comp ccToC) fun g hg => by
      apply hpos
      rw [ContinuousMap.le_def]
      intro y
      exact (CompactlySupportedContinuousMap.le_def.mp hg) y
  let μ : Measure K := RealRMK.rieszMeasure Λ
  have hintegral : ∀ g : C(K, ℝ), ∫ y, g y ∂μ = L g := by
    intro g
    have hri := RealRMK.integral_rieszMeasure (Λ := Λ)
      (CompactlySupportedContinuousMap.continuousMapEquiv g)
    have hfun : (fun y : K =>
        (CompactlySupportedContinuousMap.continuousMapEquiv g) y) = g := by
      ext y
      simp [CompactlySupportedContinuousMap.continuousMapEquiv]
    have hΛ : Λ (CompactlySupportedContinuousMap.continuousMapEquiv g) = L g := by
      change L (ccToC (CompactlySupportedContinuousMap.continuousMapEquiv g)) = L g
      congr 1
    simpa [μ, hfun] using hri.trans hΛ
  have hprob : IsProbabilityMeasure μ := by
    rw [isProbabilityMeasure_iff_real]
    have hint := integral_const (μ := μ) (1 : ℝ)
    have h1 : ∫ _ : K, (1 : ℝ) ∂μ = 1 := by
      have hfun : (fun _ : K => (1 : ℝ)) = (1 : C(K, ℝ)) := by
        ext y
        simp
      rw [hfun, hintegral, hconst]
    have hsmul : μ.real univ • (1 : ℝ) = μ.real univ := by simp
    rw [h1] at hint
    simpa [hsmul] using hint.symm
  have haff_int : ∀ a : V →ᴬ[ℝ] ℝ, (∫ y : K, a y.1 ∂μ) = a x0.1 := by
    intro a
    have hfun : (fun y : K => a y.1) = affRestrictLM K a := by
      ext y
      simp [affRestrictLM, affRestrict]
    rw [hfun, hintegral, haff]
  have hlt_null : μ {y : K | fStrict ell y < envelope (fStrict ell) y} = 0 := by
    have hmeas : Measurable (envelope (fStrict (K := K) ell)) :=
      (envelope_upperSemicontinuous (fStrict (K := K) ell)).measurable
    have hbound : ∀ y : K,
        ‖envelope (fStrict (K := K) ell) y‖ ≤ ‖fStrict (K := K) ell‖ := by
      intro y
      rw [Real.norm_eq_abs]
      exact abs_envelope_le (K := K) ell y
    have hinte : Integrable (envelope (fStrict ell)) μ :=
      Integrable.of_bound hmeas.aestronglyMeasurable ‖fStrict ell‖ (ae_of_all _ hbound)
    have hintf : Integrable (fStrict ell) μ :=
      (fStrict ell).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hint_le : ∫ y, envelope (fStrict ell) y ∂μ ≤ envelope (fStrict ell) x0 := by
      refine le_csInf (valueAt_nonempty _ x0) ?_
      intro r hr
      obtain ⟨a, ha, rfl⟩ := hr
      have hinta : Integrable (fun y : K => a y.1) μ :=
        (a.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hpt : envelope (fStrict ell) ≤ fun y => a y.1 :=
        fun y => envelope_le_of_majorant _ y ha
      have hmono := integral_mono hinte hinta hpt
      have heq : ∫ y, a y.1 ∂μ = a x0.1 := haff_int a
      linarith
    have hge : envelope (fStrict ell) x0 ≤ ∫ y, envelope (fStrict ell) y ∂μ := by
      have hpt : ∀ y : K, fStrict ell y ≤ envelope (fStrict ell) y :=
        fun y => le_envelope (fStrict ell) y
      have hmono := integral_mono_ae hintf hinte (ae_of_all _ hpt)
      rw [hintegral, hfL] at hmono
      exact hmono
    have hint_eq : ∫ y, envelope (fStrict ell) y ∂μ = ∫ y, fStrict ell y ∂μ := by
      linarith [hint_le, hge, show ∫ y, fStrict ell y ∂μ = envelope (fStrict ell) x0 from
        (hintegral (fStrict ell)).trans hfL]
    have hdiff : ∫ y, envelope (fStrict ell) y - fStrict ell y ∂μ = 0 := by
      rw [integral_sub hinte hintf, hint_eq, sub_self]
    have hnn : 0 ≤ fun y : K => envelope (fStrict ell) y - fStrict ell y :=
      fun y => sub_nonneg.mpr (le_envelope _ y)
    have hae : (fun y : K => envelope (fStrict ell) y - fStrict ell y) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg hnn (hinte.sub hintf)).1 hdiff
    have hnull : μ {y | envelope (fStrict ell) y - fStrict ell y ≠ 0} = 0 := by
      rw [← ae_iff]
      have hzero := hae
      rw [Filter.EventuallyEq] at hzero
      exact hzero.mono fun y hy => hy.trans (Pi.zero_apply y)
    refine measure_mono_null ?_ hnull
    intro y hy
    exact ne_of_gt (sub_pos.mpr hy)
  have hextreme : μ {y : K | y.1 ∉ K.extremePoints ℝ} = 0 := by
    refine measure_mono_null ?_ hlt_null
    intro y hy
    exact fStrict_lt_envelope_of_not_extreme hc ell hell hy
  exact ⟨μ, hprob, hextreme, haff_int⟩

/-- **12.9**: every point of a compact metrizable convex set is the barycenter of a
probability measure carried by the extreme points. -/
theorem exists_choquetMeasure_of_compact {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    [LocallyConvexSpace ℝ V] [T2Space V] (K : Set V) (hK : IsCompact K) (hc : Convex ℝ K)
    [TopologicalSpace.MetrizableSpace K] [MeasurableSpace K] [BorelSpace K] (x : K) :
    ∃ μ : Measure K, IsProbabilityMeasure μ ∧
      μ {y : K | y.1 ∉ K.extremePoints ℝ} = 0 ∧
      ∀ a : V →ᴬ[ℝ] ℝ, (∫ y : K, a y.1 ∂μ) = a x.1 := by
  by_cases hsub : Subsingleton K
  · exact exists_choquet_dirac K hK hc x hsub
  · exact exists_choquet_bonsall K hK hc hsub x

end CKMA
