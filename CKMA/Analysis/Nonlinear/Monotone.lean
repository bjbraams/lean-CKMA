/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Nonlinear.FixedPoint
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Convex.Uniform.Basic
public import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Topology.Order.OrderClosed

/-!
# Monotone graphs, resolvents, and variational inequalities

Hilbert-space graph monotonicity gives resolvent uniqueness at nonnegative scales; Minty's
range criterion and existence use strictly positive scales. The normal cone includes its
base-point constraint.

For maps into a real Banach dual, monotonicity, hemicontinuity, boundedness on bounded sets,
and coercivity are expressed directly in the dual pairing. Reflexivity uses surjectivity of
the canonical bidual inclusion. Variational inequalities have separate bounded-domain and
coercive unbounded-domain existence statements. Sources: GAPS 35.32, 35.40, and 35.45.

## Main definitions

* `CKMA.IsMonotoneGraph`: Monotonicity of a Hilbert-space graph.
* `CKMA.IsMaximalMonotoneGraph`: Maximal monotonicity of a Hilbert-space graph.
* `CKMA.monotoneResolventFiber`: Resolvent fiber `{y | ∃ u, (y, u) ∈ A ∧ x = y + a • u}`.
* `CKMA.normalConeGraph`: Normal-cone graph of a convex set.
* `CKMA.IsMonotoneDualMap`: Monotonicity for a map into the continuous dual.
* `CKMA.IsStrictlyMonotoneDualMap`: Strict monotonicity in the dual pairing.
* `CKMA.IsHemicontinuousDualMap`: Hemicontinuity along line segments.
* `CKMA.MapsBoundedSetsToBoundedSets`: Boundedness on bounded sets.
* `CKMA.IsCoerciveDualMap`: Coercivity in the dual pairing at infinity.
* `CKMA.SolvesVariationalInequality`: Solution predicate for a variational inequality on `C`.
* `CKMA.IsCoerciveOnAt`: Coercivity relative to a feasible point of a constraint set.

## Main results

* `CKMA.IsMonotoneGraph.resolventFiber_subsingleton`: Uniqueness of the resolvent at nonnegative
  scale.
* `CKMA.isMaximalMonotoneGraph_iff_range`: Minty's characterization of maximal monotone graphs
  (**35.32**).
* `CKMA.IsMaximalMonotoneGraph.existsUnique_resolvent`: Existence and uniqueness of the resolvent
  at positive scale.
* `CKMA.IsMonotoneDualMap.surjective`: Browder–Minty surjectivity for monotone operators on
  reflexive Banach spaces (**35.40**).
* `CKMA.IsStrictlyMonotoneDualMap.injective`: Injectivity of strictly monotone dual maps.
* `CKMA.exists_solution_variationalInequality`: Bounded-domain variational inequality existence
  (**35.45**).
* `CKMA.exists_solution_variationalInequality_of_coercive`: Unbounded-domain coercive variational
  inequality existence.

## Notation

* `⟪x, y⟫_ℝ`: Real inner product on a Hilbert space.
-/

@[expose] public section

noncomputable section

namespace CKMA

/-- A finite sum of continuous complex functions of a real variable is continuous. -/
private lemma continuous_finset_sum' {α β ι : Type*} [TopologicalSpace α] [AddCommMonoid β] [TopologicalSpace β] [ContinuousAdd β] (s : Finset ι) {f : ι → α → β}
    (hf : ∀ i ∈ s, Continuous (f i)) : Continuous (fun t ↦ ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simpa using continuous_const
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

open Filter Topology Bornology
open scoped InnerProductSpace

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Monotonicity of a Hilbert-space graph. -/
def IsMonotoneGraph (A : Set (H × H)) : Prop :=
  ∀ p ∈ A, ∀ q ∈ A, 0 ≤ ⟪p.1 - q.1, p.2 - q.2⟫_ℝ

/-- A monotone graph is maximal when it has no proper monotone enlargement. -/
def IsMaximalMonotoneGraph (A : Set (H × H)) : Prop :=
  IsMonotoneGraph A ∧ ∀ B, IsMonotoneGraph B → A ⊆ B → B ⊆ A

/-- A resolvent fiber: `y` belongs when `x ∈ y + a A(y)`.
This relation has a concrete body even before the existence theorem is proved. -/
def monotoneResolventFiber (A : Set (H × H)) (a : ℝ) (x : H) : Set H :=
  {y | ∃ u, (y, u) ∈ A ∧ x = y + a • u}

/-- Monotonicity alone makes a nonnegative-scale resolvent fiber single-valued.
This uniqueness statement does not depend on Minty's existence theorem. -/
theorem IsMonotoneGraph.resolventFiber_subsingleton {A : Set (H × H)}
    (hA : IsMonotoneGraph A) {a : ℝ} (ha : 0 ≤ a) (x : H) :
    (monotoneResolventFiber A a x).Subsingleton := by
  intro y hy z hz
  obtain ⟨u, hu, hxu⟩ := hy
  obtain ⟨v, hv, hxv⟩ := hz
  have hlinear : a • (u - v) = z - y := by
    calc
      a • (u - v) = (y + a • u) - (z + a • v) - (y - z) := by module
      _ = z - y := by rw [← hxu, ← hxv]; abel
  have hmon := hA (y, u) hu (z, v) hv
  have hscaled : 0 ≤ ⟪y - z, a • (u - v)⟫_ℝ := by
    simpa only [inner_smul_right, smul_eq_mul] using mul_nonneg ha hmon
  rw [hlinear] at hscaled
  have hneg : ⟪y - z, z - y⟫_ℝ = -(‖y - z‖ ^ 2) := by
    rw [show z - y = -(y - z) by abel, inner_neg_right, real_inner_self_eq_norm_sq]
  rw [hneg] at hscaled
  have hnorm : ‖y - z‖ = 0 := by nlinarith [sq_nonneg ‖y - z‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- A pair that is monotone against every pair of a maximal monotone graph already belongs to it. -/
private theorem IsMaximalMonotoneGraph.mem_of_monotone_with {A : Set (H × H)}
    (hA : IsMaximalMonotoneGraph A) {y u : H}
    (hmono : ∀ p ∈ A, 0 ≤ ⟪y - p.1, u - p.2⟫_ℝ) : (y, u) ∈ A := by
  let B := A ∪ {(y, u)}
  have hB : IsMonotoneGraph B := by
    intro p hp q hq
    rcases hp with hp | hp
    · rcases hq with hq | hq
      · exact hA.1 p hp q hq
      · rw [Set.mem_singleton_iff.mp hq]
        have hswap : ⟪p.1 - y, p.2 - u⟫_ℝ = ⟪y - p.1, u - p.2⟫_ℝ := by
          rw [show p.1 - y = -(y - p.1) by abel, show p.2 - u = -(u - p.2) by abel,
            inner_neg_left, inner_neg_right, neg_neg]
        rw [hswap]
        exact hmono p hp
    · rw [Set.mem_singleton_iff.mp hp]
      rcases hq with hq | hq
      · exact hmono q hq
      · rw [Set.mem_singleton_iff.mp hq]
        simp
  exact hA.2 B hB Set.subset_union_left (Set.mem_union_right _ rfl)

/-- Pairwise real inner products rearrange into a sum against the weight barycenter. -/
private theorem sum_pair_inner_eq {n : ℕ} (w : Fin n → ℝ) (v u : Fin n → H)
    (hw : ∑ i, w i = 1) :
    ∑ i, ∑ j, w i * w j * ⟪v i - v j, u i - u j⟫_ℝ =
      2 * ∑ i, w i * ⟪v i - ∑ k, w k • v k, u i⟫_ℝ := by
  have hexpand (i j : Fin n) : ⟪v i - v j, u i - u j⟫_ℝ =
      ⟪v i, u i⟫_ℝ - ⟪v i, u j⟫_ℝ - ⟪v j, u i⟫_ℝ + ⟪v j, u j⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    abel
  have hterm (i j : Fin n) : w i * w j * ⟪v i - v j, u i - u j⟫_ℝ =
      w i * w j * ⟪v i, u i⟫_ℝ - w i * w j * ⟪v i, u j⟫_ℝ -
        w i * w j * ⟪v j, u i⟫_ℝ + w i * w j * ⟪v j, u j⟫_ℝ := by
    rw [hexpand]
    ring
  have hsplit : ∑ i, ∑ j, w i * w j * ⟪v i - v j, u i - u j⟫_ℝ =
      ∑ i, ∑ j, w i * w j * ⟪v i, u i⟫_ℝ -
        ∑ i, ∑ j, w i * w j * ⟪v i, u j⟫_ℝ -
        ∑ i, ∑ j, w i * w j * ⟪v j, u i⟫_ℝ +
        ∑ i, ∑ j, w i * w j * ⟪v j, u j⟫_ℝ := by
    have hrew :
        ∑ i, ∑ j, w i * w j * ⟪v i - v j, u i - u j⟫_ℝ =
          ∑ i, ∑ j,
            (w i * w j * ⟪v i, u i⟫_ℝ - w i * w j * ⟪v i, u j⟫_ℝ -
              w i * w j * ⟪v j, u i⟫_ℝ + w i * w j * ⟪v j, u j⟫_ℝ) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      exact hterm i j
    rw [hrew]
    have hinner (i : Fin n) :
        ∑ j, (w i * w j * ⟪v i, u i⟫_ℝ - w i * w j * ⟪v i, u j⟫_ℝ -
            w i * w j * ⟪v j, u i⟫_ℝ + w i * w j * ⟪v j, u j⟫_ℝ) =
          ∑ j, w i * w j * ⟪v i, u i⟫_ℝ - ∑ j, w i * w j * ⟪v i, u j⟫_ℝ -
            ∑ j, w i * w j * ⟪v j, u i⟫_ℝ + ∑ j, w i * w j * ⟪v j, u j⟫_ℝ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp_rw [hinner]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h11 : ∑ i, ∑ j, w i * w j * ⟪v i, u i⟫_ℝ = ∑ i, w i * ⟪v i, u i⟫_ℝ := by
    simp_rw [show ∀ i j, w i * w j * ⟪v i, u i⟫_ℝ = (w i * ⟪v i, u i⟫_ℝ) * w j by
      intros; ring, ← Finset.mul_sum, hw, mul_one]
  have h22 : ∑ i, ∑ j, w i * w j * ⟪v j, u j⟫_ℝ = ∑ i, w i * ⟪v i, u i⟫_ℝ := by
    rw [Finset.sum_comm]
    simp_rw [show ∀ i j, w i * w j * ⟪v j, u j⟫_ℝ = (w j * ⟪v j, u j⟫_ℝ) * w i by
      intros; ring, ← Finset.mul_sum, hw, mul_one]
  have hcross : ∑ i, ∑ j, w i * w j * ⟪v i, u j⟫_ℝ =
      ⟪∑ i, w i • v i, ∑ j, w j • u j⟫_ℝ := by
    symm
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, inner_smul_right]
    ring
  have hcross' : ∑ i, ∑ j, w i * w j * ⟪v j, u i⟫_ℝ =
      ∑ i, ∑ j, w i * w j * ⟪v i, u j⟫_ℝ := by
    rw [Finset.sum_comm]
    simp_rw [mul_comm (w _) (w _)]
  have hdot : ⟪∑ i, w i • v i, ∑ j, w j • u j⟫_ℝ =
      ∑ i, w i * ⟪∑ k, w k • v k, u i⟫_ℝ := by
    rw [inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_right]
  have hdiff : ∑ i, w i * ⟪v i, u i⟫_ℝ - ∑ i, w i * ⟪∑ k, w k • v k, u i⟫_ℝ =
      ∑ i, w i * ⟪v i - ∑ k, w k • v k, u i⟫_ℝ := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_sub, inner_sub_left]
  rw [hsplit, h11, h22, hcross', hcross, hdot]
  have htwo : ∑ i, w i * ⟪v i, u i⟫_ℝ - ∑ i, w i * ⟪∑ k, w k • v k, u i⟫_ℝ -
      ∑ i, w i * ⟪∑ k, w k • v k, u i⟫_ℝ + ∑ i, w i * ⟪v i, u i⟫_ℝ =
      2 * (∑ i, w i * ⟪v i, u i⟫_ℝ - ∑ i, w i * ⟪∑ k, w k • v k, u i⟫_ℝ) := by
    ring
  rw [htwo, hdiff]

/-- The inequality `0 ≤ ⟪y - v, c - y⟫` cuts out the closed ball with diameter from `v` to `c`. -/
private theorem inner_nonneg_iff_mem_closedBall {v c y : H} :
    0 ≤ ⟪y - v, c - y⟫_ℝ ↔
      y ∈ Metric.closedBall ((2⁻¹ : ℝ) • (v + c)) (‖c - v‖ / 2) := by
  rw [mem_closedBall_iff_norm]
  have hm : y - (2⁻¹ : ℝ) • (v + c) = (y - v) - (2⁻¹ : ℝ) • (c - v) := by
    module
  rw [hm]
  have hrad : 0 ≤ ‖c - v‖ / 2 := div_nonneg (norm_nonneg _) zero_le_two
  rw [← sq_le_sq₀ (norm_nonneg _) hrad]
  have hexpand : ‖(y - v) - (2⁻¹ : ℝ) • (c - v)‖ ^ 2 =
      ‖y - v‖ ^ 2 - ⟪y - v, c - v⟫_ℝ + ‖c - v‖ ^ 2 / 4 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr zero_le_two)]
    ring
  have hinner : ⟪y - v, c - y⟫_ℝ = ⟪y - v, c - v⟫_ℝ - ‖y - v‖ ^ 2 := by
    rw [show c - y = (c - v) - (y - v) by abel, inner_sub_right, real_inner_self_eq_norm_sq]
  constructor
  · intro hle
    nlinarith [hexpand, hinner, hle]
  · intro hle
    nlinarith [hexpand, hinner, hle]

/-- Finitely many monotone slices meet: a simplex map fixes a convex combination in every slice. -/
private theorem exists_common_monotoneSlice {A : Set (H × H)} (hA : IsMonotoneGraph A) {a : ℝ}
    (ha : 0 < a) {n : ℕ} (hn : 0 < n) (p : Fin n → H × H) (hp : ∀ i, p i ∈ A) (x : H) :
    ∃ y, ∀ i, 0 ≤ ⟪y - (p i).1, x - y - a • (p i).2⟫_ℝ := by
  let Simplex := stdSimplex ℝ (Fin n)
  have hne : Simplex.Nonempty := ⟨Pi.single ⟨0, hn⟩ 1, single_mem_stdSimplex _ _⟩
  let bary (weight : Fin n → ℝ) : H := ∑ i, weight i • (p i).1
  let gap (weight : Fin n → ℝ) (i : Fin n) : ℝ :=
    ⟪bary weight - (p i).1, x - bary weight - a • (p i).2⟫_ℝ
  let slack (weight : Fin n → ℝ) (i : Fin n) : ℝ := max 0 (-gap weight i)
  let total (weight : Fin n → ℝ) : ℝ := ∑ i, (weight i + slack weight i)
  have htotal (s : Simplex) : 1 ≤ total s := by
    have hsum : ∑ i, (s : Fin n → ℝ) i = 1 := s.2.2
    have hslack : ∀ i, 0 ≤ slack s i := fun i => le_max_left _ _
    calc
      1 = ∑ i, (s : Fin n → ℝ) i := hsum.symm
      _ ≤ ∑ i, ((s : Fin n → ℝ) i + slack s i) := by
        gcongr with i
        exact le_add_of_nonneg_right (hslack i)
      _ = total s := rfl
  let next (s : Simplex) : Fin n → ℝ :=
    fun i => ((s : Fin n → ℝ) i + slack s i) / total s
  have hnext (s : Simplex) : next s ∈ Simplex := by
    refine ⟨fun i => div_nonneg (add_nonneg (s.2.1 i) (le_max_left _ _))
        (le_trans zero_le_one (htotal s)), ?_⟩
    have hden : total s ≠ 0 := by linarith [htotal s]
    rw [← Finset.sum_div]
    exact div_self hden
  let T : Simplex → Simplex := fun s => ⟨next s, hnext s⟩
  have hcoord (i : Fin n) : Continuous fun s : Simplex => (s : Fin n → ℝ) i :=
    (continuous_apply i).comp continuous_subtype_val
  have hbary : Continuous fun s : Simplex => bary (s : Fin n → ℝ) := by
    unfold bary
    exact continuous_finset_sum' Finset.univ fun i _ => (hcoord i).smul continuous_const
  have hgapC (i : Fin n) : Continuous fun s : Simplex => gap (s : Fin n → ℝ) i := by
    unfold gap
    exact (hbary.sub continuous_const).inner
      ((continuous_const.sub hbary).sub continuous_const)
  have hslackC (i : Fin n) : Continuous fun s : Simplex => slack (s : Fin n → ℝ) i := by
    unfold slack
    exact continuous_const.max (hgapC i).neg
  have hdenC : Continuous fun s : Simplex => total (s : Fin n → ℝ) := by
    unfold total
    exact continuous_finset_sum' Finset.univ fun i _ => (hcoord i).add (hslackC i)
  have hT : Continuous T := by
    refine Continuous.subtype_mk ?_ hnext
    exact continuous_pi fun i =>
      ((hcoord i).add (hslackC i)).div₀ hdenC fun s => by linarith [htotal s]
  let Euc := EuclideanSpace ℝ (Fin n)
  let e : Euc ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  let K : Set Euc := e.symm '' Simplex
  have hneK : K.Nonempty := by
    obtain ⟨w0, hw0⟩ := hne
    exact ⟨e.symm w0, w0, hw0, rfl⟩
  have hcompK : IsCompact K := (isCompact_stdSimplex ℝ (Fin n)).image e.symm.continuous
  have hconvK : Convex ℝ K :=
    (convex_stdSimplex ℝ (Fin n)).linear_image e.symm.toLinearMap
  have hmemK (y : K) : e y.1 ∈ Simplex := by
    obtain ⟨w0, hw0, hy⟩ := y.2
    have heq : e y.1 = w0 := by
      rw [← hy]
      simp
    simpa [heq] using hw0
  have hlift : Continuous fun y : K => (⟨e y.1, hmemK y⟩ : Simplex) :=
    Continuous.subtype_mk (e.continuous.comp continuous_subtype_val) hmemK
  have hland (y : K) : e.symm (Subtype.val (T ⟨e y.1, hmemK y⟩)) ∈ K :=
    ⟨Subtype.val (T ⟨e y.1, hmemK y⟩), (T ⟨e y.1, hmemK y⟩).2, rfl⟩
  let S : K → K := fun y => ⟨e.symm (Subtype.val (T ⟨e y.1, hmemK y⟩)), hland y⟩
  have hS : Continuous S :=
    Continuous.subtype_mk
      (e.symm.continuous.comp (continuous_subtype_val.comp (hT.comp hlift))) hland
  obtain ⟨yK, hyK⟩ := exists_fixedPoint_brouwer hneK hcompK hconvK S hS
  let s : Simplex := ⟨e yK.1, hmemK yK⟩
  have hs : T s = s := by
    apply Subtype.ext
    have happly := congrArg e (congrArg Subtype.val hyK)
    unfold S at happly
    rw [e.apply_symm_apply] at happly
    simpa [s] using happly
  have hfix : next s = (s : Fin n → ℝ) := congrArg Subtype.val hs
  let w : Fin n → ℝ := s
  have hweight : ∑ i, w i = 1 := s.2.2
  have hden : total s ≠ 0 := by linarith [htotal s]
  have hslack_eq (i : Fin n) : slack s i = w i * (total s - 1) := by
    have hi : (w i + slack s i) / total s = w i := by
      simpa [next, w] using congrFun hfix i
    rw [div_eq_iff hden] at hi
    linarith
  have hσ : total s = 1 := by
    by_contra hneσ
    have hgt : 1 < total s := lt_of_le_of_ne (htotal s) (Ne.symm hneσ)
    have hsign (i : Fin n) : w i * gap s i ≤ 0 := by
      by_cases hzi : w i = 0
      · simp [hzi]
      · have hwi : 0 < w i := lt_of_le_of_ne (s.2.1 i) (fun h => hzi h.symm)
        have hpos : 0 < slack s i := by
          rw [hslack_eq i]
          nlinarith
        have hng : 0 < -gap s i := by
          by_contra hng
          have : slack s i = 0 := by
            unfold slack
            exact max_eq_left (le_of_not_gt hng)
          linarith
        exact le_of_lt (mul_neg_of_pos_of_neg hwi (neg_pos.mp hng))
    have hsome : ∃ i, 0 < w i := by
      by_contra hall
      have hzero : ∀ i, w i = 0 := by
        intro i
        exact le_antisymm (le_of_not_gt (fun hpos => hall ⟨i, hpos⟩)) (s.2.1 i)
      have : ∑ i, w i = 0 := Finset.sum_eq_zero fun i _ => hzero i
      linarith [hweight, this]
    obtain ⟨i0, hi0⟩ := hsome
    have hstrict : w i0 * gap s i0 < 0 := by
      have hpos : 0 < slack s i0 := by
        rw [hslack_eq i0]
        nlinarith
      have hng : 0 < -gap s i0 := by
        by_contra hng
        have : slack s i0 = 0 := by
          unfold slack
          exact max_eq_left (le_of_not_gt hng)
        linarith
      exact mul_neg_of_pos_of_neg hi0 (neg_pos.mp hng)
    have hsumθ : ∑ i, w i * gap s i < 0 := by
      have hlt := Finset.sum_lt_sum (fun i _ => hsign i) ⟨i0, Finset.mem_univ _, hstrict⟩
      simpa [Finset.sum_const_zero] using hlt
    have hvanish : ∑ i, w i * ⟪bary w - (p i).1, x - bary w⟫_ℝ = 0 := by
      have hsumv : ∑ i, w i • (bary w - (p i).1) = 0 := by
        simp_rw [smul_sub, Finset.sum_sub_distrib]
        rw [← Finset.sum_smul, hweight, one_smul]
        have hbaryw : ∑ i, w i • (p i).1 = bary w := by simp [bary, w]
        rw [hbaryw, sub_self]
      have hpair : ∑ i, w i * ⟪bary w - (p i).1, x - bary w⟫_ℝ =
          ⟪∑ i, w i • (bary w - (p i).1), x - bary w⟫_ℝ := by
        rw [sum_inner]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [real_inner_smul_left]
      rw [hpair, hsumv, inner_zero_left]
    have hsplitSum : ∑ i, w i * gap s i =
        -a * ∑ i, w i * ⟪bary w - (p i).1, (p i).2⟫_ℝ := by
      have hgap_eq (i : Fin n) : gap s i = ⟪bary w - (p i).1, x - bary w⟫_ℝ -
          a * ⟪bary w - (p i).1, (p i).2⟫_ℝ := by
        unfold gap
        rw [inner_sub_right, inner_smul_right]
      simp_rw [hgap_eq, mul_sub, Finset.sum_sub_distrib, hvanish]
      simp_rw [mul_left_comm (w _) a, ← Finset.mul_sum]
      ring
    have hmono : 0 ≤ ∑ i, w i * ⟪(p i).1 - bary w, (p i).2⟫_ℝ := by
      have hpairEq := sum_pair_inner_eq w (fun i => (p i).1) (fun i => (p i).2) hweight
      have hnn : 0 ≤ ∑ i, ∑ j, w i * w j *
          ⟪(p i).1 - (p j).1, (p i).2 - (p j).2⟫_ℝ := by
        refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
        exact mul_nonneg (mul_nonneg (s.2.1 i) (s.2.1 j)) (hA _ (hp i) _ (hp j))
      have hbaryw : ∑ k, w k • (p k).1 = bary w := by simp [bary, w]
      rw [hpairEq, hbaryw] at hnn
      nlinarith
    have hnegSum : ∑ i, w i * ⟪bary w - (p i).1, (p i).2⟫_ℝ =
        -∑ i, w i * ⟪(p i).1 - bary w, (p i).2⟫_ℝ := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← neg_sub (p i).1 (bary w), inner_neg_left, mul_neg]
    have hle : ∑ i, w i * ⟪bary w - (p i).1, (p i).2⟫_ℝ ≤ 0 := by
      rw [hnegSum]
      linarith
    nlinarith [hsplitSum, hsumθ, ha, hle]
  refine ⟨bary w, fun i => ?_⟩
  have hzero : slack s i = 0 := by rw [hslack_eq i, hσ, sub_self, mul_zero]
  have hmax : max 0 (-gap s i) = 0 := by simpa [slack] using hzero
  have hgap0 : -gap s i ≤ 0 := (max_eq_left_iff).mp hmax
  simpa [gap, w] using (neg_nonpos.mp hgap0)

/-- **35.32**: Minty's characterization at each positive scale. -/
theorem isMaximalMonotoneGraph_iff_range [CompleteSpace H]
    {A : Set (H × H)} (hA : IsMonotoneGraph A) {a : ℝ} (ha : 0 < a) :
    IsMaximalMonotoneGraph A ↔ ∀ x, (monotoneResolventFiber A a x).Nonempty := by
  constructor
  · intro hmax x
    have hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ H) :=
      TauCeti.surjective_inclusionInDoubleDual_of_uniformConvexSpace
    have hneA : A.Nonempty := by
      by_contra hempty
      have hpair : (0, 0) ∈ A ∪ {(0, 0)} := Set.mem_union_right _ rfl
      have hB : IsMonotoneGraph (A ∪ {(0, 0)}) := by
        intro p hp q hq
        rcases hp with hp | hp
        · exact False.elim (hempty ⟨p, hp⟩)
        · rcases hq with hq | hq
          · exact False.elim (hempty ⟨q, hq⟩)
          · simp [show p = (0, 0) from hp, show q = (0, 0) from hq]
      have hsub := hmax.2 _ hB Set.subset_union_left hpair
      exact hempty ⟨_, hsub⟩
    let slice : A → Set H := fun q =>
      {y | 0 ≤ ⟪y - (q : H × H).1, x - y - a • (q : H × H).2⟫_ℝ}
    have hball (q : ↥A) : slice q =
        Metric.closedBall ((2⁻¹ : ℝ) • ((q : H × H).1 + (x - a • (q : H × H).2)))
          (‖(x - a • (q : H × H).2) - (q : H × H).1‖ / 2) := by
      ext y
      simp only [slice, Set.mem_setOf_eq]
      rw [show x - y - a • (q : H × H).2 = (x - a • (q : H × H).2) - y by abel]
      exact inner_nonneg_iff_mem_closedBall (v := (q : H × H).1)
        (c := x - a • (q : H × H).2) (y := y)
    have hcompact (q : ↥A) : IsCompact (toWeakSpace ℝ H '' slice q) := by
      rw [hball q]
      exact TauCeti.isCompact_toWeakSpace_closedBall hreflexive _ _
    obtain ⟨q0, hq0⟩ := hneA
    have hst (u : Finset (↥A)) :
        ((toWeakSpace ℝ H '' slice ⟨q0, hq0⟩) ∩
          ⋂ q ∈ u, toWeakSpace ℝ H '' slice q).Nonempty := by
      classical
      let qfin : Fin (u.card + 1) → H × H := fun i =>
        if h : (i : ℕ) < u.card then (u.equivFin.symm ⟨(i : ℕ), h⟩).1 else (⟨q0, hq0⟩ : ↥A)
      have hqfin : ∀ i, qfin i ∈ A := by
        intro i
        by_cases h : (i : ℕ) < u.card
        · exact (by simpa [qfin, h] using (u.equivFin.symm ⟨(i : ℕ), h⟩).1.2)
        · exact (by simpa [qfin, h] using hq0)
      obtain ⟨y, hy⟩ :=
        exists_common_monotoneSlice hA ha (Nat.succ_pos u.card) qfin hqfin x
      refine ⟨toWeakSpace ℝ H y, ?_, ?_⟩
      · have hlast : qfin (Fin.last u.card) = q0 := by
          simp [qfin, Fin.val_last]
        exact ⟨y, by simpa [slice, hlast] using hy (Fin.last u.card), rfl⟩
      · rw [Set.mem_iInter₂]
        intro q hq
        let i0 : Fin u.card := u.equivFin ⟨q, hq⟩
        let j : Fin (u.card + 1) := i0.castSucc
        have hj : (j : ℕ) < u.card := by
          have : (j : ℕ) = (i0 : ℕ) := by simp [j, Fin.val_castSucc]
          simpa [this] using i0.isLt
        have hqj : qfin j = (q : H × H) := by
          have heq : (u.equivFin.symm i0).1 = q :=
            congrArg Subtype.val (u.equivFin.symm_apply_apply ⟨q, hq⟩)
          simp [qfin, hj, j, Fin.val_castSucc, heq]
        exact ⟨y, by simpa [slice, hqj] using hy j, rfl⟩
    have hinter : (⋂ q : ↥A, toWeakSpace ℝ H '' slice q).Nonempty :=
      ((hcompact ⟨q0, hq0⟩).inter_iInter_nonempty (fun q : ↥A => toWeakSpace ℝ H '' slice q)
        (fun q => (hcompact q).isClosed) hst).imp fun _ h => h.2
    obtain ⟨zW, hzW⟩ := hinter
    let y : H := (toWeakSpace ℝ H).symm zW
    have hySlice : ∀ q : ↥A, y ∈ slice q := by
      intro q
      obtain ⟨y', hy', hzy⟩ := (Set.mem_iInter.mp hzW) q
      have hyeq : y' = y :=
        (toWeakSpace ℝ H).injective (by simpa [y] using hzy)
      exact hyeq ▸ hy'
    have hcrit : ∀ p ∈ A, 0 ≤ ⟪y - p.1, a⁻¹ • (x - y) - p.2⟫_ℝ := by
      intro p hp
      have hscale : a⁻¹ • (x - y) - p.2 = a⁻¹ • (x - y - a • p.2) := by
        calc
          a⁻¹ • (x - y) - p.2 = a⁻¹ • (x - y) - (a⁻¹ * a) • p.2 := by
            rw [inv_mul_cancel₀ ha.ne', one_smul]
          _ = a⁻¹ • (x - y) - a⁻¹ • (a • p.2) := by rw [smul_smul]
          _ = a⁻¹ • (x - y - a • p.2) := by rw [← smul_sub]
      rw [hscale, inner_smul_right]
      exact mul_nonneg (le_of_lt (inv_pos.mpr ha)) (hySlice ⟨p, hp⟩)
    refine ⟨y, a⁻¹ • (x - y), hmax.mem_of_monotone_with hcrit, ?_⟩
    rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    abel
  · intro hrange
    refine ⟨hA, fun B hB hAB z hz => ?_⟩
    obtain ⟨y, hy⟩ := hrange (z.1 + a • z.2)
    obtain ⟨u, huA, hxu⟩ := hy
    have hboth : (z.1, z.2) ∈ B ∧ (y, u) ∈ B := ⟨hz, hAB huA⟩
    have hmono := hB (z.1, z.2) hboth.1 (y, u) hboth.2
    have hlinear : a • (z.2 - u) = y - z.1 := by
      calc
        a • (z.2 - u) = (z.1 + a • z.2) - (y + a • u) - (z.1 - y) := by module
        _ = y - z.1 := by rw [← hxu]; abel
    have hscaled : 0 ≤ ⟪z.1 - y, a • (z.2 - u)⟫_ℝ := by
      simpa only [inner_smul_right, smul_eq_mul] using mul_nonneg ha.le hmono
    rw [hlinear] at hscaled
    have hneg : ⟪z.1 - y, y - z.1⟫_ℝ = -(‖z.1 - y‖ ^ 2) := by
      rw [show y - z.1 = -(z.1 - y) by abel, inner_neg_right, real_inner_self_eq_norm_sq]
    rw [hneg] at hscaled
    have hzero : z.1 = y := by
      have : ‖z.1 - y‖ = 0 := by nlinarith [sq_nonneg ‖z.1 - y‖]
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
    have hu_eq : z.2 = u := by
      have : a • (z.2 - u) = 0 := by simpa [hzero] using hlinear
      have hsub : z.2 - u = 0 := (smul_eq_zero.mp this).resolve_left ha.ne'
      exact sub_eq_zero.mp hsub
    have hzpair : z = (y, u) := Prod.ext hzero hu_eq
    rw [hzpair]
    exact huA

/-- Once a maximal monotone graph is given, every positive-scale resolvent fiber is a singleton. -/
theorem IsMaximalMonotoneGraph.existsUnique_resolvent [CompleteSpace H]
    {A : Set (H × H)} (hA : IsMaximalMonotoneGraph A) {a : ℝ} (ha : 0 < a) (x : H) :
    ∃! y, y ∈ monotoneResolventFiber A a x := by
  obtain ⟨y, hy⟩ := (isMaximalMonotoneGraph_iff_range hA.1 ha).mp hA x
  exact ⟨y, hy, fun z hz ↦ hA.1.resolventFiber_subsingleton ha.le x hz hy⟩

/-- The normal-cone graph of a convex set. Membership includes the base-point constraint. -/
def normalConeGraph (C : Set H) : Set (H × H) :=
  {p | p.1 ∈ C ∧ ∀ y ∈ C, ⟪p.2, y - p.1⟫_ℝ ≤ 0}

end Hilbert

section Banach

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Monotonicity for a map taking values in the continuous dual. -/
def IsMonotoneDualMap (A : E → StrongDual ℝ E) : Prop :=
  ∀ x y, 0 ≤ (A x - A y) (x - y)

/-- Strict monotonicity in the dual pairing. -/
def IsStrictlyMonotoneDualMap (A : E → StrongDual ℝ E) : Prop :=
  ∀ x y, x ≠ y → 0 < (A x - A y) (x - y)

/-- Hemicontinuity means continuity of every dual evaluation along each line segment. -/
def IsHemicontinuousDualMap (A : E → StrongDual ℝ E) : Prop :=
  ∀ x y z, ContinuousOn (fun t : ℝ ↦ A (x + t • y) z) (Set.Icc 0 1)

/-- Boundedness on bounded sets, without assuming global boundedness. -/
def MapsBoundedSetsToBoundedSets (A : E → StrongDual ℝ E) : Prop :=
  ∀ C : Set E, Bornology.IsBounded C → Bornology.IsBounded (A '' C)

/-- Coercivity in the dual pairing as the norm tends to infinity.
The ratio is totalized at zero, which does not affect this filter. -/
def IsCoerciveDualMap (A : E → StrongDual ℝ E) : Prop :=
  Tendsto (fun x ↦ A x x / ‖x‖) (Filter.comap (fun x : E ↦ ‖x‖) atTop) atTop

/-- **35.40**: Browder–Minty surjectivity for an everywhere-defined reflexive-Banach operator.
Reflexivity is expressed by the established bidual inclusion, as in TauCeti's weak compactness API.
  -/
theorem IsMonotoneDualMap.surjective [CompleteSpace E]
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    {A : E → StrongDual ℝ E} (hm : IsMonotoneDualMap A)
    (hh : IsHemicontinuousDualMap A) (hb : MapsBoundedSetsToBoundedSets A)
    (hc : IsCoerciveDualMap A) : Function.Surjective A := by
  sorry

/-- Strict monotonicity makes an inverse single-valued independently of existence. -/
theorem IsStrictlyMonotoneDualMap.injective {A : E → StrongDual ℝ E}
    (hA : IsStrictlyMonotoneDualMap A) : Function.Injective A := by
  intro x y hxy
  by_contra hne
  have h := hA x y hne
  simp [hxy] at h

/-- A variational inequality on `C` at forcing `f`. -/
def SolvesVariationalInequality (A : E → StrongDual ℝ E) (C : Set E)
    (f : StrongDual ℝ E) (u : E) : Prop :=
  u ∈ C ∧ ∀ v ∈ C, 0 ≤ (A u - f) (v - u)

/-- **35.45**: bounded-domain variational-inequality existence in a reflexive Banach space. -/
theorem exists_solution_variationalInequality [CompleteSpace E]
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    {A : E → StrongDual ℝ E} (hm : IsMonotoneDualMap A)
    (hh : IsHemicontinuousDualMap A) (hb : MapsBoundedSetsToBoundedSets A)
    {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C)
    (hbounded : Bornology.IsBounded C) (hc : Convex ℝ C) (f : StrongDual ℝ E) :
    ∃ u, SolvesVariationalInequality A C f u := by
  sorry

/-- Coercivity relative to a point of an unbounded constraint set. -/
def IsCoerciveOnAt (A : E → StrongDual ℝ E) (C : Set E)
    (f : StrongDual ℝ E) (u₀ : E) : Prop :=
  Tendsto (fun u ↦ (A u - f) (u - u₀) / ‖u‖)
    ((Filter.comap (fun u : E ↦ ‖u‖) atTop) ⊓ Filter.principal C) atTop

/-- The unbounded-domain version uses coercivity relative to one feasible point. -/
theorem exists_solution_variationalInequality_of_coercive [CompleteSpace E]
    (hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    {A : E → StrongDual ℝ E} (hm : IsMonotoneDualMap A)
    (hh : IsHemicontinuousDualMap A) (hb : MapsBoundedSetsToBoundedSets A)
    {C : Set E} (hclosed : IsClosed C) (hc : Convex ℝ C)
    (f : StrongDual ℝ E) {u₀ : E} (hu₀ : u₀ ∈ C) (hcoercive : IsCoerciveOnAt A C f u₀) :
    ∃ u, SolvesVariationalInequality A C f u := by
  sorry

end Banach

end CKMA
