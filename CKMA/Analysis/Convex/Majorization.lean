/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Rearrangement
public import Mathlib.Analysis.Convex.Birkhoff
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Strict
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Majorization, doubly stochastic mixing, and Karamata inequalities

Majorization is expressed without choosing sorting permutations: total sums agree, and every
fixed-cardinality coordinate sum is bounded by one of the same size in the majorizing vector.
This agrees with decreasing partial sums and includes empty finite index types.

The mixing characterization uses Mathlib's doubly stochastic matrices. Convex functions preserve
the resulting sum inequality; strict convexity characterizes equality by a permutation.
Sources: GAPS 11.22 and 11.24.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Finset Matrix
open scoped BigOperators

variable {n : ℕ}

/-- Majorization without a chosen sorting permutation: every `k`-coordinate sum of `x`
is bounded by some `k`-coordinate sum of `y`, and the total sums agree.
This is the usual decreasing-partial-sum definition, including `n = 0`. -/
def IsMajorizedBy (x y : Fin n → ℝ) : Prop :=
  (∑ i, x i) = ∑ i, y i ∧
    ∀ s : Finset (Fin n), ∃ t : Finset (Fin n),
      t.card = s.card ∧ (∑ i ∈ s, x i) ≤ ∑ i ∈ t, y i

/-- Majorization is reflexive. -/
theorem IsMajorizedBy.refl (x : Fin n → ℝ) : IsMajorizedBy x x :=
  ⟨rfl, fun s ↦ ⟨s, rfl, le_rfl⟩⟩

/-- Majorization is transitive. -/
theorem IsMajorizedBy.trans {x y z : Fin n → ℝ}
    (hxy : IsMajorizedBy x y) (hyz : IsMajorizedBy y z) : IsMajorizedBy x z := by
  refine ⟨hxy.1.trans hyz.1, ?_⟩
  intro s
  obtain ⟨t, ht, hst⟩ := hxy.2 s
  obtain ⟨u, hu, htu⟩ := hyz.2 t
  exact ⟨u, hu.trans ht, hst.trans htu⟩

/-- Sum of the coordinates of `f` whose `Fin` indices are among the first `k`. -/
def sumInitial (f : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ univ.filter fun i : Fin n => (i : ℕ) < k, f i

/-- Sum of `k` coordinates of `x` in the stable decreasing rearrangement. -/
def sumLargest (x : Fin n → ℝ) (k : ℕ) : ℝ :=
  sumInitial (x ∘ Tuple.sortDesc x) k

/-- The initial-segment sum is the corresponding sum over `range k`. -/
lemma sumInitial_eq_sum_range (f : Fin n → ℝ) {k : ℕ} (hk : k ≤ n) : sumInitial f k =
    ∑ i ∈ range k, if h : i < n then f ⟨i, h⟩ else 0 := by
  unfold sumInitial
  refine sum_bij (fun (i : Fin n) (_ : i ∈ _) => (i : ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    exact mem_range.mpr (mem_filter.mp hi).2
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro m hm
    have hm' : m < k := mem_range.mp hm
    exact ⟨⟨m, Nat.lt_of_lt_of_le hm' hk⟩, by simp [hm'], rfl⟩
  · intro i _
    simp [i.isLt]

/-- Once `k` meets the length, the initial-segment sum is the total sum. -/
lemma sumInitial_eq_sum_of_card_le (f : Fin n → ℝ) {k : ℕ} (hk : n ≤ k) :
    sumInitial f k = ∑ i, f i := by
  have hfilter : univ.filter (fun i : Fin n => (i : ℕ) < k) = univ := by
    ext i
    simp [Nat.lt_of_lt_of_le i.isLt hk]
  simp [sumInitial, hfilter]

/-- The initial segment of length `k ≤ n` has `k` indices. -/
lemma card_filter_val_lt {k : ℕ} (hk : k ≤ n) :
    (univ.filter fun i : Fin n => (i : ℕ) < k).card = k := by
  conv_rhs => rw [← card_range k]
  refine card_bij (fun (i : Fin n) (_ : i ∈ _) => (i : ℕ)) ?_ ?_ ?_
  · intro i hi
    exact mem_range.mpr (mem_filter.mp hi).2
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro m hm
    have hm' : m < k := mem_range.mp hm
    exact ⟨⟨m, Nat.lt_of_lt_of_le hm' hk⟩, by simp [hm'], rfl⟩

/-- An antitone tuple maximizes initial segments among subsets of the same size. -/
lemma sum_le_sumInitial_of_antitone {f : Fin n → ℝ} (hf : Antitone f) (s : Finset (Fin n)) :
    ∑ i ∈ s, f i ≤ sumInitial f s.card := by
  have hk : s.card ≤ n := by simpa [Fintype.card_fin] using s.card_le_univ
  let e := s.orderEmbOfFin rfl
  have hsum : ∑ i ∈ s, f i = ∑ i : Fin s.card, f (e i) := by
    conv_lhs => rw [← map_orderEmbOfFin_univ s rfl]
    rw [sum_map]
    refine sum_congr rfl fun i _ => ?_
    simp [e]
  have hle (i : Fin s.card) : (i : ℕ) ≤ e i := by
    have hsub : (Iio i).map e.toEmbedding ⊆ Iio (e i) := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := mem_map.mp ha
      exact mem_Iio.mpr (e.strictMono (mem_Iio.mp hb))
    simpa [card_map, Fin.card_Iio] using card_le_card hsub
  calc
    ∑ i ∈ s, f i = ∑ i : Fin s.card, f (e i) := hsum
    _ ≤ ∑ i : Fin s.card, f ⟨i, Nat.lt_of_lt_of_le i.isLt hk⟩ := by
      refine sum_le_sum fun i _ => hf ?_
      exact Fin.le_iff_val_le_val.mpr (hle i)
    _ = sumInitial f s.card := by
      rw [sumInitial_eq_sum_range f hk, ← Fin.sum_univ_eq_sum_range]
      refine sum_congr rfl fun i _ => ?_
      simp [Nat.lt_of_lt_of_le i.isLt hk]

/-- Every coordinate subset sum is at most the decreasing rearrangement of the same length. -/
lemma sum_le_sumLargest (x : Fin n → ℝ) (s : Finset (Fin n)) :
    ∑ i ∈ s, x i ≤ sumLargest x s.card := by
  let sigma := Tuple.sortDesc x
  let a := x ∘ sigma
  have ha : Antitone a := Tuple.antitone_sortDesc x
  let t := s.map sigma.symm.toEmbedding
  have hre : ∑ i ∈ s, x i = ∑ j ∈ t, a j := by
    rw [sum_map]
    refine sum_congr rfl fun i _ => ?_
    simp [a, sigma]
  calc
    ∑ i ∈ s, x i = ∑ j ∈ t, a j := hre
    _ ≤ sumInitial a t.card := sum_le_sumInitial_of_antitone ha t
    _ = sumLargest x s.card := by rw [card_map, sumLargest]

/-- Majorization bounds every decreasing partial sum. -/
lemma IsMajorizedBy.sumLargest_le {x y : Fin n → ℝ} (hxy : IsMajorizedBy x y) (k : ℕ) :
    sumLargest x k ≤ sumLargest y k := by
  rcases Nat.lt_or_ge n k with hk | hk
  · have hn : n ≤ k := hk.le
    have hsum (z : Fin n → ℝ) : sumLargest z k = ∑ i, z i := by
      rw [sumLargest, sumInitial_eq_sum_of_card_le _ hn]
      simpa using Equiv.sum_comp (Tuple.sortDesc z) z
    rw [hsum x, hsum y, hxy.1]
  · let s := (univ.filter fun i : Fin n => (i : ℕ) < k).map (Tuple.sortDesc x).toEmbedding
    have hs : s.card = k := by rw [card_map, card_filter_val_lt hk]
    have hx : sumLargest x k = ∑ i ∈ s, x i := by
      rw [sumLargest, sumInitial, sum_map]
      refine sum_congr rfl fun i _ => ?_
      simp [Function.comp_apply]
    obtain ⟨t, ht, hst⟩ := hxy.2 s
    have hty : ∑ i ∈ t, y i ≤ sumLargest y k := by
      simpa [ht, hs] using sum_le_sumLargest y t
    exact hx ▸ hst.trans hty

/-- A dot product is at most the dot product of the decreasing rearrangements. -/
lemma dotProduct_le_dotProduct_sortDesc (c x : Fin n → ℝ) :
    dotProduct c x ≤
      dotProduct (c ∘ Tuple.sortDesc c) (x ∘ Tuple.sortDesc x) := by
  let sc := Tuple.sortDesc c
  let sx := Tuple.sortDesc x
  let c' := c ∘ sc
  let x' := x ∘ sx
  have hmono : Monovary c' x' :=
    (Tuple.antitone_sortDesc c).monovary (Tuple.antitone_sortDesc x)
  have hre : ∑ i, c i * x i = ∑ i, c (sc i) * x (sc i) :=
    (Equiv.sum_comp sc fun i => c i * x i).symm
  have hpair : ∑ i, c (sc i) * x (sc i) =
      ∑ i, c' i * x' ((sx.symm * sc) i) := by
    refine sum_congr rfl fun i _ => ?_
    simp [c', x', Equiv.Perm.mul_apply]
  calc
    dotProduct c x = ∑ i, c i * x i := by simp [dotProduct]
    _ = ∑ i, c (sc i) * x (sc i) := hre
    _ = ∑ i, c' i * x' ((sx.symm * sc) i) := hpair
    _ ≤ ∑ i, c' i * x' i :=
      hmono.sum_mul_comp_perm_le_sum_mul (σ := sx.symm * sc)
    _ = dotProduct c' x' := by simp [dotProduct]

/-- The decreasing rearrangements realize the maximal permuted dot product. -/
lemma exists_dotProduct_comp_perm_eq_sortDesc (c y : Fin n → ℝ) :
    ∃ σ : Equiv.Perm (Fin n), dotProduct c (y ∘ σ) =
      dotProduct (c ∘ Tuple.sortDesc c) (y ∘ Tuple.sortDesc y) := by
  let sc := Tuple.sortDesc c
  let sy := Tuple.sortDesc y
  let sigma := sy * sc⁻¹
  refine ⟨sigma, ?_⟩
  rw [dotProduct, dotProduct]
  have hre : ∑ i, c (sc i) * (y ∘ sigma) (sc i) = ∑ i, c i * (y ∘ sigma) i :=
    Equiv.sum_comp sc fun i => c i * (y ∘ sigma) i
  rw [← hre]
  refine sum_congr rfl fun i _ => ?_
  simp [sigma, sc, sy, Function.comp_apply]

/-- Abel summation: an antitone weight favors the tuple with larger initial sums. -/
lemma dotProduct_le_of_sumInitial_le {c x y : Fin n → ℝ} (hc : Antitone c)
    (hsum : ∑ i, x i = ∑ i, y i) (hpart : ∀ k, sumInitial x k ≤ sumInitial y k) :
    dotProduct c x ≤ dotProduct c y := by
  let natOf (f : Fin n → ℝ) : ℕ → ℝ := fun i => if h : i < n then f ⟨i, h⟩ else 0
  let cd : ℕ → ℝ := natOf c
  let gd : ℕ → ℝ := fun i => natOf y i - natOf x i
  have hG (k : ℕ) (hk : k ≤ n) :
      ∑ i ∈ range k, gd i = sumInitial y k - sumInitial x k := by
    rw [sumInitial_eq_sum_range y hk, sumInitial_eq_sum_range x hk, ← sum_sub_distrib]
  have hnonneg (k : ℕ) (hk : k ≤ n) : 0 ≤ ∑ i ∈ range k, gd i := by
    rw [hG k hk]
    exact sub_nonneg.mpr (hpart k)
  have hGn : ∑ i ∈ range n, gd i = 0 := by
    rw [hG n le_rfl, sumInitial_eq_sum_of_card_le y le_rfl,
      sumInitial_eq_sum_of_card_le x le_rfl, hsum, sub_self]
  have hdiff : dotProduct c y - dotProduct c x = ∑ i ∈ range n, cd i * gd i := by
    rw [dotProduct, dotProduct, ← sum_sub_distrib]
    simp_rw [← mul_sub]
    rw [← Fin.sum_univ_eq_sum_range (fun i => cd i * gd i) n]
    refine sum_congr rfl fun i _ => ?_
    simp [cd, gd, natOf, i.isLt]
  have hAbel : 0 ≤ ∑ i ∈ range n, cd i • gd i := by
    rw [sum_range_by_parts, hGn, smul_zero, zero_sub]
    refine neg_nonneg.mpr (sum_nonpos fun i hi => ?_)
    have hi1 : i + 1 < n := by
      have hi0 : i < n - 1 := mem_range.mp hi
      omega
    have hi0 : i < n := Nat.lt_of_succ_lt hi1
    have hcd : cd (i + 1) ≤ cd i := by
      simp only [cd, natOf, hi0, hi1]
      exact hc (Fin.le_iff_val_le_val.mpr (Nat.le_succ i))
    exact smul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcd)
      (hnonneg (i + 1) (Nat.le_of_lt hi1))
  have hnonnegMul : 0 ≤ ∑ i ∈ range n, cd i * gd i := by
    simpa [smul_eq_mul] using hAbel
  exact sub_nonneg.mp (hdiff ▸ hnonnegMul)

/-- Under majorization, a dot product is at most the sorted dot product with `y`. -/
lemma IsMajorizedBy.dotProduct_sortDesc_le {x y c : Fin n → ℝ} (hxy : IsMajorizedBy x y) :
    dotProduct c x ≤
      dotProduct (c ∘ Tuple.sortDesc c) (y ∘ Tuple.sortDesc y) := by
  let c' := c ∘ Tuple.sortDesc c
  let x' := x ∘ Tuple.sortDesc x
  let y' := y ∘ Tuple.sortDesc y
  have hsum : ∑ i, x' i = ∑ i, y' i := by
    calc
      ∑ i, x' i = ∑ i, x i := by simpa [x'] using Equiv.sum_comp (Tuple.sortDesc x) x
      _ = ∑ i, y i := hxy.1
      _ = ∑ i, y' i := by
        simpa [y'] using (Equiv.sum_comp (Tuple.sortDesc y) y).symm
  have hpart (k : ℕ) : sumInitial x' k ≤ sumInitial y' k := by
    simpa [sumLargest, x', y'] using hxy.sumLargest_le k
  calc
    dotProduct c x ≤ dotProduct c' x' := dotProduct_le_dotProduct_sortDesc c x
    _ ≤ dotProduct c' y' :=
      dotProduct_le_of_sumInitial_le (Tuple.antitone_sortDesc c) hsum hpart

/-- Majorization puts `x` in the permutohedron of `y`. -/
lemma mem_convexHull_range_comp_perm_of_isMajorizedBy {x y : Fin n → ℝ}
    (hxy : IsMajorizedBy x y) :
    x ∈ convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) => y ∘ σ) := by
  let C : Set (Fin n → ℝ) := convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) => y ∘ σ)
  by_contra hxC
  have hclosed : IsClosed C :=
    (Set.finite_range fun σ : Equiv.Perm (Fin n) => y ∘ σ).isClosed_convexHull ℝ
  obtain ⟨f, u, hfC, hfu⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hclosed hxC
  let c : Fin n → ℝ := fun i => f (Pi.single i (1 : ℝ))
  have hf (z : Fin n → ℝ) : f z = dotProduct c z := by
    conv_lhs => rw [pi_eq_sum_univ' z]
    rw [map_sum]
    simp_rw [map_smul, smul_eq_mul]
    simp [dotProduct, c, mul_comm]
  obtain ⟨σ, hσ⟩ := exists_dotProduct_comp_perm_eq_sortDesc c y
  have hle : dotProduct c x ≤ dotProduct c (y ∘ σ) := by
    rw [hσ]
    exact hxy.dotProduct_sortDesc_le
  have hyσ : y ∘ σ ∈ C := subset_convexHull ℝ _ ⟨σ, rfl⟩
  have hlt : dotProduct c (y ∘ σ) < u := by simpa [hf] using hfC _ hyσ
  have hxu : u < dotProduct c x := by simpa [hf] using hfu
  exact hle.not_gt (hlt.trans hxu)

/-- **11.22**, Hardy–Littlewood–Pólya, from majorization to a doubly stochastic matrix. -/
lemma exists_doublyStochastic_of_isMajorizedBy (x y : Fin n → ℝ) (hxy : IsMajorizedBy x y) :
    ∃ D ∈ doublyStochastic ℝ (Fin n), x = D.mulVec y := by
  obtain ⟨ι, ιFin, w, z, hw0, hw1, hz, hx⟩ :=
    mem_convexHull_iff_exists_fintype.1 (mem_convexHull_range_comp_perm_of_isMajorizedBy hxy)
  let : Fintype ι := ιFin
  choose σ hσ using hz
  let D : Matrix (Fin n) (Fin n) ℝ := ∑ i, w i • (σ i).permMatrix ℝ
  have hD : D ∈ doublyStochastic ℝ (Fin n) := by
    rw [← SetLike.mem_coe]
    simpa [D] using convex_doublyStochastic.sum_mem (fun i _ => hw0 i) hw1
      (fun i _ => SetLike.mem_coe.mpr
        (permMatrix_mem_doublyStochastic (σ := σ i)))
  refine ⟨D, hD, ?_⟩
  symm
  calc
    D.mulVec y = ∑ i, (w i • (σ i).permMatrix ℝ).mulVec y := by
      simp [D, sum_mulVec]
    _ = ∑ i, w i • ((σ i).permMatrix ℝ).mulVec y := by simp_rw [smul_mulVec]
    _ = ∑ i, w i • (y ∘ σ i) := by simp_rw [permMatrix_mulVec]
    _ = ∑ i, w i • z i := by simp_rw [hσ]
    _ = x := hx

/-- A doubly stochastic image is majorized by the original vector. -/
lemma isMajorizedBy_of_mem_doublyStochastic {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : D ∈ doublyStochastic ℝ (Fin n)) (y : Fin n → ℝ) :
    IsMajorizedBy (D.mulVec y) y := by
  refine ⟨sum_mulVec_of_mem_doublyStochastic hD, ?_⟩
  intro s
  obtain ⟨w, hw0, hw1, hwM⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hD
  have hvec : D.mulVec y = ∑ σ : Equiv.Perm (Fin n), w σ • (y ∘ σ) := by
    rw [← hwM, sum_mulVec]
    simp_rw [smul_mulVec, permMatrix_mulVec]
  obtain ⟨σ0, -, hmax⟩ := univ.exists_max_image
    (fun σ : Equiv.Perm (Fin n) => ∑ i ∈ s, y (σ i)) univ_nonempty
  refine ⟨s.map σ0.toEmbedding, card_map _, ?_⟩
  calc
    ∑ i ∈ s, (D.mulVec y) i
        = ∑ i ∈ s, (∑ σ, w σ • (y ∘ σ)) i := by simp [hvec]
    _ = ∑ i ∈ s, ∑ σ, w σ * y (σ i) := by simp [Pi.smul_apply, smul_eq_mul]
    _ = ∑ σ, ∑ i ∈ s, w σ * y (σ i) := sum_comm
    _ = ∑ σ, w σ * ∑ i ∈ s, y (σ i) := by
      refine sum_congr rfl fun σ _ => ?_
      rw [← mul_sum]
    _ ≤ ∑ σ, w σ * ∑ i ∈ s, y (σ0 i) := by
      refine sum_le_sum fun σ _ => ?_
      exact mul_le_mul_of_nonneg_left (hmax σ (mem_univ σ)) (hw0 σ)
    _ = ∑ i ∈ s, y (σ0 i) := by rw [← sum_mul, hw1, one_mul]
    _ = ∑ j ∈ s.map σ0.toEmbedding, y j := by
      rw [sum_map]
      refine sum_congr rfl fun _ _ => rfl

/-- **11.22**, Hardy–Littlewood–Pólya: majorization is doubly stochastic mixing. -/
theorem isMajorizedBy_iff_exists_doublyStochastic (x y : Fin n → ℝ) :
    IsMajorizedBy x y ↔ ∃ D ∈ doublyStochastic ℝ (Fin n), x = D.mulVec y := by
  constructor
  · exact exists_doublyStochastic_of_isMajorizedBy x y
  · rintro ⟨D, hD, rfl⟩
    exact isMajorizedBy_of_mem_doublyStochastic hD y

/-- **11.24**, Karamata's inequality on any convex domain containing the coordinates. -/
theorem IsMajorizedBy.sum_convex_le {x y : Fin n → ℝ} (hxy : IsMajorizedBy x y)
    {s : Set ℝ} {φ : ℝ → ℝ} (hφ : ConvexOn ℝ s φ)
    (hx : ∀ i, x i ∈ s) (hy : ∀ i, y i ∈ s) :
    (∑ i, φ (x i)) ≤ ∑ i, φ (y i) := by
  obtain ⟨D, hD, rfl⟩ := (isMajorizedBy_iff_exists_doublyStochastic x y).mp hxy
  refine (And.intro ?_ hx).1
  calc
    ∑ i, φ ((D.mulVec y) i) ≤ ∑ i, ∑ j, D i j • φ (y j) := by
      refine sum_le_sum fun i _ => ?_
      simpa [mulVec_apply_eq_sum, smul_eq_mul] using
        hφ.map_sum_le (t := univ) (w := fun j => D i j) (p := y)
          (fun j _ => nonneg_of_mem_doublyStochastic hD)
          (sum_row_of_mem_doublyStochastic hD i) (fun j _ => hy j)
    _ = ∑ j, (∑ i, D i j) • φ (y j) := by
      rw [sum_comm]
      refine sum_congr rfl fun _ _ => sum_smul.symm
    _ = ∑ j, φ (y j) := by simp [sum_col_of_mem_doublyStochastic hD]

/-- Equal value multiplicities mean that the vectors differ by a permutation. -/
lemma exists_perm_of_forall_filter_card_eq {x y : Fin n → ℝ}
    (h : ∀ v, (univ.filter fun i => x i = v).card = (univ.filter fun i => y i = v).card) :
    ∃ σ : Equiv.Perm (Fin n), x = y ∘ σ := by
  classical
  have hflip (f : Fin n → ℝ) (v : ℝ) :
      univ.filter (fun i => f i = v) = univ.filter (fun i => v = f i) := by
    refine filter_congr fun _ _ => ?_
    exact eq_comm
  have haux (f : Fin n → ℝ) (v : ℝ) :
      Multiset.card (univ.val.filter fun i => v = f i) =
        (univ.filter fun i => f i = v).card := by
    rw [hflip f v, ← filter_val]
    simp only [card_val]
  have hmul : (List.ofFn x : Multiset ℝ) = List.ofFn y := by
    ext v
    rw [← Fin.univ_val_map x, ← Fin.univ_val_map y, Multiset.count_map, Multiset.count_map,
      haux x v, haux y v, h v]
  have hperm : List.Perm (List.ofFn (x ∘ Tuple.sortDesc x))
      (List.ofFn (y ∘ Tuple.sortDesc y)) :=
    ((Tuple.sortDesc x).ofFn_comp_perm x).trans
      ((Multiset.coe_eq_coe.mp hmul).trans ((Tuple.sortDesc y).ofFn_comp_perm y).symm)
  have hfun : x ∘ Tuple.sortDesc x = y ∘ Tuple.sortDesc y :=
    List.ofFn_injective (List.Perm.eq_of_sortedGE (Tuple.antitone_sortDesc x).sortedGE_ofFn
      (Tuple.antitone_sortDesc y).sortedGE_ofFn hperm)
  refine ⟨Tuple.sortDesc y * (Tuple.sortDesc x)⁻¹, ?_⟩
  ext i
  have happly := congr_fun hfun ((Tuple.sortDesc x)⁻¹ i)
  simpa [Equiv.Perm.mul_apply] using happly

/-- Equality for a strictly convex sum forces a permutation. -/
lemma IsMajorizedBy.eq_comp_perm_of_sum_strictConvex_eq {x y : Fin n → ℝ}
    (hxy : IsMajorizedBy x y) {s : Set ℝ} {φ : ℝ → ℝ} (hφ : StrictConvexOn ℝ s φ)
    (hx : ∀ i, x i ∈ s) (hy : ∀ i, y i ∈ s)
    (hsum : (∑ i, φ (x i)) = ∑ i, φ (y i)) :
    ∃ σ : Equiv.Perm (Fin n), x = y ∘ σ := by
  obtain ⟨D, hD, rfl⟩ := (isMajorizedBy_iff_exists_doublyStochastic x y).mp hxy
  have hxs : ∀ i, (D.mulVec y) i ∈ s := hx
  have havg (i : Fin n) : (D.mulVec y) i = ∑ j, D i j • y j := by
    simp [mulVec_apply_eq_sum, smul_eq_mul]
  have hle (i : Fin n) : φ ((D.mulVec y) i) ≤ ∑ j, D i j • φ (y j) := by
    have h := hφ.convexOn.map_sum_le (t := univ) (w := fun j => D i j) (p := y)
      (fun j _ => nonneg_of_mem_doublyStochastic hD)
      (sum_row_of_mem_doublyStochastic hD i) (fun j _ => hy j)
    simpa [havg i] using h
  have hdouble : ∑ i, ∑ j, D i j • φ (y j) = ∑ j, φ (y j) := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [← sum_smul]
    simp [sum_col_of_mem_doublyStochastic hD]
  have hzero : ∑ i, (∑ j, D i j • φ (y j) - φ ((D.mulVec y) i)) = 0 := by
    rw [sum_sub_distrib, hdouble, hsum, sub_self]
  have hnn (i : Fin n) (_ : i ∈ univ) :
      0 ≤ ∑ j, D i j • φ (y j) - φ ((D.mulVec y) i) := sub_nonneg.mpr (hle i)
  have heq (i : Fin n) : φ ((D.mulVec y) i) = ∑ j, D i j • φ (y j) :=
    (sub_eq_zero.mp ((sum_eq_zero_iff_of_nonneg hnn).mp hzero i (mem_univ i))).symm
  have hsupp (i j : Fin n) (hij : D i j ≠ 0) : y j = (D.mulVec y) i := by
    have hiff := hφ.map_sum_eq_iff' (t := univ) (w := fun j => D i j) (p := y)
      (fun j _ => nonneg_of_mem_doublyStochastic hD)
      (sum_row_of_mem_doublyStochastic hD i) (fun j _ => hy j)
    have hleft : φ (∑ j, D i j • y j) = ∑ j, D i j • φ (y j) := by
      simpa [havg i] using heq i
    simpa [havg i] using hiff.mp hleft j (mem_univ j) hij
  have hcard (v : ℝ) : (univ.filter fun i => (D.mulVec y) i = v).card =
      (univ.filter fun j => y j = v).card := by
    classical
    set xv := D.mulVec y
    set T := univ.filter fun i => xv i = v
    set S := univ.filter fun j => y j = v
    have hST (i j : Fin n) (hi : i ∉ T) (hj : j ∈ S) : D i j = 0 := by
      by_contra hDij
      have hyj : y j = xv i := hsupp i j hDij
      have hjv : y j = v := (mem_filter.mp hj).2
      exact hi (mem_filter.mpr ⟨mem_univ i, hjv ▸ hyj.symm⟩)
    have hTS (i j : Fin n) (hi : i ∈ T) (hj : j ∉ S) : D i j = 0 := by
      by_contra hDij
      have hyj : y j = xv i := hsupp i j hDij
      have hiv : xv i = v := (mem_filter.mp hi).2
      exact hj (mem_filter.mpr ⟨mem_univ j, hyj.trans hiv⟩)
    have hScard : (S.card : ℝ) = ∑ j ∈ S, ∑ i ∈ T, D i j := by
      calc
        (S.card : ℝ) = ∑ j ∈ S, (1 : ℝ) := by simp [sum_const, nsmul_eq_mul]
        _ = ∑ j ∈ S, ∑ i, D i j := by simp [sum_col_of_mem_doublyStochastic hD]
        _ = ∑ j ∈ S, ∑ i ∈ T, D i j := by
          refine sum_congr rfl fun j hj => ?_
          exact (sum_subset (subset_univ T) fun i _ hi => hST i j hi hj).symm
    have hTcard : (T.card : ℝ) = ∑ i ∈ T, ∑ j ∈ S, D i j := by
      calc
        (T.card : ℝ) = ∑ i ∈ T, (1 : ℝ) := by simp [sum_const, nsmul_eq_mul]
        _ = ∑ i ∈ T, ∑ j, D i j := by simp [sum_row_of_mem_doublyStochastic hD]
        _ = ∑ i ∈ T, ∑ j ∈ S, D i j := by
          refine sum_congr rfl fun i hi => ?_
          exact (sum_subset (subset_univ S) fun j _ hj => hTS i j hi hj).symm
    exact (Nat.cast_inj.mp (by rw [hScard, sum_comm, hTcard])).symm
  exact (And.intro (exists_perm_of_forall_filter_card_eq hcard) hxs).1

/-- Equality in strictly convex Karamata holds precisely for permutations. -/
theorem IsMajorizedBy.sum_strictConvex_eq_iff {x y : Fin n → ℝ}
    (hxy : IsMajorizedBy x y) {s : Set ℝ} {φ : ℝ → ℝ}
    (hφ : StrictConvexOn ℝ s φ) (hx : ∀ i, x i ∈ s) (hy : ∀ i, y i ∈ s) :
    (∑ i, φ (x i)) = (∑ i, φ (y i)) ↔
      ∃ σ : Equiv.Perm (Fin n), x = y ∘ σ := by
  constructor
  · exact hxy.eq_comp_perm_of_sum_strictConvex_eq hφ hx hy
  · rintro ⟨σ, rfl⟩
    exact Equiv.sum_comp σ fun i => φ (y i)

end CKMA
