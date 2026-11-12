/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Basic.Sign.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Tactic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Instances.Sign
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Orthogonal polynomial roots and Gaussian quadrature

Finite absolute moments give integrability of polynomial expressions. A nonzero
orthogonal polynomial for an infinite-support measure has distinct simple real roots
inside the convex support. An orthonormal polynomial family determines a unique
positive Gaussian quadrature rule at these roots, exact through degree `2n-1`, with
weights given by the reciprocal diagonal Christoffel kernel.

Sources: GAPS 48.6 and 48.14.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory Polynomial Set
open scoped BigOperators

/-- All polynomial moments are absolutely integrable. -/
def HasFiniteMoments (μ : Measure ℝ) : Prop := ∀ n : ℕ, Integrable (fun x ↦ x ^ n) μ

/-- Finite absolute moments include integrability of the constant function one. -/
theorem HasFiniteMoments.isFiniteMeasure {μ : Measure ℝ} (hm : HasFiniteMoments μ) :
    IsFiniteMeasure μ := by
  have h := hm 0
  simp only [pow_zero] at h
  exact (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp h

/-- A nonzero polynomial orthogonal to all polynomials of smaller degree.
Integrability is supplied separately by the moment hypothesis. -/
def IsOrthogonalPolynomial (μ : Measure ℝ) (p : ℝ[X]) : Prop :=
  p ≠ 0 ∧ ∀ q : ℝ[X], q.natDegree < p.natDegree → ∫ x, p.eval x * q.eval x ∂μ = 0

/-- Finite moments make every polynomial evaluation integrable. -/
private lemma HasFiniteMoments.integrable_eval {μ : Measure ℝ} (hm : HasFiniteMoments μ)
    (q : ℝ[X]) : Integrable (fun x ↦ q.eval x) μ := by
  have hfun : (fun x ↦ q.eval x) =
      fun x ↦ ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * x ^ i := by
    ext x
    exact q.eval_eq_sum_range x
  rw [hfun]
  refine integrable_finsetSum _ fun i _ ↦ (hm i).const_mul (q.coeff i)

/-- Finite moments make a product of polynomial evaluations integrable. -/
private lemma HasFiniteMoments.integrable_eval_mul {μ : Measure ℝ} (hm : HasFiniteMoments μ)
    (q r : ℝ[X]) : Integrable (fun x ↦ q.eval x * r.eval x) μ := by
  simpa [eval_mul] using hm.integrable_eval (q * r)

/-- A nonzero polynomial is not almost-everywhere zero for an infinite-support measure. -/
private lemma not_eventuallyEq_eval_zero_of_support_infinite {μ : Measure ℝ}
    (hi : μ.support.Infinite) {q : ℝ[X]} (hq : q ≠ 0) :
    ¬ (fun x ↦ q.eval x) =ᵐ[μ] 0 := by
  intro hzero
  have hmem : {x | q.eval x = 0} ∈ ae μ := hzero
  have hclosed : IsClosed {x | q.eval x = 0} := isClosed_eq q.continuous continuous_const
  have hsub : μ.support ⊆ {x | q.eval x = 0} :=
    Measure.support_subset_of_isClosed hclosed hmem
  have hfin : {x | q.eval x = 0}.Finite := by
    convert finite_setOfPred_isRoot hq using 1
    ext x
    simp [IsRoot.def]
  exact hi (hfin.subset hsub)

/-- A point outside the interior of a real convex hull lies to one side of that hull. -/
private lemma side_of_not_mem_interior_convexHull {s : Set ℝ} {a : ℝ}
    (ha : a ∉ interior (convexHull ℝ s)) :
    (∀ x ∈ convexHull ℝ s, 0 ≤ x - a) ∨ (∀ x ∈ convexHull ℝ s, x - a ≤ 0) := by
  have hside : s ⊆ Ici a ∨ s ⊆ Iic a := by
    by_contra h
    rw [not_or] at h
    obtain ⟨u, hu, hu_not⟩ := not_subset.mp h.1
    obtain ⟨v, hv, hv_not⟩ := not_subset.mp h.2
    have hu_lt : u < a := lt_of_not_ge (by simpa [mem_Ici] using hu_not)
    have hv_lt : a < v := lt_of_not_ge (by simpa [mem_Iic] using hv_not)
    apply ha
    rw [mem_interior]
    refine ⟨Ioo u v, ?_, isOpen_Ioo, ⟨hu_lt, hv_lt⟩⟩
    intro z hz
    have hseg : Icc u v ⊆ convexHull ℝ s :=
      (convex_convexHull ℝ s).ordConnected.out (subset_convexHull ℝ s hu)
        (subset_convexHull ℝ s hv)
    exact hseg ⟨hz.1.le, hz.2.le⟩
  rcases hside with hs | hs
  · exact Or.inl fun x hx ↦
      sub_nonneg.mpr (mem_Ici.mp (convexHull_min hs (convex_Ici a) hx))
  · exact Or.inr fun x hx ↦
      sub_nonpos.mpr (mem_Iic.mp (convexHull_min hs (convex_Iic a) hx))

/-- A finite product of real linear factors of constant weak sign has constant weak sign. -/
private lemma exists_weakSign_prod_sub {K : Set ℝ} {t : Finset ℝ}
    (ht : ∀ a ∈ t, (∀ x ∈ K, 0 ≤ x - a) ∨ (∀ x ∈ K, x - a ≤ 0)) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ x ∈ K, 0 ≤ ε * ∏ a ∈ t, (x - a) := by
  classical
  induction t using Finset.induction with
  | empty =>
    exact ⟨1, Or.inl rfl, fun _ _ ↦ by simp⟩
  | insert a s ha ih =>
    obtain ⟨ε, hε, hεs⟩ := ih fun b hb ↦ ht b (Finset.mem_insert_of_mem hb)
    rcases ht a (Finset.mem_insert_self a s) with hpos | hneg
    · refine ⟨ε, hε, fun x hx ↦ ?_⟩
      rw [Finset.prod_insert ha]
      have h1 : 0 ≤ x - a := hpos x hx
      have h2 : 0 ≤ ε * ∏ b ∈ s, (x - b) := hεs x hx
      have hmul : ε * ((x - a) * ∏ b ∈ s, (x - b)) =
          (ε * ∏ b ∈ s, (x - b)) * (x - a) := by ring
      rw [hmul]
      exact mul_nonneg h2 h1
    · refine ⟨-ε, ?_, fun x hx ↦ ?_⟩
      · rcases hε with rfl | rfl <;> simp
      · rw [Finset.prod_insert ha]
        have h1 : x - a ≤ 0 := hneg x hx
        have h2 : 0 ≤ ε * ∏ b ∈ s, (x - b) := hεs x hx
        have hmul : (-ε) * ((x - a) * ∏ b ∈ s, (x - b)) =
            (ε * ∏ b ∈ s, (x - b)) * (-(x - a)) := by ring
        rw [hmul]
        exact mul_nonneg h2 (neg_nonneg.mpr h1)

/-- Polynomials of degree at most `m` are spanned by a degree-exact family `p 0, …, p m`. -/
private lemma eq_sum_range_of_natDegree_le (p : ℕ → ℝ[X]) (hd : ∀ j, (p j).natDegree = j)
    (hne : ∀ j, p j ≠ 0) :
    ∀ m, ∀ {q : ℝ[X]}, q.natDegree ≤ m →
      ∃ c : ℕ → ℝ, q = ∑ j ∈ Finset.range (m + 1), C (c j) * p j := by
  intro m
  induction m with
  | zero =>
    intro q hq
    have hqC : q = C (q.coeff 0) := eq_C_of_natDegree_le_zero hq
    have hlead : (p 0).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (hne 0)
    have hpC : p 0 = C ((p 0).leadingCoeff) := by
      rw [leadingCoeff, hd 0]
      exact eq_C_of_natDegree_le_zero (hd 0).le
    refine ⟨fun _ ↦ q.coeff 0 / (p 0).leadingCoeff, ?_⟩
    rw [Finset.sum_range_one]
    conv_lhs => rw [hqC]
    conv_rhs =>
      rhs
      rw [hpC]
    rw [← C_mul, div_mul_cancel₀ _ hlead]
  | succ m ih =>
    intro q hq
    by_cases hle : q.natDegree ≤ m
    · obtain ⟨c, hc⟩ := ih hle
      let c' : ℕ → ℝ := fun j ↦ if j = m + 1 then 0 else c j
      refine ⟨c', ?_⟩
      have hc' : c' (m + 1) = 0 := by
        dsimp [c']
        rw [ite_eq_left rfl]
      have hsum : ∑ j ∈ Finset.range (m + 1), C (c' j) * p j =
          ∑ j ∈ Finset.range (m + 1), C (c j) * p j := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        have hj' : j ≠ m + 1 := by
          rw [Finset.mem_range] at hj
          omega
        dsimp [c']
        rw [ite_eq_right hj']
      rw [Finset.sum_range_succ, hc', map_zero, zero_mul, add_zero, hsum, hc]
    · have hdeg : q.natDegree = m + 1 := by omega
      have hq0 : q ≠ 0 := by
        intro h
        simp [h] at hdeg
      have hlead_p : (p (m + 1)).leadingCoeff ≠ 0 :=
        leadingCoeff_ne_zero.mpr (hne (m + 1))
      have hlead_q : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq0
      let a : ℝ := q.leadingCoeff / (p (m + 1)).leadingCoeff
      have ha : a ≠ 0 := div_ne_zero hlead_q hlead_p
      let u : ℝ[X] := C a * p (m + 1)
      have hdeg_u : degree u = ↑(m + 1) := by
        dsimp only [u]
        rw [degree_C_mul ha, degree_eq_natDegree (hne (m + 1)), hd]
      have hdeg_q : degree q = ↑(m + 1) := by rw [degree_eq_natDegree hq0, hdeg]
      have hlead_u : u.leadingCoeff = q.leadingCoeff := by
        dsimp only [u, a]
        rw [leadingCoeff_mul, leadingCoeff_C, div_mul_cancel₀ _ hlead_p]
      have hlt : degree (q - u) < degree q :=
        degree_sub_lt_left (hdeg_q.trans hdeg_u.symm) hq0 hlead_u.symm
      let r : ℝ[X] := q - u
      have hr : r.natDegree ≤ m := by
        by_cases hr0 : r = 0
        · simp [hr0]
        · have hlt' : r.degree < ↑(m + 1) := by simpa [r, hdeg_q] using hlt
          have : r.natDegree < m + 1 := (natDegree_lt_iff_degree_lt hr0).2 hlt'
          omega
      obtain ⟨c, hc⟩ := ih hr
      let c' : ℕ → ℝ := fun j ↦ if j = m + 1 then a else c j
      refine ⟨c', ?_⟩
      have hc' : c' (m + 1) = a := by
        dsimp [c']
        rw [ite_eq_left rfl]
      have hsum : ∑ j ∈ Finset.range (m + 1), C (c' j) * p j =
          ∑ j ∈ Finset.range (m + 1), C (c j) * p j := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        have hj' : j ≠ m + 1 := by
          rw [Finset.mem_range] at hj
          omega
        dsimp [c']
        rw [ite_eq_right hj']
      rw [Finset.sum_range_succ, hc', hsum, ← hc]
      dsimp only [r, u]
      rw [sub_add_cancel]

/-- An orthonormal polynomial is nonzero. -/
private lemma ne_zero_of_orthonormal {μ : Measure ℝ} (p : ℕ → ℝ[X])
    (ho : ∀ j k, ∫ x, (p j).eval x * (p k).eval x ∂μ = if j = k then 1 else 0) (j : ℕ) :
    p j ≠ 0 := by
  intro h
  have := ho j j
  simp [h, eval_zero, integral_zero] at this

/-- Each member of an orthonormal degree-exact family is orthogonal to lower degrees. -/
private lemma isOrthogonalPolynomial_orthonormal {μ : Measure ℝ} (hm : HasFiniteMoments μ)
    (p : ℕ → ℝ[X]) (hd : ∀ j, (p j).natDegree = j)
    (ho : ∀ j k, ∫ x, (p j).eval x * (p k).eval x ∂μ = if j = k then 1 else 0) (n : ℕ) :
    IsOrthogonalPolynomial μ (p n) := by
  have hne : ∀ j, p j ≠ 0 := ne_zero_of_orthonormal p ho
  refine ⟨hne n, fun q hq ↦ ?_⟩
  cases n with
  | zero =>
    rw [hd 0] at hq
    exact absurd hq (Nat.not_lt_zero _)
  | succ n =>
    rw [hd (n + 1)] at hq
    have hq' : q.natDegree ≤ n := Nat.le_of_lt_succ hq
    obtain ⟨c, hc⟩ := eq_sum_range_of_natDegree_le p hd hne n hq'
    have hfun : (fun x ↦ (p (n + 1)).eval x * q.eval x) =
        fun x ↦ ∑ j ∈ Finset.range (n + 1),
          c j * ((p j).eval x * (p (n + 1)).eval x) := by
      ext x
      rw [hc, eval_finsetSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp [eval_mul, eval_C]
      ring
    rw [hfun, integral_finsetSum]
    · refine Finset.sum_eq_zero fun j hj ↦ ?_
      have hjn : j ≠ n + 1 := by
        rw [Finset.mem_range] at hj
        omega
      rw [integral_const_mul, ho j (n + 1), ite_eq_right hjn, mul_zero]
    · intro j _
      simpa [eval_mul, mul_left_comm, mul_assoc] using
        (hm.integrable_eval_mul (p j) (p (n + 1))).const_mul (c j)

/-- **48.6**: the roots are all real, distinct, interior to the convex support, and simple. -/
theorem roots_orthogonalPolynomial (μ : Measure ℝ) (hm : HasFiniteMoments μ)
    (hi : μ.support.Infinite) {p : ℝ[X]} (hp : IsOrthogonalPolynomial μ p) :
    p.roots.toFinset.card = p.natDegree ∧ ∀ x ∈ p.roots,
      x ∈ interior (convexHull ℝ μ.support) ∧ p.rootMultiplicity x = 1 := by
  classical
  have hp0 : p ≠ 0 := hp.1
  let K : Set ℝ := convexHull ℝ μ.support
  let I : Set ℝ := interior K
  have : DecidablePred (· ∈ I) := Classical.decPred _
  let Rset : Finset ℝ := p.roots.toFinset
  let oddInt : Finset ℝ := Rset.filter fun a ↦ Odd (p.rootMultiplicity a) ∧ a ∈ I
  let oddExt : Finset ℝ := Rset.filter fun a ↦ Odd (p.rootMultiplicity a) ∧ a ∉ I
  let evenR : Finset ℝ := Rset.filter fun a ↦ Even (p.rootMultiplicity a)
  have hle : oddInt.card ≤ p.natDegree := by
    calc
      oddInt.card ≤ Rset.card := Finset.card_filter_le _ _
      _ ≤ Multiset.card p.roots := p.roots.toFinset_card_le
      _ ≤ p.natDegree := p.card_roots'
  have hge : p.natDegree ≤ oddInt.card := by
    by_contra hlt
    have hlt' : oddInt.card < p.natDegree := lt_of_not_ge hlt
    obtain ⟨cof, hcof, -, hcof_roots⟩ := exists_prod_multiset_X_sub_C_mul p
    have hcof0 : cof ≠ 0 := by
      intro h
      rw [h, mul_zero] at hcof
      exact hp0 hcof.symm
    have hcof_eval : ∀ x, cof.eval x ≠ 0 := by
      intro x hx
      have : x ∈ cof.roots := (mem_roots hcof0).2 hx
      simp [hcof_roots] at this
    have hsign_eq : ∀ x, SignType.sign (cof.eval x) = SignType.sign (cof.eval 0) := by
      intro x
      exact isPreconnected_univ.sign_eq_of_continuousOn cof.continuousOn
        (fun z _ ↦ hcof_eval z) (mem_univ x) (mem_univ 0)
    let σ : ℝ := SignType.sign (cof.eval 0)
    have hσ : ∀ x, 0 < σ * cof.eval x := by
      intro x
      rw [show σ = (SignType.sign (cof.eval x) : ℝ) by rw [hsign_eq x], sign_mul_self]
      exact abs_pos.mpr (hcof_eval x)
    have hside : ∀ a ∈ oddExt,
        (∀ x ∈ K, 0 ≤ x - a) ∨ (∀ x ∈ K, x - a ≤ 0) := by
      intro a ha
      exact side_of_not_mem_interior_convexHull (Finset.mem_filter.mp ha).2.2
    obtain ⟨ε, hε, hεsign⟩ := exists_weakSign_prod_sub hside
    let t : ℝ[X] := ∏ a ∈ oddInt, (X - C a)
    have ht_nd : t.natDegree = oddInt.card := by
      rw [natDegree_prod_of_monic oddInt (fun a ↦ X - C a) (fun _ _ ↦ monic_X_sub_C _),
        Finset.card_eq_sum_ones]
      simp
    have ht_lt : t.natDegree < p.natDegree := by rw [ht_nd]; exact hlt'
    have horth : ∫ x, p.eval x * t.eval x ∂μ = 0 := hp.2 t ht_lt
    have hfact : (∏ a ∈ Rset, (X - C a) ^ p.rootMultiplicity a) * cof = p := by
      simpa [Rset, Polynomial.count_roots, Finset.prod_multiset_map_count] using hcof
    have hdisj1 : Disjoint oddInt oddExt := by
      refine Finset.disjoint_left.mpr fun a ha ha' ↦ ?_
      exact (Finset.mem_filter.mp ha').2.2 (Finset.mem_filter.mp ha).2.2
    have hdisj2 : Disjoint (oddInt ∪ oddExt) evenR := by
      refine Finset.disjoint_left.mpr fun a ha ha' ↦ ?_
      have heven : Even (p.rootMultiplicity a) := (Finset.mem_filter.mp ha').2
      have hodd : Odd (p.rootMultiplicity a) := by
        rcases Finset.mem_union.mp ha with h | h
        · exact (Finset.mem_filter.mp h).2.1
        · exact (Finset.mem_filter.mp h).2.1
      exact Nat.not_even_iff_odd.mpr hodd heven
    have hcover : Rset = oddInt ∪ oddExt ∪ evenR := by
      ext a
      constructor
      · intro ha
        by_cases hodd : Odd (p.rootMultiplicity a)
        · by_cases hI : a ∈ I
          · exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_filter.mpr ⟨ha, hodd, hI⟩))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨ha, hodd, hI⟩))
        · have heven : Even (p.rootMultiplicity a) := Nat.not_odd_iff_even.mp hodd
          exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ha, heven⟩)
      · intro ha
        simp only [Finset.mem_union] at ha
        rcases ha with (ha | ha) | ha
        · exact (Finset.mem_filter.mp ha).1
        · exact (Finset.mem_filter.mp ha).1
        · exact (Finset.mem_filter.mp ha).1
    have hsplit (s : Finset ℝ) (hs : s ⊆ Rset) (hsOdd : ∀ a ∈ s, Odd (p.rootMultiplicity a))
        (z : ℝ) : ∏ a ∈ s, (z - a) ^ p.rootMultiplicity a =
          (∏ a ∈ s, (z - a) ^ (p.rootMultiplicity a - 1)) * ∏ a ∈ s, (z - a) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a ha ↦ ?_
      have haR : a ∈ p.roots := by
        simpa [Rset, Multiset.mem_toFinset] using hs ha
      have hpos : 1 ≤ p.rootMultiplicity a :=
        Nat.one_le_of_lt ((rootMultiplicity_pos hp0).2 ((mem_roots hp0).1 haR))
      nth_rw 1 [← Nat.sub_add_cancel hpos]
      rw [pow_add, pow_one]
    have hsignK : ∀ z ∈ K, 0 ≤ (σ * ε) * (p * t).eval z := by
      intro z hz
      have hsubI : oddInt ⊆ Rset := Finset.filter_subset _ _
      have hsubE : oddExt ⊆ Rset := Finset.filter_subset _ _
      have hoddI : ∀ a ∈ oddInt, Odd (p.rootMultiplicity a) :=
        fun a ha ↦ (Finset.mem_filter.mp ha).2.1
      have hoddE : ∀ a ∈ oddExt, Odd (p.rootMultiplicity a) :=
        fun a ha ↦ (Finset.mem_filter.mp ha).2.1
      set A : ℝ := ∏ a ∈ oddInt, (z - a) ^ (p.rootMultiplicity a - 1)
      set B : ℝ := ∏ a ∈ oddInt, (z - a)
      set C0 : ℝ := ∏ a ∈ oddExt, (z - a) ^ (p.rootMultiplicity a - 1)
      set D : ℝ := ∏ a ∈ oddExt, (z - a)
      set E0 : ℝ := ∏ a ∈ evenR, (z - a) ^ p.rootMultiplicity a
      set F : ℝ := cof.eval z
      have hpz : p.eval z = (A * B) * (C0 * D) * E0 * F := by
        have hprod : ∏ a ∈ Rset, (z - a) ^ p.rootMultiplicity a =
            (∏ a ∈ oddInt, (z - a) ^ p.rootMultiplicity a) *
            (∏ a ∈ oddExt, (z - a) ^ p.rootMultiplicity a) *
            (∏ a ∈ evenR, (z - a) ^ p.rootMultiplicity a) := by
          rw [hcover, Finset.prod_union hdisj2, Finset.prod_union hdisj1]
        rw [hsplit oddInt hsubI hoddI z, hsplit oddExt hsubE hoddE z] at hprod
        have heval : p.eval z =
            (∏ a ∈ Rset, (z - a) ^ p.rootMultiplicity a) * cof.eval z := by
          conv_lhs => rw [← hfact]
          rw [eval_mul, eval_prod]
          simp [eval_pow, eval_sub, eval_X, eval_C]
        rw [heval, hprod]
      have htz : t.eval z = B := by
        simp [t, B, eval_prod, eval_sub, eval_X, eval_C]
      have hmul : (p * t).eval z = p.eval z * t.eval z := eval_mul
      have hident : (σ * ε) * ((A * B) * (C0 * D) * E0 * F * B) =
          A * C0 * E0 * B ^ 2 * (ε * D) * (σ * F) := by ring
      rw [hmul, hpz, htz, hident]
      have hA : 0 ≤ A := Finset.prod_nonneg fun a ha ↦
        Even.pow_nonneg (Nat.Odd.sub_odd (hoddI a ha) odd_one) _
      have hC0 : 0 ≤ C0 := Finset.prod_nonneg fun a ha ↦
        Even.pow_nonneg (Nat.Odd.sub_odd (hoddE a ha) odd_one) _
      have hE0 : 0 ≤ E0 := Finset.prod_nonneg fun a ha ↦
        Even.pow_nonneg (Finset.mem_filter.mp ha).2 _
      have hB : 0 ≤ B ^ 2 := sq_nonneg _
      have hD : 0 ≤ ε * D := hεsign z hz
      have hF : 0 ≤ σ * F := le_of_lt (hσ z)
      positivity
    have hnn : 0 ≤ᵐ[μ] fun x ↦ (σ * ε) * (p * t).eval x := by
      filter_upwards [Measure.support_mem_ae] with x hx
      exact hsignK x (subset_convexHull ℝ μ.support hx)
    have hint : Integrable (fun x ↦ (p * t).eval x) μ := hm.integrable_eval (p * t)
    have hzero : ∫ x, (σ * ε) * (p * t).eval x ∂μ = 0 := by
      rw [integral_const_mul]
      have hfun : ∫ x, (p * t).eval x ∂μ = ∫ x, p.eval x * t.eval x ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        simp [eval_mul]
      rw [hfun, horth, mul_zero]
    have hgz : (fun x ↦ (σ * ε) * (p * t).eval x) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hnn (hint.const_mul (σ * ε))).1 hzero
    have hσε : σ * ε ≠ 0 := by
      have hσ0 : σ ≠ 0 := by
        intro h
        simpa [h] using hσ 0
      have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> simp
      exact mul_ne_zero hσ0 hε0
    have hf : (fun x ↦ (p * t).eval x) =ᵐ[μ] 0 := by
      filter_upwards [hgz] with x hx
      exact (mul_eq_zero.mp hx).resolve_left hσε
    have ht0 : t ≠ 0 := (monic_prod_X_sub_C (fun a : ℝ ↦ a) oddInt).ne_zero
    exact not_eventuallyEq_eval_zero_of_support_infinite hi (mul_ne_zero hp0 ht0) hf
  have hcard_odd : oddInt.card = p.natDegree := le_antisymm hle hge
  have hcard_R : Rset.card = p.natDegree := by
    have h1 : oddInt.card ≤ Rset.card := Finset.card_filter_le _ _
    have h2 : Rset.card ≤ p.natDegree := by
      calc
        Rset.card ≤ Multiset.card p.roots := p.roots.toFinset_card_le
        _ ≤ p.natDegree := p.card_roots'
    omega
  have hEq : oddInt = Rset :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      (hcard_R.trans hcard_odd.symm).le
  have hroots_card : Multiset.card p.roots = p.natDegree := by
    apply le_antisymm p.card_roots'
    calc
      p.natDegree = Rset.card := hcard_R.symm
      _ ≤ Multiset.card p.roots := p.roots.toFinset_card_le
  have hnodup : p.roots.Nodup :=
    Multiset.toFinset_card_eq_card_iff_nodup.mp (by rw [hcard_R, hroots_card])
  refine ⟨hcard_R, ?_⟩
  intro x hx
  have hxR : x ∈ Rset := by simpa [Rset, Multiset.mem_toFinset] using hx
  have hxO : x ∈ oddInt := by rwa [← hEq] at hxR
  have hmult : p.rootMultiplicity x = 1 := by
    rw [← count_roots]
    exact Multiset.count_eq_one_of_mem hnodup hx
  exact ⟨(Finset.mem_filter.mp hxO).2.2, hmult⟩

/-- Quotient and remainder of degree less than `n`, for a dividend of degree at most `2n - 1`. -/
private lemma exists_quot_rem_natDegree_lt {n : ℕ} (hn : 0 < n) {d r : ℝ[X]}
    (hd : d.natDegree = n) (hd0 : d ≠ 0) (hr : r.natDegree ≤ 2 * n - 1) :
    ∃ q s : ℝ[X], r = d * q + s ∧ q.natDegree < n ∧ s.natDegree < n := by
  refine ⟨r / d, r % d, (EuclideanDomain.div_add_mod r d).symm, ?_, ?_⟩
  · by_cases hle : d.degree ≤ r.degree
    · have hadd := degree_add_div hd0 hle
      have hq0 : r / d ≠ 0 :=
        mt (Polynomial.div_eq_zero_iff hd0).1 (not_lt_of_ge hle)
      have hr0 : r ≠ 0 := by
        intro hr0
        have hbot : d.degree = ⊥ :=
          le_bot_iff.mp (by simpa [hr0, degree_zero] using hle)
        exact hd0 (degree_eq_bot.1 hbot)
      have hsum : n + (r / d).natDegree = r.natDegree := by
        have hadd' := hadd
        rw [degree_eq_natDegree hd0, hd, degree_eq_natDegree hq0,
          degree_eq_natDegree hr0, ← Nat.cast_add, Nat.cast_inj] at hadd'
        exact hadd'
      omega
    · rw [(Polynomial.div_eq_zero_iff hd0).2 (lt_of_not_ge hle), natDegree_zero]
      exact hn
  · by_cases hs0 : r % d = 0
    · rw [hs0, natDegree_zero]
      exact hn
    · have hlt := degree_mod_lt r hd0
      rw [degree_eq_natDegree hd0, hd] at hlt
      exact (natDegree_lt_iff_degree_lt hs0).2 hlt

/-- Exactness of a quadrature rule through a specified polynomial degree. -/
def IsQuadratureRule {n : ℕ} (μ : Measure ℝ) (x w : Fin n → ℝ) (degree : ℕ) : Prop :=
  ∀ p : ℝ[X], p.natDegree ≤ degree → ∫ t, p.eval t ∂μ = ∑ j, w j * p.eval (x j)

/-- The finite Christoffel kernel of an orthonormal polynomial system. -/
def christoffelKernel (p : ℕ → ℝ[X]) (n : ℕ) (x y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, (p j).eval x * (p j).eval y

/-- **48.14**: the Gaussian rule at the roots is unique, positive, and has Christoffel weights.
The family is orthonormal, so no squared-norm factors are omitted from the kernel. -/
theorem existsUnique_gaussQuadrature (μ : Measure ℝ) (hm : HasFiniteMoments μ)
    (hi : μ.support.Infinite) (p : ℕ → ℝ[X]) (hd : ∀ j, (p j).natDegree = j)
    (ho : ∀ j k, ∫ x, (p j).eval x * (p k).eval x ∂μ = if j = k then 1 else 0)
    {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (hx : Function.Injective x)
    (hroot : ∀ j, (p n).eval (x j) = 0) :
    ∃! w : Fin n → ℝ, IsQuadratureRule μ x w (2 * n - 1) ∧
      (∀ j, 0 < w j) ∧ ∀ j, w j = (christoffelKernel p n (x j) (x j))⁻¹ := by
  have hne : ∀ j, p j ≠ 0 := ne_zero_of_orthonormal p ho
  have horth : IsOrthogonalPolynomial μ (p n) :=
    isOrthogonalPolynomial_orthonormal hm p hd ho n
  have hroots := roots_orthogonalPolynomial μ hm hi horth
  have hnodes : Finset.univ.image x = (p n).roots.toFinset := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro y hy
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
      exact Multiset.mem_toFinset.mpr ((mem_roots (hne n)).2 (hroot j))
    · have hEq : (Finset.univ.image x).card = (p n).roots.toFinset.card := by
        rw [Finset.card_image_of_injective _ hx, Finset.card_univ, Fintype.card_fin,
          hroots.1, hd n]
      exact hEq.symm.le
  have hcard : (Finset.univ : Finset (Fin n)).card = (p n).roots.toFinset.card := by
    calc
      (Finset.univ : Finset (Fin n)).card = (Finset.univ.image x).card :=
        (Finset.card_image_of_injective Finset.univ hx).symm
      _ = (p n).roots.toFinset.card := by simp [hnodes]
  let ℓ : Fin n → ℝ[X] := fun j ↦ Lagrange.basis Finset.univ x j
  let w : Fin n → ℝ := fun j ↦ ∫ t, (ℓ j).eval t ∂μ
  have hinj : Set.InjOn x (SetLike.coe (Finset.univ : Finset (Fin n))) := by
    intro a _ b _ hxy
    exact hx hxy
  have hℓnd : ∀ j, (ℓ j).natDegree = n - 1 := fun j ↦ by
    simpa [ℓ, Finset.card_univ, Fintype.card_fin] using
      Lagrange.natDegree_basis hinj (Finset.mem_univ j)
  have hℓself : ∀ j, (ℓ j).eval (x j) = 1 := fun j ↦ by
    simpa [ℓ] using Lagrange.eval_basis_self hinj (Finset.mem_univ j)
  have hℓne : ∀ i j, i ≠ j → (ℓ i).eval (x j) = 0 := fun i j hij ↦ by
    simpa [ℓ] using Lagrange.eval_basis_of_ne hij (Finset.mem_univ j)
  have hℓ0 : ∀ j, ℓ j ≠ 0 := fun j ↦ by
    simpa [ℓ] using Lagrange.basis_ne_zero hinj (Finset.mem_univ j)
  have hexact : IsQuadratureRule μ x w (2 * n - 1) := by
    intro r hr
    obtain ⟨q, s, hdiv, hq, hs⟩ :=
      exists_quot_rem_natDegree_lt hn (hd n) (hne n) hr
    have hr_eval : ∀ t, r.eval t = (p n).eval t * q.eval t + s.eval t := by
      intro t
      simpa [eval_add, eval_mul] using congr_arg (eval t) hdiv
    have hkill : ∫ t, (p n).eval t * q.eval t ∂μ = 0 :=
      horth.2 q (lt_of_lt_of_eq hq (hd n).symm)
    have hint_r : ∫ t, r.eval t ∂μ = ∫ t, s.eval t ∂μ := by
      have hadd :=
        integral_add (hm.integrable_eval_mul (p n) q) (hm.integrable_eval s)
      rw [integral_congr_ae (ae_of_all _ hr_eval), hadd, hkill, zero_add]
    have hs_deg : s.degree < (Finset.univ : Finset (Fin n)).card := by
      rw [hcard, hroots.1, hd n]
      exact lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.mpr hs)
    have hs_eq : s = ∑ i, C (s.eval (x i)) * ℓ i := by
      conv_lhs =>
        rw [Lagrange.eq_interpolate hinj hs_deg, Lagrange.interpolate_apply]
    have hrs : ∀ i, s.eval (x i) = r.eval (x i) := by
      intro i
      have hnode := hr_eval (x i)
      rw [hroot i, zero_mul, zero_add] at hnode
      exact hnode.symm
    have hfun : (fun t ↦ s.eval t) =
        fun t ↦ ∑ i, s.eval (x i) * (ℓ i).eval t := by
      ext t
      conv_lhs => rw [hs_eq]
      rw [eval_finsetSum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [eval_mul, eval_C]
    rw [hint_r, hfun, integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [integral_const_mul, hrs i, mul_comm]
    · intro i _
      exact (hm.integrable_eval (ℓ i)).const_mul (s.eval (x i))
  have hpos : ∀ j, 0 < w j := by
    intro j
    have hdeg : (ℓ j ^ 2).natDegree ≤ 2 * n - 1 := by
      calc
        (ℓ j ^ 2).natDegree ≤ 2 * (ℓ j).natDegree := natDegree_pow_le
        _ = 2 * (n - 1) := by rw [hℓnd j]
        _ ≤ 2 * n - 1 := by omega
    have hint := hexact (ℓ j ^ 2) hdeg
    have hoff : ∀ i, i ≠ j → w i * (ℓ j ^ 2).eval (x i) = 0 := by
      intro i hi
      rw [eval_pow, hℓne j i hi.symm, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
    have hsum : ∑ i, w i * (ℓ j ^ 2).eval (x i) = w j := by
      rw [Fintype.sum_eq_single j hoff, eval_pow, hℓself j, one_pow, mul_one]
    have hnn : ∀ t, 0 ≤ (ℓ j ^ 2).eval t := by
      intro t
      rw [eval_pow]
      exact sq_nonneg _
    have hintg : Integrable (fun t ↦ (ℓ j ^ 2).eval t) μ := hm.integrable_eval _
    have hposint : 0 < ∫ t, (ℓ j ^ 2).eval t ∂μ := by
      refine lt_of_le_of_ne (integral_nonneg hnn) ?_
      intro hz
      exact not_eventuallyEq_eval_zero_of_support_infinite hi
        (pow_ne_zero 2 (hℓ0 j))
        ((integral_eq_zero_iff_of_nonneg hnn hintg).1 hz.symm)
    rw [hint, hsum] at hposint
    exact hposint
  have hchrist : ∀ j, w j = (christoffelKernel p n (x j) (x j))⁻¹ := by
    intro j
    obtain ⟨c, hc⟩ :=
      eq_sum_range_of_natDegree_le p hd hne (n - 1) (hℓnd j).le
    have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
    rw [hn1] at hc
    have hck : ∀ k ∈ Finset.range n,
        c k = ∫ t, (ℓ j).eval t * (p k).eval t ∂μ := by
      intro k hk
      have hfun : (fun t ↦ (ℓ j).eval t * (p k).eval t) =
          fun t ↦ ∑ m ∈ Finset.range n,
            c m * ((p m).eval t * (p k).eval t) := by
        ext t
        rw [hc, eval_finsetSum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ ↦ ?_
        simp [eval_mul, eval_C, mul_assoc]
      rw [hfun, integral_finsetSum]
      · rw [Finset.sum_eq_single_of_mem k hk]
        · rw [integral_const_mul, ho k k, ite_eq_left rfl, mul_one]
        · intro m _ hmk
          rw [integral_const_mul, ho m k, ite_eq_right hmk, mul_zero]
      · intro m _
        exact (hm.integrable_eval_mul (p m) (p k)).const_mul (c m)
    have hckw : ∀ k ∈ Finset.range n, c k = w j * (p k).eval (x j) := by
      intro k hk
      have hklt : k < n := Finset.mem_range.mp hk
      have hdeg : ((ℓ j) * p k).natDegree ≤ 2 * n - 1 := by
        calc
          ((ℓ j) * p k).natDegree ≤ (ℓ j).natDegree + (p k).natDegree :=
            natDegree_mul_le
          _ = (n - 1) + k := by rw [hℓnd j, hd k]
          _ ≤ 2 * n - 1 := by omega
      rw [hck k hk]
      have hint := hexact (ℓ j * p k) hdeg
      have hfun : ∫ t, (ℓ j).eval t * (p k).eval t ∂μ =
          ∫ t, ((ℓ j) * p k).eval t ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
        simp [eval_mul]
      rw [hfun, hint]
      have hoff : ∀ i, i ≠ j → w i * ((ℓ j) * p k).eval (x i) = 0 := by
        intro i hi
        rw [eval_mul, hℓne j i hi.symm, zero_mul, mul_zero]
      rw [Fintype.sum_eq_single j hoff, eval_mul, hℓself j, one_mul]
    have hone : ∑ k ∈ Finset.range n, c k * (p k).eval (x j) = 1 := by
      rw [← hℓself j, hc, eval_finsetSum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp [eval_mul, eval_C]
    have hprod : ∑ k ∈ Finset.range n, c k * (p k).eval (x j) =
        w j * christoffelKernel p n (x j) (x j) := by
      rw [christoffelKernel, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [hckw k hk]
      ring
    exact eq_inv_of_mul_eq_one_left (hprod.symm.trans hone)
  refine ExistsUnique.intro w ⟨hexact, hpos, hchrist⟩ ?_
  intro w' hw'
  funext j
  have hdeg : (ℓ j).natDegree ≤ 2 * n - 1 := by
    rw [hℓnd j]
    omega
  have hoff : ∀ i, i ≠ j → w' i * (ℓ j).eval (x i) = 0 := by
    intro i hi
    rw [hℓne j i hi.symm, mul_zero]
  have hsum : ∑ i, w' i * (ℓ j).eval (x i) = w' j := by
    rw [Fintype.sum_eq_single j hoff, hℓself j, mul_one]
  change w' j = ∫ t, (ℓ j).eval t ∂μ
  rw [hw'.1 (ℓ j) hdeg, hsum]

end CKMA
