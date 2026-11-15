/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Support

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.Algebra.Polynomial

/-!
# Orthogonal polynomial roots and Gaussian quadrature

Finite absolute moments give integrability of polynomial expressions. A nonzero
orthogonal polynomial for an infinite-support measure has distinct simple real roots
inside the convex support. An orthonormal polynomial family determines a unique
positive Gaussian quadrature rule at these roots, exact through degree `2n-1`, with
weights given by the reciprocal diagonal Christoffel kernel.

Sources: GAPS 48.6 and 48.14.

## Main definitions

* `CKMA.HasFiniteMoments`: integrability of all monomial powers `x ^ n` with respect to `μ`.
* `CKMA.IsOrthogonalPolynomial`: nonzero polynomial orthogonal to all polynomials of lower degree.
* `CKMA.IsQuadratureRule`: exactness of a quadrature rule through a given polynomial degree.
* `CKMA.christoffelKernel`: finite Christoffel kernel `∑ j ∈ range n, (p j).eval x * (p j).eval y`.

## Main results

* `CKMA.roots_orthogonalPolynomial` (**48.6**): the roots are real, distinct, simple, and lie in
  the interior of the convex hull of `μ.support`.
* `CKMA.existsUnique_gaussQuadrature` (**48.14**): existence, uniqueness, positivity, and
  reciprocal diagonal Christoffel weight formula for Gaussian quadrature at the roots of an
  orthonormal family.
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

/-- A nonzero real polynomial without real roots has a constant strict sign. -/
private lemma exists_mul_eval_pos_of_roots_eq_zero {q : ℝ[X]} (hq0 : q ≠ 0) (hq : q.roots = 0) :
    ∃ σ : ℝ, σ ≠ 0 ∧ ∀ x, 0 < σ * q.eval x := by
  have hq_eval : ∀ x, q.eval x ≠ 0 := by
    intro x hx
    have : x ∈ q.roots := (mem_roots hq0).2 hx
    simp [hq] at this
  have hsign_eq : ∀ x, SignType.sign (q.eval x) = SignType.sign (q.eval 0) := fun x ↦
    isPreconnected_univ.sign_eq_of_continuousOn q.continuousOn
      (fun z _ ↦ hq_eval z) (mem_univ x) (mem_univ 0)
  have hσ : ∀ x, 0 < (SignType.sign (q.eval 0) : ℝ) * q.eval x := by
    intro x
    rw [← hsign_eq x, sign_mul_self]
    exact abs_pos.mpr (hq_eval x)
  exact ⟨_, fun h ↦ by simpa [h] using hσ 0, hσ⟩

/-- If `s` consists of odd-multiplicity roots of `p`, and every other odd-multiplicity root lies
on one side of `K`, then `p * ∏ a ∈ s, (X - a)` has a constant weak sign on `K`. -/
private lemma exists_mul_eval_mul_prod_nonneg {p : ℝ[X]} (hp0 : p ≠ 0) {K : Set ℝ}
    {s : Finset ℝ} (hs : ∀ a ∈ s, a ∈ p.roots ∧ Odd (p.rootMultiplicity a))
    (hside : ∀ a ∈ p.roots, Odd (p.rootMultiplicity a) → a ∉ s →
      (∀ x ∈ K, 0 ≤ x - a) ∨ (∀ x ∈ K, x - a ≤ 0)) :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ z ∈ K, 0 ≤ c * (p * ∏ a ∈ s, (X - C a)).eval z := by
  classical
  obtain ⟨cof, hcof, -, hcof_roots⟩ := exists_prod_multiset_X_sub_C_mul p
  have hcof0 : cof ≠ 0 := by
    intro h
    rw [h, mul_zero] at hcof
    exact hp0 hcof.symm
  obtain ⟨σ, hσ0, hσ⟩ := exists_mul_eval_pos_of_roots_eq_zero hcof0 hcof_roots
  let Rset : Finset ℝ := p.roots.toFinset
  let oddExt : Finset ℝ := Rset.filter fun a ↦ Odd (p.rootMultiplicity a) ∧ a ∉ s
  let evenR : Finset ℝ := Rset.filter fun a ↦ Even (p.rootMultiplicity a)
  have hoddE : ∀ a ∈ oddExt, Odd (p.rootMultiplicity a) :=
    fun a ha ↦ (Finset.mem_filter.mp ha).2.1
  obtain ⟨ε, hε, hεsign⟩ := exists_weakSign_prod_sub (K := K) (t := oddExt) fun a ha ↦ by
    have ha' := Finset.mem_filter.mp ha
    exact hside a (Multiset.mem_toFinset.mp ha'.1) ha'.2.1 ha'.2.2
  have hfact : (∏ a ∈ Rset, (X - C a) ^ p.rootMultiplicity a) * cof = p := by
    simpa [Rset, Polynomial.count_roots, Finset.prod_multiset_map_count] using hcof
  have hdisj1 : Disjoint s oddExt :=
    Finset.disjoint_left.mpr fun a ha ha' ↦ (Finset.mem_filter.mp ha').2.2 ha
  have hdisj2 : Disjoint (s ∪ oddExt) evenR := by
    refine Finset.disjoint_left.mpr fun a ha ha' ↦ ?_
    have hodd : Odd (p.rootMultiplicity a) := by
      rcases Finset.mem_union.mp ha with h | h
      · exact (hs a h).2
      · exact hoddE a h
    exact Nat.not_even_iff_odd.mpr hodd (Finset.mem_filter.mp ha').2
  have hcover : Rset = s ∪ oddExt ∪ evenR := by
    ext a
    constructor
    · intro ha
      by_cases hodd : Odd (p.rootMultiplicity a)
      · by_cases hI : a ∈ s
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ hI)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨ha, hodd, hI⟩))
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨ha, Nat.not_odd_iff_even.mp hodd⟩)
    · intro ha
      simp only [Finset.mem_union] at ha
      rcases ha with (ha | ha) | ha
      · exact Multiset.mem_toFinset.mpr (hs a ha).1
      · exact (Finset.mem_filter.mp ha).1
      · exact (Finset.mem_filter.mp ha).1
  have hsplit (t : Finset ℝ) (ht : ∀ a ∈ t, Odd (p.rootMultiplicity a)) (z : ℝ) :
      ∏ a ∈ t, (z - a) ^ p.rootMultiplicity a =
        (∏ a ∈ t, (z - a) ^ (p.rootMultiplicity a - 1)) * ∏ a ∈ t, (z - a) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a ha ↦ ?_
    rw [← pow_succ, Nat.sub_add_cancel (ht a ha).pos]
  refine ⟨σ * ε, mul_ne_zero hσ0 (by rcases hε with rfl | rfl <;> norm_num), fun z hz ↦ ?_⟩
  set A : ℝ := ∏ a ∈ s, (z - a) ^ (p.rootMultiplicity a - 1)
  set B : ℝ := ∏ a ∈ s, (z - a)
  set C0 : ℝ := ∏ a ∈ oddExt, (z - a) ^ (p.rootMultiplicity a - 1)
  set D : ℝ := ∏ a ∈ oddExt, (z - a)
  set E0 : ℝ := ∏ a ∈ evenR, (z - a) ^ p.rootMultiplicity a
  set F : ℝ := cof.eval z
  have hpz : p.eval z = (A * B) * (C0 * D) * E0 * F := by
    have hprod : ∏ a ∈ Rset, (z - a) ^ p.rootMultiplicity a =
        (∏ a ∈ s, (z - a) ^ p.rootMultiplicity a) *
        (∏ a ∈ oddExt, (z - a) ^ p.rootMultiplicity a) *
        (∏ a ∈ evenR, (z - a) ^ p.rootMultiplicity a) := by
      rw [hcover, Finset.prod_union hdisj2, Finset.prod_union hdisj1]
    rw [hsplit s (fun a ha ↦ (hs a ha).2) z, hsplit oddExt hoddE z] at hprod
    have heval : p.eval z =
        (∏ a ∈ Rset, (z - a) ^ p.rootMultiplicity a) * cof.eval z := by
      conv_lhs => rw [← hfact]
      rw [eval_mul, eval_prod]
      simp [eval_pow, eval_sub, eval_X, eval_C]
    rw [heval, hprod]
  have htz : (∏ a ∈ s, (X - C a)).eval z = B := by
    simp [B, eval_prod, eval_sub, eval_X, eval_C]
  have hident : (σ * ε) * ((A * B) * (C0 * D) * E0 * F * B) =
      A * C0 * E0 * B ^ 2 * (ε * D) * (σ * F) := by ring
  rw [eval_mul, hpz, htz, hident]
  have hA : 0 ≤ A := Finset.prod_nonneg fun a ha ↦
    Even.pow_nonneg (Nat.Odd.sub_odd (hs a ha).2 odd_one) _
  have hC0 : 0 ≤ C0 := Finset.prod_nonneg fun a ha ↦
    Even.pow_nonneg (Nat.Odd.sub_odd (hoddE a ha) odd_one) _
  have hE0 : 0 ≤ E0 := Finset.prod_nonneg fun a ha ↦
    Even.pow_nonneg (Finset.mem_filter.mp ha).2 _
  have hB : 0 ≤ B ^ 2 := sq_nonneg _
  have hD : 0 ≤ ε * D := hεsign z hz
  have hF : 0 ≤ σ * F := le_of_lt (hσ z)
  positivity

/-- An orthogonal polynomial times a nonzero polynomial of lower degree has no constant weak sign
on the convex hull of the support of an infinite-support measure. -/
private lemma not_forall_nonneg_mul_eval_mul {μ : Measure ℝ} (hm : HasFiniteMoments μ)
    (hi : μ.support.Infinite) {p t : ℝ[X]} (hp : IsOrthogonalPolynomial μ p) (ht0 : t ≠ 0)
    (ht : t.natDegree < p.natDegree) {c : ℝ} (hc : c ≠ 0) :
    ¬ ∀ z ∈ convexHull ℝ μ.support, 0 ≤ c * (p * t).eval z := by
  intro hsign
  have hnn : 0 ≤ᵐ[μ] fun x ↦ c * (p * t).eval x := by
    filter_upwards [Measure.support_mem_ae] with x hx
    exact hsign x (subset_convexHull ℝ μ.support hx)
  have hzero : ∫ x, c * (p * t).eval x ∂μ = 0 := by
    rw [integral_const_mul]
    have hfun : ∫ x, (p * t).eval x ∂μ = ∫ x, p.eval x * t.eval x ∂μ := by
      refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      simp [eval_mul]
    rw [hfun, hp.2 t ht, mul_zero]
  have hgz : (fun x ↦ c * (p * t).eval x) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnn ((hm.integrable_eval (p * t)).const_mul c)).1 hzero
  have hf : (fun x ↦ (p * t).eval x) =ᵐ[μ] 0 := by
    filter_upwards [hgz] with x hx
    exact (mul_eq_zero.mp hx).resolve_left hc
  exact not_eventuallyEq_eval_zero_of_support_infinite hi (mul_ne_zero hp.1 ht0) hf

/-- **48.6**: the roots are all real, distinct, interior to the convex support, and simple. -/
theorem roots_orthogonalPolynomial (μ : Measure ℝ) (hm : HasFiniteMoments μ)
    (hi : μ.support.Infinite) {p : ℝ[X]} (hp : IsOrthogonalPolynomial μ p) :
    p.roots.toFinset.card = p.natDegree ∧ ∀ x ∈ p.roots,
      x ∈ interior (convexHull ℝ μ.support) ∧ p.rootMultiplicity x = 1 := by
  classical
  have hp0 : p ≠ 0 := hp.1
  let I : Set ℝ := interior (convexHull ℝ μ.support)
  have : DecidablePred (· ∈ I) := Classical.decPred _
  let Rset : Finset ℝ := p.roots.toFinset
  let oddInt : Finset ℝ := Rset.filter fun a ↦ Odd (p.rootMultiplicity a) ∧ a ∈ I
  have hle : oddInt.card ≤ p.natDegree := by
    calc
      oddInt.card ≤ Rset.card := Finset.card_filter_le _ _
      _ ≤ Multiset.card p.roots := p.roots.toFinset_card_le
      _ ≤ p.natDegree := p.card_roots'
  have hge : p.natDegree ≤ oddInt.card := by
    by_contra hlt
    have ht_nd : (∏ a ∈ oddInt, (X - C a)).natDegree = oddInt.card := by
      rw [natDegree_prod_of_monic oddInt (fun a ↦ X - C a) (fun _ _ ↦ monic_X_sub_C _),
        Finset.card_eq_sum_ones]
      simp
    obtain ⟨c, hc, hcsign⟩ := exists_mul_eval_mul_prod_nonneg hp0
      (K := convexHull ℝ μ.support) (s := oddInt)
      (fun a ha ↦ by
        have ha' := Finset.mem_filter.mp ha
        exact ⟨Multiset.mem_toFinset.mp ha'.1, ha'.2.1⟩)
      (fun a ha hodd hs ↦ side_of_not_mem_interior_convexHull fun hI ↦
        hs (Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr ha, hodd, hI⟩))
    exact not_forall_nonneg_mul_eval_mul hm hi hp (t := ∏ a ∈ oddInt, (X - C a))
      (monic_prod_X_sub_C (fun a : ℝ ↦ a) oddInt).ne_zero (by rw [ht_nd]; omega) hc hcsign
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

/-- The Lagrange basis at `n` distinct nodes has degree `n - 1`. -/
private lemma natDegree_lagrangeBasis_univ {n : ℕ} {x : Fin n → ℝ} (hx : Function.Injective x)
    (j : Fin n) : (Lagrange.basis Finset.univ x j).natDegree = n - 1 := by
  simpa [Finset.card_univ, Fintype.card_fin] using
    Lagrange.natDegree_basis hx.injOn (Finset.mem_univ j)

/-- A weighted node sum of `ℓⱼ * q`, with `ℓⱼ` a Lagrange basis polynomial, keeps only the
`j`th node. -/
private lemma sum_mul_eval_lagrangeBasis_mul {n : ℕ} {x : Fin n → ℝ}
    (hx : Function.Injective x) (w : Fin n → ℝ) (j : Fin n) (q : ℝ[X]) :
    ∑ i, w i * (Lagrange.basis Finset.univ x j * q).eval (x i) = w j * q.eval (x j) := by
  have hoff : ∀ i, i ≠ j → w i * (Lagrange.basis Finset.univ x j * q).eval (x i) = 0 := by
    intro i hi
    rw [eval_mul, Lagrange.eval_basis_of_ne hi.symm (Finset.mem_univ i), zero_mul, mul_zero]
  rw [Fintype.sum_eq_single j hoff, eval_mul,
    Lagrange.eval_basis_self hx.injOn (Finset.mem_univ j), one_mul]

/-- Integrating the Lagrange basis at the zeros of an orthogonal polynomial of degree `n` gives
a quadrature rule exact through degree `2n - 1`. -/
private lemma isQuadratureRule_integral_lagrangeBasis {μ : Measure ℝ} (hm : HasFiniteMoments μ)
    {P : ℝ[X]} (hP : IsOrthogonalPolynomial μ P) {n : ℕ} (hn : 0 < n) (hPn : P.natDegree = n)
    {x : Fin n → ℝ} (hx : Function.Injective x) (hroot : ∀ j, P.eval (x j) = 0) :
    IsQuadratureRule μ x (fun j ↦ ∫ t, (Lagrange.basis Finset.univ x j).eval t ∂μ)
      (2 * n - 1) := by
  have hinj : Set.InjOn x (SetLike.coe (Finset.univ : Finset (Fin n))) := hx.injOn
  intro r hr
  obtain ⟨q, s, hdiv, hq, hs⟩ := exists_quot_rem_natDegree_lt hn hPn hP.1 hr
  have hr_eval : ∀ t, r.eval t = P.eval t * q.eval t + s.eval t := by
    intro t
    simpa [eval_add, eval_mul] using congr_arg (eval t) hdiv
  have hkill : ∫ t, P.eval t * q.eval t ∂μ = 0 := hP.2 q (lt_of_lt_of_eq hq hPn.symm)
  have hint_r : ∫ t, r.eval t ∂μ = ∫ t, s.eval t ∂μ := by
    rw [integral_congr_ae (ae_of_all _ hr_eval),
      integral_add (hm.integrable_eval_mul P q) (hm.integrable_eval s), hkill, zero_add]
  have hs_deg : s.degree < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.mpr hs)
  have hs_eq : s = ∑ i, C (s.eval (x i)) * Lagrange.basis Finset.univ x i := by
    conv_lhs =>
      rw [Lagrange.eq_interpolate hinj hs_deg, Lagrange.interpolate_apply]
  have hrs : ∀ i, s.eval (x i) = r.eval (x i) := by
    intro i
    have hnode := hr_eval (x i)
    rw [hroot i, zero_mul, zero_add] at hnode
    exact hnode.symm
  have hfun : (fun t ↦ s.eval t) =
      fun t ↦ ∑ i, s.eval (x i) * (Lagrange.basis Finset.univ x i).eval t := by
    ext t
    conv_lhs => rw [hs_eq]
    rw [eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [eval_mul, eval_C]
  rw [hint_r, hfun, integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_const_mul, hrs i, mul_comm]
  · intro i _
    exact (hm.integrable_eval _).const_mul (s.eval (x i))

/-- The weights of a rule exact through degree `2n - 1` at `n` distinct nodes are the integrals
of the Lagrange basis polynomials. -/
private lemma eq_integral_lagrangeBasis_of_isQuadratureRule {μ : Measure ℝ} {n : ℕ}
    {x w : Fin n → ℝ} (hx : Function.Injective x) (hw : IsQuadratureRule μ x w (2 * n - 1))
    (j : Fin n) : w j = ∫ t, (Lagrange.basis Finset.univ x j).eval t ∂μ := by
  have hdeg : (Lagrange.basis Finset.univ x j).natDegree ≤ 2 * n - 1 := by
    rw [natDegree_lagrangeBasis_univ hx j]
    omega
  have hsum := sum_mul_eval_lagrangeBasis_mul hx w j 1
  simp only [mul_one, eval_one] at hsum
  rw [hw _ hdeg, hsum]

/-- The weights of a rule exact through degree `2n - 1` at `n` distinct nodes are positive for
an infinite-support measure. -/
private lemma pos_of_isQuadratureRule {μ : Measure ℝ} (hm : HasFiniteMoments μ)
    (hi : μ.support.Infinite) {n : ℕ} {x w : Fin n → ℝ} (hx : Function.Injective x)
    (hw : IsQuadratureRule μ x w (2 * n - 1)) (j : Fin n) : 0 < w j := by
  have hdeg : (Lagrange.basis Finset.univ x j * Lagrange.basis Finset.univ x j).natDegree ≤
      2 * n - 1 := by
    refine natDegree_mul_le.trans ?_
    rw [natDegree_lagrangeBasis_univ hx j]
    omega
  have hsum := sum_mul_eval_lagrangeBasis_mul hx w j (Lagrange.basis Finset.univ x j)
  rw [Lagrange.eval_basis_self hx.injOn (Finset.mem_univ j), mul_one] at hsum
  have hnn : ∀ t, 0 ≤
      (Lagrange.basis Finset.univ x j * Lagrange.basis Finset.univ x j).eval t := fun t ↦ by
    rw [eval_mul]
    exact mul_self_nonneg _
  have hℓ0 : Lagrange.basis Finset.univ x j ≠ 0 :=
    Lagrange.basis_ne_zero hx.injOn (Finset.mem_univ j)
  have hposint : 0 <
      ∫ t, (Lagrange.basis Finset.univ x j * Lagrange.basis Finset.univ x j).eval t ∂μ := by
    refine lt_of_le_of_ne (integral_nonneg hnn) ?_
    intro hz
    exact not_eventuallyEq_eval_zero_of_support_infinite hi (mul_ne_zero hℓ0 hℓ0)
      ((integral_eq_zero_iff_of_nonneg hnn (hm.integrable_eval _)).1 hz.symm)
  rwa [hw _ hdeg, hsum] at hposint

/-- The weights of a rule exact through degree `2n - 1` at `n` distinct nodes are the reciprocal
diagonal Christoffel kernel of an orthonormal degree-exact family. -/
private lemma eq_inv_christoffelKernel_of_isQuadratureRule {μ : Measure ℝ}
    (hm : HasFiniteMoments μ) (p : ℕ → ℝ[X]) (hd : ∀ j, (p j).natDegree = j)
    (ho : ∀ j k, ∫ x, (p j).eval x * (p k).eval x ∂μ = if j = k then 1 else 0)
    {n : ℕ} (hn : 0 < n) {x w : Fin n → ℝ} (hx : Function.Injective x)
    (hw : IsQuadratureRule μ x w (2 * n - 1)) (j : Fin n) :
    w j = (christoffelKernel p n (x j) (x j))⁻¹ := by
  have hne : ∀ j, p j ≠ 0 := ne_zero_of_orthonormal p ho
  obtain ⟨c, hc⟩ :=
    eq_sum_range_of_natDegree_le p hd hne (n - 1) (natDegree_lagrangeBasis_univ hx j).le
  rw [Nat.sub_add_cancel hn] at hc
  have hck : ∀ k ∈ Finset.range n,
      c k = ∫ t, (Lagrange.basis Finset.univ x j).eval t * (p k).eval t ∂μ := by
    intro k hk
    have hfun : (fun t ↦ (Lagrange.basis Finset.univ x j).eval t * (p k).eval t) =
        fun t ↦ ∑ m ∈ Finset.range n, c m * ((p m).eval t * (p k).eval t) := by
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
    have hdeg : (Lagrange.basis Finset.univ x j * p k).natDegree ≤ 2 * n - 1 := by
      refine natDegree_mul_le.trans ?_
      rw [natDegree_lagrangeBasis_univ hx j, hd k]
      omega
    rw [hck k hk, ← sum_mul_eval_lagrangeBasis_mul hx w j (p k), ← hw _ hdeg]
    refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
    simp [eval_mul]
  have hone : ∑ k ∈ Finset.range n, c k * (p k).eval (x j) = 1 := by
    rw [← Lagrange.eval_basis_self hx.injOn (Finset.mem_univ j), hc, eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp [eval_mul, eval_C]
  have hprod : ∑ k ∈ Finset.range n, c k * (p k).eval (x j) =
      w j * christoffelKernel p n (x j) (x j) := by
    rw [christoffelKernel, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [hckw k hk]
    ring
  exact eq_inv_of_mul_eq_one_left (hprod.symm.trans hone)

/-- **48.14**: the Gaussian rule at the roots is unique, positive, and has Christoffel weights.
The family is orthonormal, so no squared-norm factors are omitted from the kernel. -/
theorem existsUnique_gaussQuadrature (μ : Measure ℝ) (hm : HasFiniteMoments μ)
    (hi : μ.support.Infinite) (p : ℕ → ℝ[X]) (hd : ∀ j, (p j).natDegree = j)
    (ho : ∀ j k, ∫ x, (p j).eval x * (p k).eval x ∂μ = if j = k then 1 else 0)
    {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (hx : Function.Injective x)
    (hroot : ∀ j, (p n).eval (x j) = 0) :
    ∃! w : Fin n → ℝ, IsQuadratureRule μ x w (2 * n - 1) ∧
      (∀ j, 0 < w j) ∧ ∀ j, w j = (christoffelKernel p n (x j) (x j))⁻¹ := by
  have hexact := isQuadratureRule_integral_lagrangeBasis hm
    (isOrthogonalPolynomial_orthonormal hm p hd ho n) hn (hd n) hx hroot
  refine ⟨_, ⟨hexact, pos_of_isQuadratureRule hm hi hx hexact,
    eq_inv_christoffelKernel_of_isQuadratureRule hm p hd ho hn hx hexact⟩, ?_⟩
  intro w' hw'
  funext j
  exact eq_integral_lagrangeBasis_of_isQuadratureRule hx hw'.1 j

end CKMA
