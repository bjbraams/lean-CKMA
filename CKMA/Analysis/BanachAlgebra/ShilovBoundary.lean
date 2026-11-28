/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Compact

import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The Shilov boundary of a uniform algebra

For a subalgebra `A` of `C(K, ℂ)` on a compact Hausdorff space `K`, a closed norming boundary is a
closed set `F ⊆ K` on which every `f ∈ A` attains its supremum norm, with the convention
`sSup ∅ = 0` that also covers the zero algebra on the empty carrier. If `A` separates the points
of `K`, the intersection of all closed norming boundaries is again one: the Shilov boundary, as in
Bonsall–Duncan.
Source: GAPS 20.23.

## Main definitions

* `CKMA.IsUniformAlgebraBoundary`: closed norming boundary for a subalgebra of `C(K, ℂ)`.

## Main results

* `CKMA.isUniformAlgebraBoundary_iff`: defining lemma.
* `CKMA.exists_shilov_boundary`: existence of the smallest closed norming boundary.
-/

public section

noncomputable section

namespace CKMA

open Filter Topology

/-- A closed boundary for a uniform algebra, using the supremum convention that also
allows the zero algebra on the empty compact space. -/
@[expose]
def IsUniformAlgebraBoundary {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (A : Subalgebra ℂ C(K, ℂ)) (F : Set K) : Prop :=
  IsClosed F ∧ ∀ f : A, ‖f.1‖ = sSup ((fun x ↦ ‖f.1 x‖) '' F)

/-- Defining property of `IsUniformAlgebraBoundary`: `F` is closed and every `f ∈ A` has sup norm
equal to the supremum of `‖f x‖` over `x ∈ F`. -/
theorem isUniformAlgebraBoundary_iff {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {A : Subalgebra ℂ C(K, ℂ)} {F : Set K} :
    IsUniformAlgebraBoundary A F ↔
      IsClosed F ∧ ∀ f : A, ‖f.1‖ = sSup ((fun x ↦ ‖f.1 x‖) '' F) :=
  Iff.rfl

/-- The supremum of a norm on any set is at most the supremum norm. -/
private theorem sSup_norm_image_le {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {A : Subalgebra ℂ C(K, ℂ)} (f : A) (F : Set K) :
    sSup ((fun x => ‖f.1 x‖) '' F) ≤ ‖f.1‖ := by
  by_cases hF : ((fun x => ‖f.1 x‖) '' F).Nonempty
  · exact csSup_le hF fun r hr => by
      obtain ⟨x, -, rfl⟩ := hr
      exact f.1.norm_coe_le_norm x
  · rw [Set.not_nonempty_iff_eq_empty] at hF
    rw [hF, Real.sSup_empty]
    exact norm_nonneg _

/-- Norms are nonnegative, so their supremum on any set is nonnegative. -/
private theorem sSup_norm_image_nonneg {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {A : Subalgebra ℂ C(K, ℂ)} (f : A) (F : Set K) :
    0 ≤ sSup ((fun x => ‖f.1 x‖) '' F) := by
  by_cases hF : ((fun x => ‖f.1 x‖) '' F).Nonempty
  · obtain ⟨r, hr⟩ := hF
    obtain ⟨x, hx, rfl⟩ := hr
    exact (norm_nonneg (f.1 x)).trans <| le_csSup
      ⟨‖f.1‖, fun t ht => by
        obtain ⟨y, -, rfl⟩ := ht
        exact f.1.norm_coe_le_norm y⟩ ⟨x, hx, rfl⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hF
    rw [hF, Real.sSup_empty]

/-- On a compact carrier the supremum norm is the supremum of the pointwise norms. -/
private theorem norm_eq_sSup_univ {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (f : C(K, ℂ)) : ‖f‖ = sSup ((fun x => ‖f x‖) '' Set.univ) := by
  rw [ContinuousMap.norm_eq_iSup_norm, iSup, ← Set.image_univ]

/-- The whole carrier is a closed norming boundary. -/
private theorem isUniformAlgebraBoundary_univ {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (A : Subalgebra ℂ C(K, ℂ)) : IsUniformAlgebraBoundary A Set.univ :=
  ⟨isClosed_univ, fun f => norm_eq_sSup_univ f.1⟩

/-- Pointwise norm of a power times another algebra element. -/
private theorem norm_pow_mul_apply {K : Type*} [TopologicalSpace K]
    {A : Subalgebra ℂ C(K, ℂ)} (g f : A) (n : ℕ) (z : K) :
    ‖((g ^ n * f).1 z)‖ = ‖g.1 z‖ ^ n * ‖f.1 z‖ := by
  rw [Subalgebra.coe_mul, Subalgebra.coe_pow, ContinuousMap.mul_apply,
    ContinuousMap.pow_apply, norm_mul, norm_pow]

/-- A strict pointwise bound on a compact set is a strict bound on the supremum. -/
private theorem sSup_norm_image_lt {K : Type*} [TopologicalSpace K]
    {E : Set K} (hE : IsCompact E) {g : C(K, ℂ)} {c : ℝ} (hc : 0 < c)
    (hlt : ∀ x ∈ E, ‖g x‖ < c) : sSup ((fun x => ‖g x‖) '' E) < c := by
  by_cases hne : E.Nonempty
  · obtain ⟨x, hx, heq⟩ := hE.exists_sSup_image_eq hne
      ((continuous_norm.comp g.continuous).continuousOn (s := E))
    have hfun : (fun a : ℂ => ‖a‖) ∘ ⇑g = fun x => ‖g x‖ := funext fun _ => rfl
    rw [hfun] at heq
    rw [heq]
    exact hlt x hx
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.image_empty, Real.sSup_empty]
    exact hc

/-- A nonempty boundary attains the supremum norm of every algebra element. -/
private theorem exists_norm_eq_on_boundary {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {A : Subalgebra ℂ C(K, ℂ)} {E : Set K} (hE : IsUniformAlgebraBoundary A E)
    (hEne : E.Nonempty) (g : A) : ∃ z ∈ E, ‖g.1 z‖ = ‖g.1‖ := by
  obtain ⟨z, hz, heq⟩ := hE.1.isCompact.exists_sSup_image_eq hEne
    ((continuous_norm.comp g.1.continuous).continuousOn (s := E))
  have hfun : (fun a : ℂ => ‖a‖) ∘ ⇑(g.1) = fun x => ‖g.1 x‖ :=
    funext fun _ => rfl
  rw [hfun] at heq
  exact ⟨z, hz, heq.symm.trans (hE.2 g).symm⟩

/-- The carrierwise point-separation hypothesis is separation of points for the algebra. -/
private theorem separatesPoints_of_point_separation {K : Type*} [TopologicalSpace K]
    {A : Subalgebra ℂ C(K, ℂ)}
    (hsep : ∀ x y : K, x ≠ y → ∃ f : A, f.1 x ≠ f.1 y) : A.SeparatesPoints := by
  intro x y hxy
  obtain ⟨f, hf⟩ := hsep x y hxy
  exact ⟨⇑(f.1), ⟨f.1, f.property, rfl⟩, hf⟩

/-- Folding set differences cannot restore a point that starts outside or meets a deleted set. -/
private theorem notMem_foldl_sdiff {α β : Type*} (l : List α) (U : α → Set β) (E : Set β)
    {z : β} (h : z ∉ E ∨ ∃ i ∈ l, z ∈ U i) :
    z ∉ l.foldl (fun G i => G \ U i) E := by
  induction l generalizing E with
  | nil =>
    cases h with
    | inl hz => exact hz
    | inr hex =>
      obtain ⟨_, hi, _⟩ := hex
      cases hi
  | cons a as ih =>
    dsimp only [List.foldl]
    refine ih (E \ U a) ?_
    cases h with
    | inl hz => exact Or.inl fun hz' => hz hz'.1
    | inr hex =>
      obtain ⟨i, hi, hz⟩ := hex
      rcases List.mem_cons.mp hi with hia | hias
      · subst hia
        exact Or.inl fun hz' => hz'.2 hz
      · exact Or.inr ⟨i, hias, hz⟩

/-- Deleting sets that preserve boundaries, one at a time, leaves a boundary. -/
private theorem boundary_foldl_sdiff {K α : Type*} [TopologicalSpace K] [CompactSpace K]
    (A : Subalgebra ℂ C(K, ℂ)) (l : List α) (U : α → Set K)
    (hdel : ∀ i ∈ l, ∀ E, IsUniformAlgebraBoundary A E →
      IsUniformAlgebraBoundary A (E \ U i))
    {E : Set K} (hE : IsUniformAlgebraBoundary A E) :
    IsUniformAlgebraBoundary A (l.foldl (fun G i => G \ U i) E) := by
  induction l generalizing E with
  | nil => exact hE
  | cons i is ih =>
    dsimp only [List.foldl]
    exact ih (fun j hj F hF => hdel j (List.mem_cons.mpr (Or.inr hj)) F hF)
      (hdel i (List.mem_cons.mpr (Or.inl rfl)) E hE)

/-- On a nonempty carrier every closed boundary is nonempty, since it norms the unit. -/
private theorem IsUniformAlgebraBoundary.nonempty {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [Nonempty K] {A : Subalgebra ℂ C(K, ℂ)} {E : Set K}
    (hE : IsUniformAlgebraBoundary A E) : E.Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hsup := hE.2 (1 : A)
  rw [hempty, Set.image_empty, Real.sSup_empty, Subalgebra.coe_one] at hsup
  have hnorm : ‖(1 : C(K, ℂ))‖ = 1 := by
    rw [ContinuousMap.norm_eq_iSup_norm]
    have hpt : ∀ x : K, ‖(1 : C(K, ℂ)) x‖ = 1 := fun x => by
      rw [ContinuousMap.one_apply, norm_one]
    simp only [hpt]
    exact ciSup_const
  exact one_ne_zero (hnorm.symm.trans hsup)

/-- If `0 ≤ ρ < N` and `0 < M`, then `ρ ^ n * M < N ^ n` for some exponent `n`. -/
private theorem exists_pow_mul_lt_pow {ρ N M : ℝ} (hρ : 0 ≤ ρ) (hρN : ρ < N) (hM : 0 < M) :
    ∃ n : ℕ, ρ ^ n * M < N ^ n := by
  have hNpos : 0 < N := hρ.trans_lt hρN
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (one_div_pos.mpr hM) ((div_lt_one hNpos).mpr hρN)
  have hlt1 : (ρ / N) ^ n * M < 1 := by
    calc
      (ρ / N) ^ n * M < (1 / M) * M := mul_lt_mul_of_pos_right hn hM
      _ = 1 := by rw [one_div, inv_mul_cancel₀ hM.ne']
  refine ⟨n, ?_⟩
  have hrewrite : ρ ^ n * M = (ρ / N) ^ n * M * N ^ n := by
    rw [div_pow, div_mul_eq_mul_div, div_mul_cancel₀ _ (pow_ne_zero n hNpos.ne')]
  rw [hrewrite]
  calc
    (ρ / N) ^ n * M * N ^ n < 1 * N ^ n := mul_lt_mul_of_pos_right hlt1 (pow_pos hNpos n)
    _ = N ^ n := one_mul _

/-- Deleting an open set `U` from a boundary `E` keeps the norm of `g`, provided that `U` misses
a nonempty boundary `E0` and is the common sublevel set `{‖f y‖ < 1}` of finitely many algebra
elements `f y` of norm at most `M`. Otherwise `g ^ n * f y` would have norm below `‖g‖ ^ n`
on `E` for large `n`, forcing the point of `E0` where `g` peaks into `U`. -/
private theorem norm_le_sSup_norm_image_sdiff {K ι : Type*} [TopologicalSpace K]
    [CompactSpace K] {A : Subalgebra ℂ C(K, ℂ)} {E0 E U : Set K}
    (hE0 : IsUniformAlgebraBoundary A E0) (hE0ne : E0.Nonempty)
    (hE : IsUniformAlgebraBoundary A E) (hcap : E0 ∩ U = ∅) {t : Finset ι} (f : ι → A) {M : ℝ}
    (hM : 0 < M) (hMy : ∀ y ∈ t, ‖(f y).1‖ ≤ M)
    (hU : ∀ z, z ∈ U ↔ ∀ y ∈ t, ‖(f y).1 z‖ < 1) (g : A) :
    ‖g.1‖ ≤ sSup ((fun x => ‖g.1 x‖) '' (E \ U)) := by
  set N : ℝ := ‖g.1‖
  set ρ : ℝ := sSup ((fun x => ‖g.1 x‖) '' (E \ U))
  have hρnn : 0 ≤ ρ := sSup_norm_image_nonneg g (E \ U)
  by_contra hlt
  have hρlt : ρ < N := lt_of_not_ge hlt
  have hNpos : 0 < N := hρnn.trans_lt hρlt
  obtain ⟨n, hpow⟩ := exists_pow_mul_lt_pow hρnn hρlt hM
  have hpt (y : ι) (hy : y ∈ t) (z : K) (hz : z ∈ E) :
      ‖((g ^ n * f y).1 z)‖ < N ^ n := by
    rw [norm_pow_mul_apply]
    by_cases hzu : z ∈ U
    · have hfy : ‖(f y).1 z‖ < 1 := (hU z).1 hzu y hy
      calc
        ‖g.1 z‖ ^ n * ‖(f y).1 z‖
            ≤ N ^ n * ‖(f y).1 z‖ :=
              mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ (norm_nonneg _) (g.1.norm_coe_le_norm z) _)
                (norm_nonneg _)
        _ < N ^ n * 1 := mul_lt_mul_of_pos_left hfy (pow_pos hNpos n)
        _ = N ^ n := mul_one _
    · have hzE : z ∈ E \ U := ⟨hz, hzu⟩
      have hgle : ‖g.1 z‖ ≤ ρ := le_csSup
        ⟨N, fun r hr => by
          obtain ⟨w, -, rfl⟩ := hr
          exact g.1.norm_coe_le_norm w⟩ ⟨z, hzE, rfl⟩
      calc
        ‖g.1 z‖ ^ n * ‖(f y).1 z‖
            ≤ ρ ^ n * ‖(f y).1 z‖ :=
              mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ (norm_nonneg _) hgle n) (norm_nonneg _)
        _ ≤ ρ ^ n * M := mul_le_mul_of_nonneg_left
              ((f y).1.norm_coe_le_norm z |>.trans (hMy y hy))
              (pow_nonneg hρnn n)
        _ < N ^ n := hpow
  obtain ⟨y0, hy0E, hy0⟩ := exists_norm_eq_on_boundary hE0 hE0ne g
  have hy0lt : ∀ y ∈ t, ‖(f y).1 y0‖ < 1 := by
    intro y hy
    have hnorm : ‖(g ^ n * f y).1‖ < N ^ n := by
      have hs := sSup_norm_image_lt hE.1.isCompact (pow_pos hNpos n) (hpt y hy)
      rw [← hE.2 (g ^ n * f y)] at hs
      exact hs
    have hval : N ^ n * ‖(f y).1 y0‖ < N ^ n := by
      calc
        N ^ n * ‖(f y).1 y0‖ = ‖((g ^ n * f y).1 y0)‖ := by
          rw [norm_pow_mul_apply, hy0]
        _ ≤ ‖(g ^ n * f y).1‖ := (g ^ n * f y).1.norm_coe_le_norm y0
        _ < N ^ n := hnorm
    exact (mul_lt_iff_lt_one_left (pow_pos hNpos n)).mp (by
      rw [mul_comm]
      exact hval)
  have hy0cap : y0 ∈ E0 ∩ U := ⟨hy0E, (hU y0).2 hy0lt⟩
  rw [hcap] at hy0cap
  exact Set.notMem_empty y0 hy0cap

/-- Around a point omitted by one boundary, an open set may be deleted from every boundary. -/
private theorem exists_open_boundary_sdiff {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (A : Subalgebra ℂ C(K, ℂ))
    (hsep : ∀ x y : K, x ≠ y → ∃ f : A, f.1 x ≠ f.1 y)
    {E0 : Set K} (hE0 : IsUniformAlgebraBoundary A E0) {x0 : K} (hx0 : x0 ∉ E0) :
    ∃ U : Set K, IsOpen U ∧ x0 ∈ U ∧ ∀ E : Set K, IsUniformAlgebraBoundary A E →
      IsUniformAlgebraBoundary A (E \ U) := by
  have : Nonempty K := ⟨x0⟩
  have hE0ne : E0.Nonempty := hE0.nonempty
  -- Functions vanishing at `x0` and of modulus `2` at the points of `E0`.
  have hpts := separatesPoints_of_point_separation hsep
  have hex (y : E0) : ∃ f : A, f.1 x0 = 0 ∧ f.1 (y : K) = 2 := by
    classical
    have hyx : (y : K) ≠ x0 := fun h => hx0 (h ▸ y.property)
    obtain ⟨g, hgA, hg0, hg2⟩ := hpts.strongly
      (fun z => if z = (y : K) then (2 : ℂ) else 0) x0 y
    refine ⟨⟨g, hgA⟩, ?_, ?_⟩
    · rw [hg0]
      simp [Ne.symm hyx]
    · rw [hg2]
      simp
  choose f hf0 hf2 using hex
  -- Finitely many of the open sets `{1 < ‖f y‖}` cover the compact boundary `E0`.
  let V : E0 → Set K := fun y => {z | 1 < ‖(f y).1 z‖}
  have hVopen : ∀ y, IsOpen (V y) := fun y =>
    isOpen_lt continuous_const (continuous_norm.comp (f y).1.continuous)
  have hcover : E0 ⊆ ⋃ y, V y := by
    intro z hz
    refine Set.mem_iUnion.mpr ⟨⟨z, hz⟩, ?_⟩
    apply Set.mem_ofPred.mpr
    rw [hf2 ⟨z, hz⟩, Complex.norm_two]
    exact one_lt_two
  obtain ⟨t, ht⟩ := hE0.1.isCompact.elim_finite_subcover V hVopen hcover
  have htne : t.Nonempty := by
    obtain ⟨z, hz⟩ := hE0ne
    obtain ⟨y, hy, -⟩ := Set.mem_iUnion₂.mp (ht hz)
    exact ⟨y, hy⟩
  -- The open set `U` where all of these functions are small contains `x0` and misses `E0`.
  let U : Set K := ⋂ y ∈ t, {z | ‖(f y).1 z‖ < 1}
  have hU : ∀ z, z ∈ U ↔ ∀ y ∈ t, ‖(f y).1 z‖ < 1 := fun z => Set.mem_iInter₂
  have hUopen : IsOpen U := isOpen_biInter_finset fun y _ =>
    isOpen_lt (continuous_norm.comp (f y).1.continuous) continuous_const
  have hx0U : x0 ∈ U := (hU x0).2 fun y _ => by
    rw [hf0 y, norm_zero]
    exact one_pos
  have hcap : E0 ∩ U = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hzE hzU
    obtain ⟨y, hy, hyz⟩ := Set.mem_iUnion₂.mp (ht hzE)
    exact lt_asymm hyz.out ((hU z).1 hzU y hy)
  have hMbd : BddAbove ((fun y : E0 => ‖(f y).1‖) '' (t : Set E0)) :=
    ((Finset.finite_toSet t).image (fun y => ‖(f y).1‖)).bddAbove
  set M : ℝ := sSup ((fun y : E0 => ‖(f y).1‖) '' (t : Set E0))
  have hMy (y : E0) (hy : y ∈ t) : ‖(f y).1‖ ≤ M :=
    le_csSup hMbd (Set.mem_image_of_mem _ hy)
  have hMpos : 0 < M := by
    obtain ⟨y, hy⟩ := htne
    calc
      (0 : ℝ) < 2 := two_pos
      _ = ‖(f y).1 (y : K)‖ := by rw [hf2 y, Complex.norm_two]
      _ ≤ ‖(f y).1‖ := (f y).1.norm_coe_le_norm _
      _ ≤ M := hMy y hy
  refine ⟨U, hUopen, hx0U, fun E hE => ⟨hE.1.sdiff hUopen, fun g => ?_⟩⟩
  exact le_antisymm
    (norm_le_sSup_norm_image_sdiff hE0 hE0ne hE hcap f hMpos hMy hU g)
    (sSup_norm_image_le g (E \ U))

/-- **20.23**: a point-separating algebra has a smallest closed norming boundary.
The restriction isometry is expressed by the exact boundary-norm identity in the predicate. -/
theorem exists_shilov_boundary {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (A : Subalgebra ℂ C(K, ℂ))
    (hsep : ∀ x y : K, x ≠ y → ∃ f : A, f.1 x ≠ f.1 y) :
    ∃ F : Set K, IsUniformAlgebraBoundary A F ∧
      ∀ G : Set K, IsUniformAlgebraBoundary A G → F ⊆ G := by
  let boundaries : Set (Set K) := {F | IsUniformAlgebraBoundary A F}
  let S : Set K := ⋂₀ boundaries
  have hSclosed : IsClosed S := isClosed_sInter fun _ hB => hB.1
  have hleast : ∀ G, IsUniformAlgebraBoundary A G → S ⊆ G :=
    fun _ hG => Set.sInter_subset_of_mem hG
  refine ⟨S, ⟨hSclosed, ?_⟩, hleast⟩
  intro f
  have hle : sSup ((fun x => ‖f.1 x‖) '' S) ≤ ‖f.1‖ := sSup_norm_image_le f S
  by_cases hf0 : ‖f.1‖ = 0
  · have hnn := sSup_norm_image_nonneg f S
    have hle0 : sSup ((fun x => ‖f.1 x‖) '' S) ≤ 0 := by simpa [hf0] using hle
    rw [hf0, le_antisymm hle0 hnn]
  · have hfpos : 0 < ‖f.1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hf0)
    let Mset : Set K := {x | ‖f.1 x‖ = ‖f.1‖}
    have hMclosed : IsClosed Mset := by
      have hcont : Continuous fun x => ‖f.1 x‖ := continuous_norm.comp f.1.continuous
      have hset : Mset = (fun x => ‖f.1 x‖) ⁻¹' {‖f.1‖} := by
        ext x
        simp [Mset]
      rw [hset]
      exact isClosed_singleton.preimage hcont
    by_cases hinter : (S ∩ Mset).Nonempty
    · obtain ⟨x, hx⟩ := hinter
      have hbdd : BddAbove ((fun z => ‖f.1 z‖) '' S) :=
        ⟨‖f.1‖, fun r hr => by
          obtain ⟨z, -, rfl⟩ := hr
          exact f.1.norm_coe_le_norm z⟩
      exact le_antisymm (le_csSup hbdd ⟨x, hx.1, hx.2⟩) hle
    · rw [Set.not_nonempty_iff_eq_empty] at hinter
      exfalso
      have hex (x : Mset) :
          ∃ E, IsUniformAlgebraBoundary A E ∧ (x : K) ∉ E := by
        have hxS : (x : K) ∉ S := by
          intro hx
          have : (x : K) ∈ S ∩ Mset := ⟨hx, x.property⟩
          rw [hinter] at this
          exact Set.notMem_empty _ this
        have hnot : ¬ ∀ E : boundaries, (x : K) ∈ (E : Set K) := by
          intro hall
          apply hxS
          dsimp only [S]
          rw [Set.sInter_eq_iInter]
          exact Set.mem_iInter.mpr fun E => hall E
        obtain ⟨E, hE⟩ := not_forall.mp hnot
        exact ⟨E.1, E.2, hE⟩
      choose E hEb hxE using hex
      have hU (x : Mset) := exists_open_boundary_sdiff A hsep (hEb x) (hxE x)
      choose U hUopen hxU hUbd using hU
      have hcover : Mset ⊆ ⋃ x : Mset, U x := fun z hz =>
        Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hxU ⟨z, hz⟩⟩
      obtain ⟨t, ht⟩ := hMclosed.isCompact.elim_finite_subcover U
        (fun x => hUopen x) hcover
      have hfold := boundary_foldl_sdiff A t.toList U
        (fun V _ F hF => hUbd V F hF) (isUniformAlgebraBoundary_univ A)
      have hmiss : ∀ z ∈ Mset, z ∉ t.toList.foldl (fun G i => G \ U i) Set.univ := by
        intro z hz
        obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (ht hz)
        exact notMem_foldl_sdiff t.toList U Set.univ
          (Or.inr ⟨i, Finset.mem_toList.mpr hi, hzi⟩)
      have hpt : ∀ z ∈ t.toList.foldl (fun G i => G \ U i) Set.univ,
          ‖f.1 z‖ < ‖f.1‖ := by
        intro z hz
        exact lt_of_le_of_ne (f.1.norm_coe_le_norm z) fun heq => hmiss z heq hz
      have hstrict := sSup_norm_image_lt hfold.1.isCompact hfpos hpt
      exact hstrict.ne (hfold.2 f).symm

end CKMA
