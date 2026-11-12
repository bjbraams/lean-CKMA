/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ProjectiveLimit.Countable

/-!
# Arbitrary-index Kolmogorov extension (06.1)

A consistent family of finite-dimensional probability measures on standard Borel
coordinate spaces has a unique probability measure on the full product sigma-algebra.
The index type is arbitrary, including the empty type.

Uniqueness is `MeasureTheory.IsProjectiveLimit.unique`. Existence extends
`projectiveFamilyContent` by `AddContent.measure`. Sigma-additivity is
`addContent_iUnion_eq_sum_of_tendsto_zero` and
`isSigmaSubadditive_of_addContent_iUnion_eq_tsum`: cylinders in a decreasing sequence
with empty intersection depend on countably many coordinates, where
`TauCeti.Measure.exists_isProjectiveLimit_of_countable` supplies a measure, and
`tendsto_measure_iInter_atTop` gives continuity from above.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped NNReal ENNReal Topology

open MeasureTheory Filter Function Set Finset

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- A coordinate of a projective family of probability measures is nonempty. -/
private lemma nonempty_of_isProjectiveProbability
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) [∀ I, IsProbabilityMeasure (P I)] (i : ι) :
    Nonempty (X i) := by
  have h : Nonempty (∀ j : ({i} : Finset ι), X j) :=
    MeasureTheory.nonempty_of_isProbabilityMeasure (P {i})
  exact ⟨h.some ⟨i, Finset.mem_singleton_self i⟩⟩

/-- Read the coordinates in `I` from a point indexed by a superset `u`. -/
private def coordIncl {u : Set ι} {I : Finset ι} (hI : (I : Set ι) ⊆ u)
    (x : ∀ i : u, X i) (i : I) : X i :=
  x ⟨i.1, hI i.2⟩

/-- The coordinate inclusion into a finite subproduct is measurable. -/
private lemma measurable_coordIncl {u : Set ι} {I : Finset ι} (hI : (I : Set ι) ⊆ u) :
    Measurable (coordIncl (X := X) hI) := by
  refine Measurable.of_eval fun i ↦ ?_
  simpa [coordIncl] using measurable_pi_apply (⟨i.1, hI i.2⟩ : u)

/-- Transport a finset along a propositional equality, preserving underlying elements. -/
private def finsetCongr {s t : Finset ι} (h : s = t) : s ≃ t :=
  Equiv.subtypeEquivProp (show (fun a : ι ↦ a ∈ s) = (fun a : ι ↦ a ∈ t) by rw [h])

/-- Finite products along an equality of index finsets are measurably equivalent. -/
private def finsetPiCongr {s t : Finset ι} (h : s = t) :
    (∀ i : s, X i) ≃ᵐ (∀ i : t, X i) :=
  MeasurableEquiv.piCongrLeft (fun i : t ↦ X i) (finsetCongr h)

/-- Pushing a finite-dimensional law along `finsetPiCongr` does not change it. -/
private lemma map_finsetPiCongr (P : ∀ I : Finset ι, Measure (∀ i : I, X i))
    {s t : Finset ι} (h : s = t) :
    (P s).map (finsetPiCongr (X := X) h) = P t := by
  cases h
  refine Measure.ext fun _ _ ↦ ?_
  rw [MeasurableEquiv.map_apply]
  congr 1

/-- Equivalence between a product over a subtype finset and the product over its image. -/
private def subtypeImagePiEquiv (u : Set ι) (J : Finset u) :
    (∀ j : J, X j) ≃ᵐ (∀ i : J.map (Embedding.subtype (· ∈ u)), X i) :=
  MeasurableEquiv.piCongrLeft (fun i : J.map (Embedding.subtype (· ∈ u)) ↦ X i)
    (J.equivMap (Embedding.subtype (· ∈ u)))

/-- Inverse of `subtypeImagePiEquiv` on a coordinate. -/
private lemma subtypeImagePiEquiv_symm_apply (u : Set ι) (J : Finset u)
    (x : ∀ i : J.map (Embedding.subtype (· ∈ u)), X i) (j : J) :
    (subtypeImagePiEquiv (X := X) u J).symm x j =
      x (J.equivMap (Embedding.subtype (· ∈ u)) j) :=
  Equiv.piCongrLeft_symm_apply
    (fun i : J.map (Embedding.subtype (· ∈ u)) ↦ X i)
    (J.equivMap (Embedding.subtype (· ∈ u))) x j

/-- The projective family induced on the finite subsets of a set of coordinates. -/
private def projectiveFamilyOn (u : Set ι) (P : ∀ I : Finset ι, Measure (∀ i : I, X i))
    (J : Finset u) : Measure (∀ j : J, X j) :=
  (P (J.map (Embedding.subtype (· ∈ u)))).map (subtypeImagePiEquiv (X := X) u J).symm

/-- Restriction to a coordinate subset preserves probability measures. -/
private lemma isProbabilityMeasure_projectiveFamilyOn (u : Set ι)
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) [∀ I, IsProbabilityMeasure (P I)]
    (J : Finset u) : IsProbabilityMeasure (projectiveFamilyOn u P J) := by
  rw [projectiveFamilyOn]
  infer_instance

/-- The family induced on a coordinate subset is projective. -/
private lemma isProjectiveMeasureFamily_projectiveFamilyOn (u : Set ι)
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) (hP : IsProjectiveMeasureFamily P) :
    IsProjectiveMeasureFamily (α := fun i : u ↦ X i) (projectiveFamilyOn u P) := by
  intro I J hJI
  let emb : u ↪ ι := Embedding.subtype (· ∈ u)
  have hmap : J.map emb ⊆ I.map emb := Finset.map_subset_map.mpr hJI
  rw [projectiveFamilyOn, projectiveFamilyOn, hP (I.map emb) (J.map emb) hmap]
  rw [Measure.map_map (subtypeImagePiEquiv (X := X) u J).symm.measurable
    (Finset.measurable_restrict₂ hmap)]
  have hcomp :
      ((subtypeImagePiEquiv (X := X) u J).symm ∘ Finset.restrict₂ hmap :
        (∀ i : I.map emb, X i) → ∀ j : J, X j) =
        Finset.restrict₂ (π := fun i : u ↦ X i) hJI ∘
          (subtypeImagePiEquiv (X := X) u I).symm := by
    funext x j
    simp only [Function.comp_apply, Finset.restrict₂_def, subtypeImagePiEquiv_symm_apply]
    congr 1
  rw [hcomp]
  exact (Measure.map_map (Finset.measurable_restrict₂ hJI)
    (subtypeImagePiEquiv (X := X) u I).symm.measurable).symm

/-- A projective limit on `u` reproduces finite-dimensional laws of coordinates inside `u`. -/
private lemma projectiveLimit_coordIncl (u : Set ι)
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) {μ : Measure (∀ i : u, X i)}
    (hμ : IsProjectiveLimit μ (projectiveFamilyOn u P)) {I : Finset ι}
    {S : Set (∀ i : I, X i)} (hS : MeasurableSet S) (hI : (I : Set ι) ⊆ u) :
    μ (coordIncl (X := X) hI ⁻¹' S) = P I S := by
  let emb : u ↪ ι := Embedding.subtype (· ∈ u)
  let J : Finset u := I.preimage Subtype.val Subtype.val_injective.injOn
  have hmap : J.map emb = I := by
    ext i
    constructor
    · intro hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      exact Finset.mem_preimage.mp hj
    · intro hi
      exact Finset.mem_map.mpr ⟨⟨i, hI hi⟩, Finset.mem_preimage.mpr hi, rfl⟩
  let aux : J ≃ I :=
    { toFun := fun j ↦ ⟨j.1.1, Finset.mem_preimage.mp j.2⟩
      invFun := fun i ↦ ⟨⟨i.1, hI i.2⟩, Finset.mem_preimage.mpr i.2⟩
      left_inv := fun j ↦ Subtype.ext (Subtype.ext rfl)
      right_inv := fun i ↦ Subtype.ext rfl }
  let g : (∀ j : J, X j) ≃ᵐ (∀ i : I, X i) :=
    MeasurableEquiv.piCongrLeft (fun i : I ↦ X i) aux
  have hcoord (x : ∀ i : u, X i) : coordIncl (X := X) hI x = g (J.restrict x) := by
    funext i
    let j : J := ⟨⟨i.1, hI i.2⟩, Finset.mem_preimage.mpr i.2⟩
    have hj : aux j = i := Subtype.ext rfl
    have hg : g (J.restrict x) (aux j) = J.restrict x j :=
      MeasurableEquiv.piCongrLeft_apply_apply (β := fun k : I ↦ X k) aux (J.restrict x) j
    calc
      coordIncl (X := X) hI x i = J.restrict x j := rfl
      _ = g (J.restrict x) (aux j) := hg.symm
      _ = g (J.restrict x) i := by
        cases congr_arg_heq (g (J.restrict x)) hj
        rfl
  have hpre : coordIncl (X := X) hI ⁻¹' S = cylinder J (g ⁻¹' S) := by
    ext x
    simp [mem_cylinder, hcoord x]
  rw [hpre, hμ.measure_cylinder J (hS.preimage g.measurable)]
  let E := subtypeImagePiEquiv (X := X) u J
  let φ := finsetPiCongr (X := X) hmap
  have hcomp (y : ∀ i : J.map emb, X i) : g (E.symm y) = φ y := by
    funext i
    let j : J := ⟨⟨i.1, hI i.2⟩, Finset.mem_preimage.mpr i.2⟩
    have hj : aux j = i := Subtype.ext rfl
    have hidx : finsetCongr hmap (J.equivMap emb j) = i := by
      apply Subtype.ext
      simp only [finsetCongr, Equiv.subtypeEquivProp, Equiv.subtypeEquiv_apply, Equiv.refl_apply]
      rfl
    have h1 : g (E.symm y) i = g (E.symm y) (aux j) := by
      cases congr_arg_heq (g (E.symm y)) hj.symm
      rfl
    have h2 : g (E.symm y) (aux j) = E.symm y j :=
      MeasurableEquiv.piCongrLeft_apply_apply (β := fun k : I ↦ X k) aux (E.symm y) j
    have h3 : E.symm y j = y (J.equivMap emb j) := subtypeImagePiEquiv_symm_apply u J y j
    have h4 : y (J.equivMap emb j) =
        φ y (finsetCongr hmap (J.equivMap emb j)) :=
      (MeasurableEquiv.piCongrLeft_apply_apply (β := fun k : I ↦ X k) (finsetCongr hmap) y
        (J.equivMap emb j)).symm
    have h5 : φ y (finsetCongr hmap (J.equivMap emb j)) = φ y i := by
      cases congr_arg_heq (φ y) hidx
      rfl
    exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
  have hset : E.symm ⁻¹' (g ⁻¹' S) = φ ⁻¹' S := by
    ext z
    simp only [Set.mem_preimage, hcomp z]
  rw [projectiveFamilyOn, MeasurableEquiv.map_apply, hset, ← MeasurableEquiv.map_apply]
  exact congrArg (fun ν : Measure (∀ i : I, X i) ↦ ν S) (map_finsetPiCongr P hmap)

/-- The projective-family content of a decreasing sequence of cylinders with empty
intersection tends to zero. -/
private lemma projectiveFamilyContent_tendsto_zero [∀ i, StandardBorelSpace (X i)]
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily P) {A : ℕ → Set (∀ i, X i)}
    (A_mem : ∀ n, A n ∈ measurableCylinders X) (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅) :
    Tendsto (fun n ↦ projectiveFamilyContent hP (A n)) atTop (𝓝 0) := by
  classical
  have hne : ∀ i, Nonempty (X i) := fun i ↦ nonempty_of_isProjectiveProbability P i
  have A_cyl (n : ℕ) : ∃ s S, MeasurableSet S ∧ A n = cylinder s S :=
    (mem_measurableCylinders _).1 (A_mem n)
  choose s S mS A_eq using A_cyl
  let u : Set ι := ⋃ n, (s n : Set ι)
  have hsu (n : ℕ) : (s n : Set ι) ⊆ u := fun _ hi ↦ Set.mem_iUnion.2 ⟨n, hi⟩
  let f : (∀ i : u, X i) → ∀ i, X i :=
    fun y i ↦ if hi : i ∈ u then y ⟨i, hi⟩ else (hne i).some
  let B : ℕ → Set (∀ i : u, X i) := fun n ↦ coordIncl (X := X) (hsu n) ⁻¹' S n
  have hBf (n : ℕ) : f ⁻¹' A n = B n := by
    ext y
    rw [A_eq, Set.mem_preimage, mem_cylinder]
    have hrest : (s n).restrict (f y) = coordIncl (X := X) (hsu n) y := by
      funext i
      simp only [Finset.restrict, coordIncl, f]
      exact dite_eq_left (hsu n i.2)
    rw [hrest]
    simp [B]
  have B_anti : Antitone B := fun m n hmn ↦ by
    rw [← hBf m, ← hBf n]
    exact Set.preimage_mono (A_anti hmn)
  have B_inter : ⋂ n, B n = ∅ := by
    simp_rw [← hBf, ← Set.preimage_iInter, A_inter, Set.preimage_empty]
  have mB (n : ℕ) : MeasurableSet (B n) :=
    (mS n).preimage (measurable_coordIncl (hsu n))
  have : Countable u := Set.countable_iUnion fun n ↦ (s n).countable_toSet
  have : ∀ i : u, StandardBorelSpace (X i) := fun _ ↦ inferInstance
  have : ∀ J : Finset u, IsProbabilityMeasure (projectiveFamilyOn u P J) :=
    fun J ↦ isProbabilityMeasure_projectiveFamilyOn u P J
  have hQ : IsProjectiveMeasureFamily (α := fun i : u ↦ X i) (projectiveFamilyOn u P) :=
    isProjectiveMeasureFamily_projectiveFamilyOn u P hP
  obtain ⟨μ, hμProb, hμ⟩ := TauCeti.Measure.exists_isProjectiveLimit_of_countable
    (ι := u) (X := fun i : u ↦ X i) (projectiveFamilyOn u P) hQ
  have : IsProbabilityMeasure μ := hμProb
  conv =>
    enter [1]; ext n
    rw [A_eq, projectiveFamilyContent_cylinder hP (mS n),
      ← projectiveLimit_coordIncl u P (μ := μ) hμ (mS n) (hsu n)]
  convert!
    tendsto_measure_iInter_atTop (fun n ↦ (mB n).nullMeasurableSet) B_anti
      ⟨0, measure_ne_top _ _⟩
  · rw [B_inter, measure_empty]
  · infer_instance

/-- The content of a projective family of probability measures is sigma-subadditive. -/
private lemma isSigmaSubadditive_projectiveFamilyContent [∀ i, StandardBorelSpace (X i)]
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily P) :
    (projectiveFamilyContent hP).IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum isSetRing_measurableCylinders
    (fun f hf hUnion hdisj ↦ ?_)
  exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (projectiveFamilyContent hP) (fun _ _ ↦ projectiveFamilyContent_ne_top hP)
    (fun _ hmem hanti hinter ↦
      projectiveFamilyContent_tendsto_zero P hP hmem hanti hinter)
    hf hUnion hdisj

/-- **06.1**: arbitrary-index Kolmogorov extension on standard Borel coordinates.
Uniqueness is inherited from Mathlib; the countable existence theorem is in TauCeti. -/
theorem existsUnique_isProjectiveLimit [∀ i, StandardBorelSpace (X i)]
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) [∀ I, IsProbabilityMeasure (P I)]
    (hP : IsProjectiveMeasureFamily P) :
    ∃! μ : Measure (∀ i, X i), IsProbabilityMeasure μ ∧ IsProjectiveLimit μ P := by
  refine existsUnique_of_exists_of_unique ?_ ?_
  · let m := projectiveFamilyContent hP
    have hσ : m.IsSigmaSubadditive := isSigmaSubadditive_projectiveFamilyContent P hP
    let μ : Measure (∀ i, X i) := m.measure isSetSemiring_measurableCylinders
      generateFrom_measurableCylinders.ge hσ
    have hlim : IsProjectiveLimit μ P := by
      intro I
      ext Z hZ
      rw [Measure.map_apply (Finset.measurable_restrict I) hZ]
      unfold μ
      rw [AddContent.measure_eq, ← cylinder, projectiveFamilyContent_cylinder hP hZ]
      · exact generateFrom_measurableCylinders.symm
      · exact cylinder_mem_measurableCylinders _ _ hZ
    exact ⟨μ, hlim.isProbabilityMeasure, hlim⟩
  · intro μ ν hμ hν
    exact hμ.2.unique hν.2

end CKMA
