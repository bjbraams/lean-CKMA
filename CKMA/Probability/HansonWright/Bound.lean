/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Probability.HansonWright.OffDiagonal

/-!
# Hanson–Wright tail from the diagonal and off-diagonal pieces

The centered quadratic form splits into a diagonal and an off-diagonal sum. Boolean slices
of the off-diagonal sum are linear in one coordinate block, so the sub-Gaussian product
bound closes the moment generating function.
-/

@[expose] public section

noncomputable section

namespace CKMA

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal RealInnerProductSpace Matrix Matrix.Norms.L2Operator

universe u

variable {n : ℕ}

/-- A sampled quadratic form is its diagonal plus the off-diagonal sum. -/
lemma sampledQuadraticForm_eq_diag_add_off (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    ∑ i, ∑ j, A i j * x i * x j =
      ∑ i, A i i * x i ^ 2 + offDiagonalForm A x := by
  unfold offDiagonalForm
  have hdiag : ∑ i, A i i * x i ^ 2 =
      ∑ i, ∑ j, if i = j then A i i * x i ^ 2 else 0 := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_eq_single i (fun j _ hj ↦ ?_)
      (fun hi ↦ absurd (Finset.mem_univ i) hi)]
    · rw [ite_eq_left rfl]
    · rw [ite_eq_right (fun h : i = j ↦ hj h.symm)]
  rw [hdiag, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, ite_eq_left rfl, pow_two, add_zero, mul_assoc]
  · rw [ite_eq_right hij, ite_eq_right hij, zero_add]

/-- Negation passes through the off-diagonal form. -/
lemma offDiagonalForm_neg (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    offDiagonalForm (-A) x = -offDiagonalForm A x := by
  unfold offDiagonalForm
  simp only [Matrix.neg_apply]
  simp_rw [mul_assoc, neg_mul]
  have hsign : ∀ i j,
      (if i = j then (0 : ℝ) else -(A i j * (x i * x j))) =
        -(if i = j then 0 else A i j * (x i * x j)) := by
    intro i j
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  simp_rw [hsign, Finset.sum_neg_distrib]

/-- Negation preserves the Euclidean operator norm. -/
lemma realMatrixOperatorNorm_neg (A : Matrix (Fin n) (Fin n) ℝ) :
    realMatrixOperatorNorm (-A) = realMatrixOperatorNorm A := by
  rw [realMatrixOperatorNorm_eq, realMatrixOperatorNorm_eq, norm_neg]

/-- Negation preserves the squared Frobenius norm. -/
lemma realMatrixFrobeniusSq_neg (A : Matrix (Fin n) (Fin n) ℝ) :
    realMatrixFrobeniusSq (-A) = realMatrixFrobeniusSq A := by
  unfold realMatrixFrobeniusSq
  simp [Matrix.neg_apply]

/-- A masked transpose sees only the `δ = true` coordinates. -/
lemma maskedTranspose_mulVec_blocks (A : Matrix (Fin n) (Fin n) ℝ) (δ : Fin n → Bool)
    (u : {i : Fin n // δ i = true} → ℝ) (v : {j : Fin n // ¬ δ j = true} → ℝ) (k : Fin n) :
    ((maskedMatrix A δ).transpose *ᵥ fun i ↦
        if h : δ i = true then u ⟨i, h⟩ else v ⟨i, h⟩) k =
      if _ : ¬ δ k = true then ∑ i : {i // δ i = true}, A i.1 k * u i else 0 := by
  classical
  let x : Fin n → ℝ := fun i ↦ if h : δ i = true then u ⟨i, h⟩ else v ⟨i, h⟩
  have hxfun : x = fun i ↦ if h : δ i = true then u ⟨i, h⟩ else v ⟨i, h⟩ := rfl
  rw [← hxfun]
  simp only [Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply, maskedMatrix]
  by_cases hk : δ k = true
  · have hnot : ¬ ¬ δ k = true := fun h ↦ h hk
    rw [dite_eq_right hnot]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hmask : ¬ (δ i = true ∧ δ k = false) := by
      intro h
      rw [h.2] at hk
      exact Bool.false_ne_true hk
    rw [ite_eq_right hmask, zero_mul]
  · rw [dite_eq_left hk]
    have hkf : δ k = false := Bool.eq_false_of_not_eq_true hk
    have hterm : ∀ i,
        (if δ i = true ∧ δ k = false then A i k else 0) * x i =
          if δ i = true then A i k * x i else 0 := by
      intro i
      by_cases hi : δ i = true
      · rw [ite_eq_left (And.intro hi hkf), ite_eq_left hi]
      · have hmask : ¬ (δ i = true ∧ δ k = false) := fun h ↦ hi h.1
        rw [ite_eq_right hmask, ite_eq_right hi, zero_mul]
    rw [Finset.sum_congr rfl (fun i _ ↦ hterm i), ← Finset.sum_filter]
    rw [Finset.sum_subtype (p := fun i : Fin n ↦ δ i = true)
      (Finset.univ.filter fun i ↦ δ i = true) (fun i ↦ by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and])]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hi : δ (i : Fin n) = true := i.2
    have hx : x (i : Fin n) = u ⟨i, hi⟩ := by simp only [x, dite_eq_left hi]
    rw [hx]

/-- A Boolean slice is the block linear form on complementary coordinates. -/
lemma bernoulliSlice_eq_subtype_dot (A : Matrix (Fin n) (Fin n) ℝ) (δ : Fin n → Bool)
    (u : {i : Fin n // δ i = true} → ℝ) (v : {j : Fin n // ¬ δ j = true} → ℝ) :
    bernoulliSlice A δ (fun i ↦ if h : δ i = true then u ⟨i, h⟩ else v ⟨i, h⟩) =
      ∑ j : {j : Fin n // ¬ δ j = true},
        (∑ i : {i : Fin n // δ i = true}, A i.1 j.1 * u i) * v j := by
  classical
  let x : Fin n → ℝ := fun i ↦ if h : δ i = true then u ⟨i, h⟩ else v ⟨i, h⟩
  rw [show bernoulliSlice A δ (fun i ↦ if h : δ i = true then u ⟨i, h⟩ else v ⟨i, h⟩) =
      bernoulliSlice A δ x by rfl, bernoulliSlice_eq_dot]
  simp only [dotProduct]
  simp_rw [show x = fun i ↦ if h : δ i = true then u ⟨i, h⟩ else v ⟨i, h⟩ by rfl,
    maskedTranspose_mulVec_blocks A δ u v]
  have hterm : ∀ k, (if hk : ¬ δ k = true then
      ∑ i : {i // δ i = true}, A i.1 k * u i else 0) * x k =
      if ¬ δ k = true then
        (∑ i : {i // δ i = true}, A i.1 k * u i) * x k else 0 := by
    intro k
    by_cases hk : ¬ δ k = true
    · rw [dite_eq_left hk, ite_eq_left hk]
    · rw [dite_eq_right hk, ite_eq_right hk, zero_mul]
  rw [Finset.sum_congr rfl (fun k _ ↦ hterm k), ← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun k : Fin n ↦ ¬ δ k = true)
    (Finset.univ.filter fun k ↦ ¬ δ k = true) (fun k ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and])]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hk : ¬ δ (k : Fin n) = true := k.2
  have hx : x (k : Fin n) = v ⟨k, hk⟩ := by simp only [x, dite_eq_right hk]
  rw [hx]

/-- The squared masked image depends only on the `δ = true` block. -/
lemma maskedTranspose_sq_blocks (A : Matrix (Fin n) (Fin n) ℝ) (δ : Fin n → Bool)
    (u : {i : Fin n // δ i = true} → ℝ) (v : {j : Fin n // ¬ δ j = true} → ℝ) :
    let x : Fin n → ℝ := fun i ↦ if h : δ i = true then u ⟨i, h⟩ else v ⟨i, h⟩
    ((maskedMatrix A δ).transpose *ᵥ x) ⬝ᵥ ((maskedMatrix A δ).transpose *ᵥ x) =
      ∑ j : {j : Fin n // ¬ δ j = true},
        (∑ i : {i : Fin n // δ i = true}, A i.1 j.1 * u i) ^ 2 := by
  classical
  intro x
  simp only [dotProduct, sq]
  simp_rw [show x = fun i ↦ if h : δ i = true then u ⟨i, h⟩ else v ⟨i, h⟩ by rfl,
    maskedTranspose_mulVec_blocks A δ u v]
  have hsq : ∀ k, (if hk : ¬ δ k = true then
      ∑ i : {i // δ i = true}, A i.1 k * u i else 0) *
      (if hk : ¬ δ k = true then ∑ i : {i // δ i = true}, A i.1 k * u i else 0) =
      if ¬ δ k = true then
        (∑ i : {i // δ i = true}, A i.1 k * u i) *
          (∑ i : {i // δ i = true}, A i.1 k * u i) else 0 := by
    intro k
    by_cases hk : ¬ δ k = true
    · rw [dite_eq_left hk, ite_eq_left hk]
    · rw [dite_eq_right hk, zero_mul, ite_eq_right hk]
  rw [Finset.sum_congr rfl (fun k _ ↦ hsq k), ← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun k : Fin n ↦ ¬ δ k = true)
    (Finset.univ.filter fun k ↦ ¬ δ k = true) (fun k ↦ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and])]

/-- The symmetric split preserves the centered quadratic form. -/
lemma centeredQuadratic_eq_diag_add_off {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) (hcent : ∀ i, ∫ ω, X i ω ∂μ = 0) {K : ℝ}
    (hpsi : ∀ i, HasPsiTwoBound (X i) μ (2 * K)) (A : Matrix (Fin n) (Fin n) ℝ) (ω : Ω) :
    sampledQuadraticForm A X ω - ∫ η, sampledQuadraticForm A X η ∂μ =
      (∑ i, A i i * (X i ω ^ 2 - ∫ η, X i η ^ 2 ∂μ)) +
        offDiagonalForm A (fun i ↦ X i ω) := by
  have hint := integral_sampledQuadraticForm X hmeas hindep hcent hpsi A
  have hsplit := sampledQuadraticForm_eq_diag_add_off A (fun i ↦ X i ω)
  calc
    sampledQuadraticForm A X ω - ∫ η, sampledQuadraticForm A X η ∂μ =
        (∑ i, A i i * X i ω ^ 2 + offDiagonalForm A (fun i ↦ X i ω)) -
          ∑ i, A i i * ∫ η, X i η ^ 2 ∂μ := by
      rw [sampledQuadraticForm, hsplit, hint.2]
    _ = (∑ i, A i i * X i ω ^ 2 - ∑ i, A i i * ∫ η, X i η ^ 2 ∂μ) +
          offDiagonalForm A (fun i ↦ X i ω) := by rw [add_sub_right_comm]
    _ = (∑ i, A i i * (X i ω ^ 2 - ∫ η, X i η ^ 2 ∂μ)) +
          offDiagonalForm A (fun i ↦ X i ω) := by
      rw [← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- One Boolean slice has a quadratic exponential moment on a sub-Gaussian product. -/
lemma integral_exp_bernoulliSlice_le (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    {K θ : ℝ} (hK : 0 < K)
    (hsub : ∀ i, HasSubgaussianMGF id (⟨64 * K ^ 2, by positivity⟩ : ℝ≥0) (ν i))
    (A : Matrix (Fin n) (Fin n) ℝ) (δ : Fin n → Bool)
    (hcut : 2048 * K ^ 4 * θ ^ 2 * realMatrixOperatorNorm (maskedMatrix A δ) ^ 2 ≤ 1 / 4) :
    Integrable (fun x ↦ Real.exp (θ * bernoulliSlice A δ x)) (Measure.pi ν) ∧
      ∫ x, Real.exp (θ * bernoulliSlice A δ x) ∂Measure.pi ν ≤
        Real.exp (4096 * K ^ 4 * θ ^ 2 * realMatrixFrobeniusSq (maskedMatrix A δ)) := by
  classical
  let p : Fin n → Prop := fun i ↦ δ i = true
  let ρ := Measure.pi ν
  let ρI := Measure.pi (fun i : {i // p i} ↦ ν i.1)
  let ρJ := Measure.pi (fun j : {j // ¬ p j} ↦ ν j.1)
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n ↦ ℝ) p
  have he := measurePreserving_piEquivPiSubtypeProd (α := fun _ : Fin n ↦ ℝ) (μ := ν) p
  let M := maskedMatrix A δ
  let αcoef : ℝ := 32 * K ^ 2 * θ ^ 2
  have hα : 0 ≤ αcoef := by positivity
  let w : ({i // p i} → ℝ) → ({j // ¬ p j} → ℝ) :=
    fun u j ↦ ∑ i : {i // p i}, A i.1 j.1 * u i
  have happ : ∀ u v i, e.symm (u, v) i =
      if h : p i then u ⟨i, h⟩ else v ⟨i, h⟩ := by
    intro u v i
    simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply]
  have hslice : ∀ u v, bernoulliSlice A δ (e.symm (u, v)) = ∑ j, w u j * v j := by
    intro u v
    have hx : e.symm (u, v) = fun i ↦ if h : p i then u ⟨i, h⟩ else v ⟨i, h⟩ := by
      ext i; exact happ u v i
    rw [hx, bernoulliSlice_eq_subtype_dot]
  have hsq : ∀ u v,
      ((M.transpose *ᵥ e.symm (u, v)) ⬝ᵥ (M.transpose *ᵥ e.symm (u, v))) =
        ∑ j, (w u j) ^ 2 := by
    intro u v
    have hx : e.symm (u, v) = fun i ↦ if h : p i then u ⟨i, h⟩ else v ⟨i, h⟩ := by
      ext i; exact happ u v i
    rw [hx]
    simpa [w, sq] using maskedTranspose_sq_blocks A δ u v
  let φ : (Fin n → ℝ) → ℝ :=
    fun x ↦ Real.exp (αcoef * ((M.transpose *ᵥ x) ⬝ᵥ (M.transpose *ᵥ x)))
  have hcutT : 64 * K ^ 2 * αcoef * realMatrixOperatorNorm M.transpose ^ 2 ≤ 1 / 4 := by
    rw [realMatrixOperatorNorm_transpose]
    have hfac : 64 * K ^ 2 * αcoef = 2048 * K ^ 4 * θ ^ 2 := by
      simp only [αcoef]
      ring
    rw [hfac, mul_assoc]
    simpa [mul_assoc] using hcut
  have hφ := integral_exp_mulVec_sq_subgaussian ν hK hα hsub M.transpose hcutT
  have hcoe : ((⟨64 * K ^ 2, by positivity⟩ : ℝ≥0) : ℝ) = 64 * K ^ 2 := rfl
  have hJindep : iIndepFun (fun (j : {j // ¬ p j}) (v : {j // ¬ p j} → ℝ) ↦ v j) ρJ :=
    iIndepFun_pi (fun _ ↦ aemeasurable_id)
  have hc : ∀ j : {j // ¬ p j}, HasSubgaussianMGF (fun v : {j // ¬ p j} → ℝ ↦ v j)
      (⟨64 * K ^ 2, by positivity⟩ : ℝ≥0) ρJ :=
    fun j ↦ hasSubgaussianMGF_pi_eval (fun j : {j // ¬ p j} ↦ ν j.1) (fun j ↦ hsub j.1) j
  have hlin : ∀ u : {i // p i} → ℝ,
      Integrable (fun v : {j // ¬ p j} → ℝ ↦ Real.exp (θ * ∑ j, w u j * v j)) ρJ ∧
      ∫ v : {j // ¬ p j} → ℝ, Real.exp (θ * ∑ j, w u j * v j) ∂ρJ ≤
        Real.exp (αcoef * ∑ j, (w u j) ^ 2) := by
    intro u
    have hbound := integral_exp_linear_of_subgaussian
      (fun j (v : {j // ¬ p j} → ℝ) ↦ v j) hJindep hc (w u) θ
    have hpow : ((⟨64 * K ^ 2, by positivity⟩ : ℝ≥0) : ℝ) * (∑ j, (w u j) ^ 2) * θ ^ 2 / 2 =
        αcoef * ∑ j, (w u j) ^ 2 := by
      rw [hcoe]
      simp only [αcoef]
      ring_nf
    exact ⟨hbound.1, hbound.2.trans_eq (congrArg Real.exp hpow)⟩
  let f : ({i // p i} → ℝ) × ({i // ¬ p i} → ℝ) → ℝ :=
    fun q ↦ Real.exp (θ * bernoulliSlice A δ (e.symm q))
  have hf_meas : Measurable f := by
    have hcont : Continuous (fun x : Fin n → ℝ ↦ bernoulliSlice A δ x) := by
      unfold bernoulliSlice
      refine continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦ ?_
      by_cases h : δ i = true ∧ δ j = false
      · simp only [ite_eq_left h]
        fun_prop
      · simp only [ite_eq_right h]
        exact continuous_const
    have hsymm : Continuous (fun q : ({i // p i} → ℝ) × ({i // ¬ p i} → ℝ) ↦
        (e.symm q : Fin n → ℝ)) := by
      refine continuous_pi fun i ↦ ?_
      by_cases hi : p i
      · have hfun : (fun q : ({i // p i} → ℝ) × ({i // ¬ p i} → ℝ) ↦ e.symm q i) =
            fun q ↦ q.1 ⟨i, hi⟩ := by
          ext q
          rw [happ q.1 q.2 i, dite_eq_left hi]
        rw [hfun]
        exact (continuous_apply (⟨i, hi⟩ : {x // p x})).comp continuous_fst
      · have hfun : (fun q : ({i // p i} → ℝ) × ({i // ¬ p i} → ℝ) ↦ e.symm q i) =
            fun q ↦ q.2 ⟨i, hi⟩ := by
          ext q
          rw [happ q.1 q.2 i, dite_eq_right hi]
        rw [hfun]
        exact (continuous_apply (⟨i, hi⟩ : {x // ¬ p x})).comp continuous_snd
    have hfun : Continuous (fun q : ({i // p i} → ℝ) × ({i // ¬ p i} → ℝ) ↦
        bernoulliSlice A δ (e.symm q)) := hcont.comp hsymm
    fun_prop
  have hint_inner : ∀ u, Integrable (fun v ↦ f (u, v)) ρJ := by
    intro u
    simpa [f, hslice] using (hlin u).1
  have hdom : ∀ u, ∫ v, ‖f (u, v)‖ ∂ρJ ≤ Real.exp (αcoef * ∑ j, (w u j) ^ 2) := by
    intro u
    calc
      ∫ v, ‖f (u, v)‖ ∂ρJ = ∫ v, Real.exp (θ * ∑ j, w u j * v j) ∂ρJ := by
        refine integral_congr_ae (ae_of_all _ fun v ↦ ?_)
        change ‖f (u, v)‖ = Real.exp (θ * ∑ j, w u j * v j)
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        simp [hslice]
      _ ≤ Real.exp (αcoef * ∑ j, (w u j) ^ 2) := (hlin u).2
  let g : ({i // p i} → ℝ) → ℝ := fun u ↦ Real.exp (αcoef * ∑ j, (w u j) ^ 2)
  have hφeq : ∀ u v, φ (e.symm (u, v)) = g u := by
    intro u v
    simp [φ, g, hsq]
  have hprodφ : Integrable (φ ∘ e.symm) (ρI.prod ρJ) :=
    he.symm.integrable_comp_of_integrable hφ.1
  have hconst : (fun q : ({i // p i} → ℝ) × ({i // ¬ p i} → ℝ) ↦ g q.1) =
      fun q ↦ φ (e.symm q) := by
    ext q
    exact (hφeq q.1 q.2).symm
  have hg_prod : Integrable (fun q ↦ g q.1) (ρI.prod ρJ) := by
    rw [hconst]
    exact hprodφ
  have hJne : ρJ ≠ 0 := by
    intro h0
    have := IsProbabilityMeasure.measure_univ (μ := ρJ)
    simp [h0] at this
  have hg_int : Integrable g ρI := hg_prod.of_comp_fst hJne
  have hint_norm : Integrable (fun u ↦ ∫ v, ‖f (u, v)‖ ∂ρJ) ρI := by
    refine Integrable.mono' hg_int (by
      have hfsm : StronglyMeasurable f := hf_meas.stronglyMeasurable
      exact hfsm.norm.integral_prod_right'.aestronglyMeasurable) ?_
    filter_upwards with u
    have hnn : 0 ≤ ∫ v, ‖f (u, v)‖ ∂ρJ := integral_nonneg fun _ ↦ norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hdom u
  have hint_f : Integrable f (ρI.prod ρJ) :=
    (integrable_prod_iff hf_meas.aestronglyMeasurable).2
      ⟨ae_of_all _ hint_inner, hint_norm⟩
  have hint_full : Integrable (fun x ↦ Real.exp (θ * bernoulliSlice A δ x)) ρ := by
    have hint_comp : Integrable (f ∘ e) ρ := he.integrable_comp_of_integrable hint_f
    have hfun : f ∘ e = fun x ↦ Real.exp (θ * bernoulliSlice A δ x) := by
      ext x
      simp only [f, Function.comp]
      rw [e.symm_apply_apply]
    simpa [hfun] using hint_comp
  refine ⟨hint_full, ?_⟩
  have hback : ∫ u, g u ∂ρI = ∫ x, φ x ∂ρ := by
    calc
      ∫ u, g u ∂ρI = ∫ u, ∫ v, g u ∂ρJ ∂ρI := by
        refine (integral_congr_ae (ae_of_all _ fun u ↦ ?_)).symm
        simp [integral_const, probReal_univ]
      _ = ∫ q, g q.1 ∂(ρI.prod ρJ) := (integral_prod (fun q ↦ g q.1) hg_prod).symm
      _ = ∫ q, φ (e.symm q) ∂(ρI.prod ρJ) := by rw [hconst]
      _ = ∫ x, φ x ∂ρ := he.symm.integral_comp' φ
  calc
    ∫ x, Real.exp (θ * bernoulliSlice A δ x) ∂ρ =
        ∫ q, f q ∂(ρI.prod ρJ) := by
      have hfe : (fun x ↦ f (e x)) = fun x ↦ Real.exp (θ * bernoulliSlice A δ x) := by
        ext x
        simp only [f]
        rw [e.symm_apply_apply]
      rw [← hfe]
      exact he.integral_comp' f
    _ = ∫ u, ∫ v, f (u, v) ∂ρJ ∂ρI := integral_prod _ hint_f
    _ ≤ ∫ u, g u ∂ρI := by
      refine integral_mono hint_f.integral_prod_left hg_int fun u ↦ ?_
      simpa [f, g, hslice] using (hlin u).2
    _ = ∫ x, φ x ∂ρ := hback
    _ ≤ Real.exp (128 * K ^ 2 * αcoef * realMatrixFrobeniusSq M.transpose) := hφ.2
    _ = Real.exp (4096 * K ^ 4 * θ ^ 2 * realMatrixFrobeniusSq M) := by
      rw [realMatrixFrobeniusSq_transpose]
      simp only [αcoef]
      ring_nf

/-- A matrix cut dominates the Boolean-slice cut. -/
lemma masked_slice_cut {K lam opA opM : ℝ}
    (hop : 0 ≤ opM) (hle : opM ≤ opA)
    (hcut : 131072 * K ^ 4 * lam ^ 2 * opA ^ 2 ≤ 1) :
    2048 * K ^ 4 * (4 * lam) ^ 2 * opM ^ 2 ≤ 1 / 4 := by
  have hsq : opM ^ 2 ≤ opA ^ 2 := pow_le_pow_left₀ hop hle 2
  have hleft : 32768 * K ^ 4 * lam ^ 2 * opM ^ 2 ≤ 32768 * K ^ 4 * lam ^ 2 * opA ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hsq
      (by positivity : 0 ≤ 32768 * K ^ 4 * lam ^ 2)
    simpa [mul_assoc] using hmul
  have hparent : 32768 * K ^ 4 * lam ^ 2 * opA ^ 2 ≤ 1 / 4 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    have h4 : 4 * (32768 * K ^ 4 * lam ^ 2 * opA ^ 2) ≤ 1 := by
      have hnum : (4 : ℝ) * 32768 = 131072 := by norm_num
      calc
        4 * (32768 * K ^ 4 * lam ^ 2 * opA ^ 2) = 131072 * K ^ 4 * lam ^ 2 * opA ^ 2 := by
          rw [← hnum]
          ring_nf
        _ ≤ 1 := hcut
    calc
      32768 * K ^ 4 * lam ^ 2 * opA ^ 2 * 4 = 4 * (32768 * K ^ 4 * lam ^ 2 * opA ^ 2) := by
        ring_nf
      _ ≤ 1 := h4
  have hfac : 2048 * K ^ 4 * (4 * lam) ^ 2 * opM ^ 2 = 32768 * K ^ 4 * lam ^ 2 * opM ^ 2 := by
    ring_nf
  calc
    2048 * K ^ 4 * (4 * lam) ^ 2 * opM ^ 2 = 32768 * K ^ 4 * lam ^ 2 * opM ^ 2 := hfac
    _ ≤ 32768 * K ^ 4 * lam ^ 2 * opA ^ 2 := hleft
    _ ≤ 1 / 4 := hparent

/-- The off-diagonal exponential moment is at most the Frobenius quadratic. -/
lemma integral_exp_offDiagonal_le (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    {K lam : ℝ} (hK : 0 < K)
    (hsub : ∀ i, HasSubgaussianMGF id (⟨64 * K ^ 2, by positivity⟩ : ℝ≥0) (ν i))
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hcut : 131072 * K ^ 4 * lam ^ 2 * realMatrixOperatorNorm A ^ 2 ≤ 1) :
    Integrable (fun x ↦ Real.exp (lam * offDiagonalForm A x)) (Measure.pi ν) ∧
      ∫ x, Real.exp (lam * offDiagonalForm A x) ∂Measure.pi ν ≤
        Real.exp (65536 * K ^ 4 * lam ^ 2 * realMatrixFrobeniusSq A) := by
  let ρ := Measure.pi ν
  have hslice : ∀ δ : Fin n → Bool,
      Integrable (fun x ↦ Real.exp ((4 * lam) * bernoulliSlice A δ x)) ρ ∧
        ∫ x, Real.exp ((4 * lam) * bernoulliSlice A δ x) ∂ρ ≤
          Real.exp (65536 * K ^ 4 * lam ^ 2 * realMatrixFrobeniusSq A) := by
    intro δ
    have hcutδ := masked_slice_cut (realMatrixOperatorNorm_nonneg _)
      (maskedMatrix_opNorm_le A δ) hcut
    have hbound := integral_exp_bernoulliSlice_le ν hK hsub A δ hcutδ
    refine ⟨hbound.1, hbound.2.trans ?_⟩
    apply Real.exp_le_exp.mpr
    have hF := maskedMatrix_frobenius_le A δ
    have hnum : 4096 * K ^ 4 * (4 * lam) ^ 2 * realMatrixFrobeniusSq (maskedMatrix A δ) =
        65536 * K ^ 4 * lam ^ 2 * realMatrixFrobeniusSq (maskedMatrix A δ) := by ring
    rw [hnum]
    have hcoef : 0 ≤ 65536 * K ^ 4 * lam ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hF hcoef
  have hintSum : Integrable (fun x ↦ ∑ δ : Fin n → Bool,
      Real.exp (4 * lam * bernoulliSlice A δ x)) ρ :=
    integrable_finsetSum _ fun δ _ ↦ (hslice δ).1
  have hintAvg : Integrable (fun x ↦ (∑ δ : Fin n → Bool,
      Real.exp (4 * lam * bernoulliSlice A δ x)) / (2 : ℝ) ^ n) ρ := hintSum.div_const _
  have hcont : Continuous (fun x : Fin n → ℝ ↦ Real.exp (lam * offDiagonalForm A x)) := by
    have hoff : Continuous (fun x : Fin n → ℝ ↦ offDiagonalForm A x) := by
      unfold offDiagonalForm
      refine continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦ ?_
      by_cases hij : i = j
      · simp only [ite_eq_left hij]
        exact continuous_const
      · simp only [ite_eq_right hij]
        fun_prop
    fun_prop
  have hintExp : Integrable (fun x ↦ Real.exp (lam * offDiagonalForm A x)) ρ := by
    refine Integrable.mono hintAvg hcont.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs,
      abs_of_nonneg (by positivity :
        0 ≤ (∑ δ : Fin n → Bool, Real.exp (4 * lam * bernoulliSlice A δ x)) / (2 : ℝ) ^ n)]
    exact exp_offDiagonal_le_avg A x lam
  refine ⟨hintExp, ?_⟩
  calc
    ∫ x, Real.exp (lam * offDiagonalForm A x) ∂ρ ≤
        ∫ x, (∑ δ : Fin n → Bool, Real.exp (4 * lam * bernoulliSlice A δ x)) /
          (2 : ℝ) ^ n ∂ρ := by
      refine integral_mono hintExp hintAvg fun x ↦ exp_offDiagonal_le_avg A x lam
    _ = (∑ δ : Fin n → Bool, ∫ x, Real.exp (4 * lam * bernoulliSlice A δ x) ∂ρ) /
          (2 : ℝ) ^ n := by
      rw [integral_div, integral_finsetSum _ fun δ _ ↦ (hslice δ).1]
    _ ≤ (∑ δ : Fin n → Bool,
          Real.exp (65536 * K ^ 4 * lam ^ 2 * realMatrixFrobeniusSq A)) / (2 : ℝ) ^ n := by
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact Finset.sum_le_sum fun δ _ ↦ (hslice δ).2
    _ = Real.exp (65536 * K ^ 4 * lam ^ 2 * realMatrixFrobeniusSq A) := by
      have hcard : (Fintype.card (Fin n → Bool) : ℝ) = (2 : ℝ) ^ n := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
        norm_cast
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
      exact mul_div_cancel_left₀ _ (by positivity)

/-- The same off-diagonal moment on the original coordinate space. -/
lemma integral_exp_offDiagonalForm_le [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    (hcent : ∀ i, ∫ ω, X i ω ∂μ = 0) {K : ℝ} (hK : 0 < K)
    (hpsi : ∀ i, HasPsiTwoBound (X i) μ (2 * K)) (A : Matrix (Fin n) (Fin n) ℝ) {lam : ℝ}
    (hcut : 131072 * K ^ 4 * lam ^ 2 * realMatrixOperatorNorm A ^ 2 ≤ 1) :
    Integrable (fun ω ↦ Real.exp (lam * offDiagonalForm A (fun i ↦ X i ω))) μ ∧
      ∫ ω, Real.exp (lam * offDiagonalForm A (fun i ↦ X i ω)) ∂μ ≤
        Real.exp (65536 * K ^ 4 * lam ^ 2 * realMatrixFrobeniusSq A) := by
  let ν : Fin n → Measure ℝ := fun i ↦ μ.map (X i)
  have hsub : ∀ i, HasSubgaussianMGF id (⟨64 * K ^ 2, by positivity⟩ : ℝ≥0) (ν i) := by
    intro i
    exact (HasSubgaussianMGF.id_map_iff (hmeas i).aemeasurable).2
      (hasSubgaussianMGF_scale (hmeas i) (hcent i) (hpsi i))
  have hprod := integral_exp_offDiagonal_le ν hK hsub A hcut
  let Φ : Ω → Fin n → ℝ := fun ω i ↦ X i ω
  have hΦ : AEMeasurable Φ μ := (measurable_pi_iff.mpr hmeas).aemeasurable
  have hmap := iIndepFun.map_fun_eq_pi_map (fun i ↦ (hmeas i).aemeasurable) hindep
  have hfm : AEStronglyMeasurable (fun x ↦ Real.exp (lam * offDiagonalForm A x)) (μ.map Φ) := by
    rw [hmap]
    exact hprod.1.aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · have hint : Integrable (fun x ↦ Real.exp (lam * offDiagonalForm A x)) (μ.map Φ) := by
      rw [hmap]
      exact hprod.1
    have hcomp := hint.comp_aemeasurable hΦ
    refine hcomp.congr ?_
    filter_upwards with ω
    simp [Φ, Function.comp]
  · have heq := integral_map (φ := Φ) hΦ hfm
    rw [hmap] at heq
    have hgoal : ∫ y, Real.exp (lam * offDiagonalForm A y) ∂Measure.pi (fun i ↦ μ.map (X i)) =
        ∫ ω, Real.exp (lam * offDiagonalForm A (fun i ↦ X i ω)) ∂μ := by
      simpa [Φ] using heq
    exact hgoal.symm.trans_le hprod.2

/-- Off-diagonal deviation at a fixed positive level. -/
lemma offDiagonalDeviation_tail [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    (hcent : ∀ i, ∫ ω, X i ω ∂μ = 0) {K : ℝ} (hK : 0 < K)
    (hpsi : ∀ i, HasPsiTwoBound (X i) μ (2 * K)) (A : Matrix (Fin n) (Fin n) ℝ) {t : ℝ}
    (ht : 0 < t) :
    μ {ω | t < |offDiagonalForm A (fun i ↦ X i ω)|} ≤
      ENNReal.ofReal (2 * Real.exp (-(1 / 262144) * min
        (t ^ 2 / (K ^ 4 * realMatrixFrobeniusSq A))
        (t / (K ^ 2 * realMatrixOperatorNorm A)))) := by
  by_cases hop0 : realMatrixOperatorNorm A = 0
  · have hA : A = 0 := (realMatrixOperatorNorm_eq_zero_iff A).mp hop0
    have hempty : {ω | t < |offDiagonalForm A (fun i ↦ X i ω)|} = ∅ := by
      ext ω
      simp [offDiagonalForm, hA, abs_zero, not_lt.mpr ht.le]
    simp [hempty]
  · have hop : 0 < realMatrixOperatorNorm A :=
      lt_of_le_of_ne (realMatrixOperatorNorm_nonneg A) (Ne.symm hop0)
    have hF : 0 < realMatrixFrobeniusSq A := by
      have hsq := realMatrixOperatorNorm_sq_le_frobenius A
      nlinarith
    let O : Ω → ℝ := fun ω ↦ offDiagonalForm A (fun i ↦ X i ω)
    let Q : ℝ := 65536 * K ^ 4 * realMatrixFrobeniusSq A
    let cap : ℝ := 1 / (512 * K ^ 2 * realMatrixOperatorNorm A)
    have hQ : 0 < Q := by positivity
    have hcap : 0 < cap := by positivity
    have hscale : ∀ s : ℝ, 0 ≤ s → s ≤ cap →
        131072 * K ^ 4 * s ^ 2 * realMatrixOperatorNorm A ^ 2 ≤ 1 := by
      intro s hs0 hscap
      have hsop : s * (K ^ 2 * realMatrixOperatorNorm A) ≤ 1 / 512 := by
        calc
          s * (K ^ 2 * realMatrixOperatorNorm A) ≤
              cap * (K ^ 2 * realMatrixOperatorNorm A) := by
            gcongr
          _ = 1 / 512 := by
            simp only [cap]
            field_simp
      have hsqle : (s * (K ^ 2 * realMatrixOperatorNorm A)) ^ 2 ≤ (1 / 512) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hsop 2
      have hnum : (131072 : ℝ) * (1 / 512) ^ 2 = 1 / 2 := by norm_num
      have hcoef : 131072 * (s * (K ^ 2 * realMatrixOperatorNorm A)) ^ 2 ≤ 1 / 2 := by
        calc
          131072 * (s * (K ^ 2 * realMatrixOperatorNorm A)) ^ 2 ≤
              131072 * (1 / 512) ^ 2 := by gcongr
          _ = 1 / 2 := hnum
      have hrewrite : 131072 * (s * (K ^ 2 * realMatrixOperatorNorm A)) ^ 2 =
          131072 * K ^ 4 * s ^ 2 * realMatrixOperatorNorm A ^ 2 := by ring
      linarith
    have hOmgf : ∀ s : ℝ, 0 ≤ s → s ≤ cap →
        Integrable (fun ω ↦ Real.exp (s * O ω)) μ ∧
          ∫ ω, Real.exp (s * O ω) ∂μ ≤ Real.exp (Q * s ^ 2) := by
      intro s hs0 hscap
      have hbound := integral_exp_offDiagonalForm_le X hmeas hindep hcent hK hpsi A
        (hscale s hs0 hscap)
      refine ⟨hbound.1, hbound.2.trans_eq ?_⟩
      congr 1
      simp only [Q]
      ring_nf
    have hneg : ∀ s : ℝ, 0 ≤ s → s ≤ cap →
        Integrable (fun ω ↦ Real.exp (s * (-O) ω)) μ ∧
          ∫ ω, Real.exp (s * (-O) ω) ∂μ ≤ Real.exp (Q * s ^ 2) := by
      intro s hs0 hscap
      have hcutNeg : 131072 * K ^ 4 * s ^ 2 * realMatrixOperatorNorm (-A) ^ 2 ≤ 1 := by
        rw [realMatrixOperatorNorm_neg]
        exact hscale s hs0 hscap
      have hbound := integral_exp_offDiagonalForm_le X hmeas hindep hcent hK hpsi (-A) hcutNeg
      have hfun : (fun ω ↦ Real.exp (s * offDiagonalForm (-A) (fun i ↦ X i ω))) =
          fun ω ↦ Real.exp (s * (-O) ω) := by
        ext ω
        rw [offDiagonalForm_neg]
        simp [O]
      rw [hfun] at hbound
      refine ⟨hbound.1, hbound.2.trans_eq ?_⟩
      congr 1
      simp only [Q, realMatrixFrobeniusSq_neg]
      ring_nf
    have hup := measure_ge_of_quad_mgf (Y := O) hQ hcap ht hOmgf
    have hlow := measure_ge_of_quad_mgf (Y := -O) hQ hcap ht hneg
    have hsub : {ω | t < |O ω|} ⊆ {ω | t ≤ O ω} ∪ {ω | t ≤ (-O) ω} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      rcases le_or_gt 0 (O ω) with hpos | hnegO
      · exact Or.inl (by rw [abs_of_nonneg hpos] at hω; exact hω.le)
      · exact Or.inr (by rw [abs_of_neg hnegO] at hω; exact hω.le)
    set r : ℝ := 1 / 262144
    set phi : ℝ := min (t ^ 2 / (K ^ 4 * realMatrixFrobeniusSq A))
      (t / (K ^ 2 * realMatrixOperatorNorm A))
    have hdecay : Real.exp (-min (t ^ 2 / (4 * Q)) (t * cap / 2)) ≤
        Real.exp (-r * phi) := by
      apply Real.exp_le_exp.mpr
      have hquad : t ^ 2 / (4 * Q) =
          (t ^ 2 / (K ^ 4 * realMatrixFrobeniusSq A)) / 262144 := by
        simp only [Q]
        field_simp; ring_nf
      have hlin : t * cap / 2 =
          (t / (K ^ 2 * realMatrixOperatorNorm A)) / 1024 := by
        simp only [cap]
        field_simp; ring_nf
      have hmin : phi / 262144 ≤ min (t ^ 2 / (4 * Q)) (t * cap / 2) := by
        refine le_min ?_ ?_
        · rw [hquad]
          exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
        · rw [hlin]
          have hden : (1024 : ℝ) ≤ 262144 := by norm_num
          have hfrac : phi / 262144 ≤ phi / 1024 :=
            div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
          exact hfrac.trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
      have hr : r * phi = phi / 262144 := by
        simp only [r]
        rw [one_div, mul_comm, ← div_eq_mul_inv]
      have hneg := neg_le_neg (hr.symm ▸ hmin)
      rw [neg_mul_eq_neg_mul] at hneg
      exact hneg
    have hone := hup.trans (ENNReal.ofReal_le_ofReal hdecay)
    have hother := hlow.trans (ENNReal.ofReal_le_ofReal hdecay)
    have hunion := (measure_mono hsub).trans
      ((measure_union_le _ _).trans (add_le_add hone hother))
    have hadd : ENNReal.ofReal (Real.exp (-r * phi)) + ENNReal.ofReal (Real.exp (-r * phi)) =
        ENNReal.ofReal (2 * Real.exp (-r * phi)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring_nf
    simpa [O, r, phi] using hunion.trans_eq hadd

/-- Diagonal and off-diagonal tails give a uniform Hanson–Wright constant. -/
lemma hanson_wright_explicit :
    ∀ (n : ℕ) (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : Fin n → Ω → ℝ), (∀ i, Measurable (X i)) → iIndepFun X μ →
      (∀ i, ∫ ω, X i ω ∂μ = 0) →
      ∀ K : ℝ, 0 < K → (∀ i, psiTwoGauge (X i) μ ≤ ENNReal.ofReal K) →
      ∀ (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ), 0 < t →
      μ {ω | t < |sampledQuadraticForm A X ω - ∫ η, sampledQuadraticForm A X η ∂μ|} ≤
        ENNReal.ofReal (2 * Real.exp (-(1 / 2359296) * min
          (t ^ 2 / (K ^ 4 * realMatrixFrobeniusSq A))
          (t / (K ^ 2 * realMatrixOperatorNorm A)))) := by
  intro n Ω _ μ _ X hmeas hindep hcent K hK hgauge A t ht
  have hpsi : ∀ i, HasPsiTwoBound (X i) μ (2 * K) :=
    fun i ↦ hasPsiTwoBound_of_psiTwoGauge_le hK (hgauge i)
  let c : ℝ := 1 / 2359296
  let phi : ℝ := min (t ^ 2 / (K ^ 4 * realMatrixFrobeniusSq A))
    (t / (K ^ 2 * realMatrixOperatorNorm A))
  by_cases hsmall : c * phi ≤ Real.log 2
  · have hμle : μ {ω | t < |sampledQuadraticForm A X ω -
        ∫ η, sampledQuadraticForm A X η ∂μ|} ≤ 1 := prob_le_one
    have h1 : (1 : ℝ) ≤ 2 * Real.exp (-c * phi) := by
      have hneg : -Real.log 2 ≤ -c * phi := by linarith
      have hexp : Real.exp (-Real.log 2) ≤ Real.exp (-c * phi) := Real.exp_le_exp.mpr hneg
      have hhalf : Real.exp (-Real.log 2) = 1 / 2 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num), inv_eq_one_div]
      linarith
    rw [← ENNReal.ofReal_one] at hμle
    exact hμle.trans (ENNReal.ofReal_le_ofReal h1)
  · have hlog : Real.log 2 < c * phi := lt_of_not_ge hsmall
    have hcpos : 0 < c := by norm_num
    have hphi : 0 < phi := by
      have hpos : 0 < c * phi := lt_trans (Real.log_pos (by norm_num)) hlog
      exact (mul_pos_iff_of_pos_left hcpos).mp hpos
    have hF : 0 < realMatrixFrobeniusSq A := by
      by_contra hnon
      have h0 : realMatrixFrobeniusSq A = 0 :=
        le_antisymm (le_of_not_gt hnon) (realMatrixFrobeniusSq_nonneg A)
      have hle : phi ≤ 0 := by
        dsimp [phi]
        rw [h0, mul_zero, div_zero]
        exact min_le_left _ _
      linarith
    have hop : 0 < realMatrixOperatorNorm A := by
      by_contra hnon
      have h0 : realMatrixOperatorNorm A = 0 :=
        le_antisymm (le_of_not_gt hnon) (realMatrixOperatorNorm_nonneg A)
      have hle : phi ≤ 0 := by
        dsimp [phi]
        rw [h0, mul_zero, div_zero]
        exact min_le_right _ _
      linarith
    let half : ℝ := t / 2
    have hhalf : 0 < half := by positivity
    let D : Ω → ℝ := fun ω ↦ ∑ i, A i i * (X i ω ^ 2 - ∫ η, X i η ^ 2 ∂μ)
    let O : Ω → ℝ := fun ω ↦ offDiagonalForm A (fun i ↦ X i ω)
    have hcenter := centeredQuadratic_eq_diag_add_off X hmeas hindep hcent hpsi A
    have hset : {ω | t < |sampledQuadraticForm A X ω - ∫ η, sampledQuadraticForm A X η ∂μ|} ⊆
        {ω | half < |D ω|} ∪ {ω | half < |O ω|} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [hcenter ω] at hω
      by_contra hnot
      simp only [Set.mem_ofPred_eq, Set.mem_union] at hnot
      rw [not_or] at hnot
      have hDle : |D ω| ≤ half := not_lt.mp hnot.1
      have hOle : |O ω| ≤ half := not_lt.mp hnot.2
      have habs : |D ω + O ω| ≤ t := by
        calc
          |D ω + O ω| ≤ |D ω| + |O ω| := abs_add_le _ _
          _ ≤ half + half := add_le_add hDle hOle
          _ = t := by simp [half]
      exact not_lt.mpr habs hω
    have hdiag := diagonalDeviation_tail X hmeas hindep hK hpsi A hhalf
    have hoff := offDiagonalDeviation_tail X hmeas hindep hcent hK hpsi A hhalf
    have hψ : phi / 4 ≤ min ((t / 2) ^ 2 / (K ^ 4 * realMatrixFrobeniusSq A))
        ((t / 2) / (K ^ 2 * realMatrixOperatorNorm A)) := by
      refine le_min ?_ ?_
      · have hqa : (t / 2) ^ 2 / (K ^ 4 * realMatrixFrobeniusSq A) =
            (t ^ 2 / (K ^ 4 * realMatrixFrobeniusSq A)) / 4 := by
          field_simp; norm_num
        rw [hqa]
        exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      · have hqb : (t / 2) / (K ^ 2 * realMatrixOperatorNorm A) =
            (t / (K ^ 2 * realMatrixOperatorNorm A)) / 2 := by
          field_simp
        rw [hqb]
        have htwo : phi / 4 ≤ phi / 2 :=
          div_le_div_of_nonneg_left (le_of_lt hphi) (by norm_num) (by norm_num)
        have hhalfb : phi / 2 ≤ (t / (K ^ 2 * realMatrixOperatorNorm A)) / 2 :=
          div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
        exact htwo.trans hhalfb
    have hdiagRate : (1 / (32768 * (Real.exp 1) ^ 2)) *
        min ((t / 2) ^ 2 / (K ^ 4 * realMatrixFrobeniusSq A))
          ((t / 2) / (K ^ 2 * realMatrixOperatorNorm A)) ≥ phi / 1179648 := by
      have hcd : (1 / (32768 * (Real.exp 1) ^ 2)) * (phi / 4) =
          phi / (131072 * (Real.exp 1) ^ 2) := by
        field_simp; ring_nf
      have hden : 131072 * (Real.exp 1) ^ 2 < 1179648 := by
        have he2 : (Real.exp 1) ^ 2 < 9 := by
          calc
            (Real.exp 1) ^ 2 < 3 ^ 2 := by
              gcongr
              exact Real.exp_one_lt_three
            _ = 9 := by norm_num
        have hnine : (131072 : ℝ) * 9 = 1179648 := by norm_num
        calc
          131072 * (Real.exp 1) ^ 2 < 131072 * 9 :=
            mul_lt_mul_of_pos_left he2 (by norm_num)
          _ = 1179648 := hnine
      have hcmp : phi / 1179648 ≤ phi / (131072 * (Real.exp 1) ^ 2) :=
        div_le_div_of_nonneg_left (le_of_lt hphi) (by positivity) hden.le
      calc
        phi / 1179648 ≤ phi / (131072 * (Real.exp 1) ^ 2) := hcmp
        _ = (1 / (32768 * (Real.exp 1) ^ 2)) * (phi / 4) := by rw [hcd]
        _ ≤ (1 / (32768 * (Real.exp 1) ^ 2)) *
            min ((t / 2) ^ 2 / (K ^ 4 * realMatrixFrobeniusSq A))
              ((t / 2) / (K ^ 2 * realMatrixOperatorNorm A)) := by
          gcongr
    have hDdecay : Real.exp (-(1 / (32768 * (Real.exp 1) ^ 2)) *
        min ((t / 2) ^ 2 / (K ^ 4 * realMatrixFrobeniusSq A))
          ((t / 2) / (K ^ 2 * realMatrixOperatorNorm A))) ≤
        Real.exp (-(phi / 1179648)) := by
      apply Real.exp_le_exp.mpr
      simpa [neg_mul] using neg_le_neg hdiagRate
    have hOdecay : Real.exp (-(1 / 262144) *
        min ((t / 2) ^ 2 / (K ^ 4 * realMatrixFrobeniusSq A))
          ((t / 2) / (K ^ 2 * realMatrixOperatorNorm A))) ≤
        Real.exp (-(phi / 1179648)) := by
      apply Real.exp_le_exp.mpr
      suffices hneg : -((1 / 262144) *
          min ((t / 2) ^ 2 / (K ^ 4 * realMatrixFrobeniusSq A))
            ((t / 2) / (K ^ 2 * realMatrixOperatorNorm A))) ≤ -(phi / 1179648) by
        rw [neg_mul_eq_neg_mul] at hneg
        exact hneg
      refine neg_le_neg ?_
      have hmul : (1 / 262144) * (phi / 4) ≤ (1 / 262144) *
          min ((t / 2) ^ 2 / (K ^ 4 * realMatrixFrobeniusSq A))
            ((t / 2) / (K ^ 2 * realMatrixOperatorNorm A)) :=
        mul_le_mul_of_nonneg_left hψ (by norm_num)
      have hprod : (1 / 262144) * (phi / 4) = phi / 1048576 := by ring_nf
      have hden : (1048576 : ℝ) ≤ 1179648 := by norm_num
      have hfrac : phi / 1179648 ≤ phi / 1048576 :=
        div_le_div_of_nonneg_left (le_of_lt hphi) (by norm_num) hden
      calc
        phi / 1179648 ≤ phi / 1048576 := hfrac
        _ = (1 / 262144) * (phi / 4) := hprod.symm
        _ ≤ (1 / 262144) *
            min ((t / 2) ^ 2 / (K ^ 4 * realMatrixFrobeniusSq A))
              ((t / 2) / (K ^ 2 * realMatrixOperatorNorm A)) := hmul
    have hDone : μ {ω | half < |D ω|} ≤
        ENNReal.ofReal (2 * Real.exp (-(phi / 1179648))) :=
      hdiag.trans (ENNReal.ofReal_le_ofReal (by
        simp only [half]
        exact mul_le_mul_of_nonneg_left hDdecay (by norm_num)))
    have hOone : μ {ω | half < |O ω|} ≤
        ENNReal.ofReal (2 * Real.exp (-(phi / 1179648))) :=
      hoff.trans (ENNReal.ofReal_le_ofReal (by
        simp only [half]
        exact mul_le_mul_of_nonneg_left hOdecay (by norm_num)))
    have hunion := (measure_mono hset).trans
      ((measure_union_le _ _).trans (add_le_add hDone hOone))
    have hadd : ENNReal.ofReal (2 * Real.exp (-(phi / 1179648))) +
        ENNReal.ofReal (2 * Real.exp (-(phi / 1179648))) =
        ENNReal.ofReal (4 * Real.exp (-(phi / 1179648))) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring_nf
    have hfour : 4 * Real.exp (-(phi / 1179648)) ≤ 2 * Real.exp (-c * phi) := by
      have hexp : (2 : ℝ) ≤ Real.exp (c * phi) := by
        calc
          (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
          _ ≤ Real.exp (c * phi) := Real.exp_le_exp.mpr hlog.le
      have hinner : 2 * Real.exp (-(phi / 1179648)) ≤
          Real.exp (c * phi) * Real.exp (-(phi / 1179648)) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
      calc
        4 * Real.exp (-(phi / 1179648)) =
            2 * (2 * Real.exp (-(phi / 1179648))) := by ring_nf
        _ ≤ 2 * (Real.exp (c * phi) * Real.exp (-(phi / 1179648))) := by
          gcongr
        _ = 2 * Real.exp (-c * phi) := by
          have hsum : c * phi + -(phi / 1179648) = -c * phi := by
            have htwo : (2 : ℝ) * c = 1 / 1179648 := by
              simp only [c]
              norm_num
            calc
              c * phi + -(phi / 1179648) = c * phi - phi / 1179648 := by
                rw [← sub_eq_add_neg]
              _ = c * phi - phi * (1 / 1179648) := by rw [div_eq_mul_one_div]
              _ = c * phi - phi * (2 * c) := by rw [← htwo]
              _ = -c * phi := by ring_nf
          rw [← Real.exp_add, hsum]
    have hreal : 4 * Real.exp (-(phi / 1179648)) ≤ 2 * Real.exp (-c * phi) := hfour
    have hfinal := hunion.trans_eq hadd |>.trans (ENNReal.ofReal_le_ofReal hreal)
    simpa [c, phi, D, O] using hfinal

end CKMA
