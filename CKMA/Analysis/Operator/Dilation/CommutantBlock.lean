/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Operator.Dilation.CommutantDefect
public import CKMA.Analysis.Operator.Dilation.CommutantFactor
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# Blocks of the commutant lifting iteration

An operator `X` commuting with a contraction is compressed by the co-invariant embedding.
Each block of the lifting series is a contraction factor of the previous block through the
square root of the positive remainder `‖X‖² - X₀* X₀ - Σ Bₖ* Bₖ`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped InnerProductSpace
open ContinuousLinearMap

universe u

variable {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The compression `X J*` of an operator on the original space. -/
def coextensionCompress (X : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) : K →L[ℂ] H :=
  X.comp J.toContinuousLinearMap.adjoint

/-- Co-invariance and commutation give `T X₀ = X₀ V`. -/
theorem coextensionCompress_intertwine (T X : H →L[ℂ] H) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) :
    T.comp (coextensionCompress X J) =
      (coextensionCompress X J).comp V.toContinuousLinearMap := by
  have hcoin' : J.toContinuousLinearMap.adjoint.comp V.toContinuousLinearMap =
      T.comp J.toContinuousLinearMap.adjoint := by
    ext y
    simpa [coextensionCompress, comp_apply, LinearIsometry.coe_toContinuousLinearMap] using
      hcoin y
  have hcomm : X.comp T = T.comp X := by
    simpa [mul_def] using hXT.eq
  rw [coextensionCompress, ← comp_assoc, ← hcomm, comp_assoc, ← hcoin', comp_assoc]

/-- Pointwise form of the compressed intertwining relation. -/
theorem coextensionCompress_apply_V (T X : H →L[ℂ] H) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (y : K) :
    T (coextensionCompress X J y) = coextensionCompress X J (V y) := by
  have happly := congrArg (fun A : K →L[ℂ] H => A y)
    (coextensionCompress_intertwine T X hXT J V hcoin)
  simpa [comp_apply] using happly

/-- The adjoint of an isometric embedding is a contraction. -/
theorem norm_embed_adjoint_le (J : H →ₗᵢ[ℂ] K) :
    ‖J.toContinuousLinearMap.adjoint‖ ≤ 1 := by
  have hJ : ‖J.toContinuousLinearMap‖ ≤ 1 :=
    opNorm_le_bound _ zero_le_one fun x => by
      rw [one_mul, LinearIsometry.coe_toContinuousLinearMap, J.norm_map]
  rw [(ContinuousLinearMap.adjoint (E := H) (F := K)).norm_map J.toContinuousLinearMap]
  exact hJ

/-- Compressing by `J*` does not increase the operator norm. -/
theorem norm_coextensionCompress_le (X : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) :
    ‖coextensionCompress X J‖ ≤ ‖X‖ := by
  rw [coextensionCompress]
  calc
    ‖X.comp J.toContinuousLinearMap.adjoint‖ ≤ ‖X‖ * ‖J.toContinuousLinearMap.adjoint‖ :=
      opNorm_comp_le X _
    _ ≤ ‖X‖ * 1 :=
      mul_le_mul_of_nonneg_left (norm_embed_adjoint_le J) (norm_nonneg X)
    _ = ‖X‖ := mul_one _

omit [CompleteSpace H] in
/-- A contraction does not increase vector norms. -/
theorem contraction_norm_apply_le (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x : H) : ‖T x‖ ≤ ‖x‖ := by
  have hmul : ‖T‖ * ‖x‖ ≤ 1 * ‖x‖ :=
    mul_le_mul_of_nonneg_right hT (norm_nonneg x)
  rw [one_mul] at hmul
  exact (le_opNorm T x).trans hmul

/-- Pointwise squared norm of the compression. -/
theorem coextensionCompress_apply_norm_sq_le (X : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (y : K) :
    ‖coextensionCompress X J y‖ ^ 2 ≤ ‖X‖ ^ 2 * ‖y‖ ^ 2 := by
  have hle : ‖coextensionCompress X J y‖ ≤ ‖X‖ * ‖y‖ :=
    (le_opNorm _ y).trans
      (mul_le_mul_of_nonneg_right (norm_coextensionCompress_le X J) (norm_nonneg y))
  calc
    ‖coextensionCompress X J y‖ ^ 2 ≤ (‖X‖ * ‖y‖) ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_self_le_mul_self (norm_nonneg _) hle
    _ = ‖X‖ ^ 2 * ‖y‖ ^ 2 := by ring

omit [CompleteSpace H] [CompleteSpace K] in
/-- Real quadratic form of a real multiple of the identity. -/
theorem re_inner_smul_one (c : ℝ) (y : K) :
    RCLike.re ⟪(Complex.ofReal c • (1 : K →L[ℂ] K)) y, y⟫_ℂ = c * ‖y‖ ^ 2 := by
  have hsmul : (Complex.ofReal c • (1 : K →L[ℂ] K)) y = Complex.ofReal c • y := by
    rw [smul_apply, one_apply_eq_self]
  have hinner : ⟪Complex.ofReal c • y, y⟫_ℂ = Complex.ofReal c * ⟪y, y⟫_ℂ := by
    simpa [Complex.star_def, Complex.conj_ofReal] using inner_smul_left y y (Complex.ofReal c)
  have hself : ⟪y, y⟫_ℂ = Complex.ofReal (‖y‖ ^ 2) := by
    simp [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
  calc
    RCLike.re ⟪(Complex.ofReal c • (1 : K →L[ℂ] K)) y, y⟫_ℂ
        = RCLike.re ⟪Complex.ofReal c • y, y⟫_ℂ := by rw [hsmul]
    _ = RCLike.re (Complex.ofReal c * ⟪y, y⟫_ℂ) := congrArg RCLike.re hinner
    _ = RCLike.re (Complex.ofReal c * Complex.ofReal (‖y‖ ^ 2)) := by rw [hself]
    _ = RCLike.re (Complex.ofReal (c * ‖y‖ ^ 2)) := by rw [← Complex.ofReal_mul]
    _ = c * ‖y‖ ^ 2 := RCLike.ofReal_re _

/-- Real quadratic form of `A* A`. -/
theorem re_inner_adjoint_comp_self {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A : K →L[ℂ] E) (y : K) :
    RCLike.re ⟪(A.adjoint.comp A) y, y⟫_ℂ = ‖A y‖ ^ 2 :=
  (apply_norm_sq_eq_inner_adjoint_left A y).symm

/-- `A* A` is self-adjoint. -/
theorem isSelfAdjoint_adjoint_comp_self {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (A : K →L[ℂ] E) :
    IsSelfAdjoint (A.adjoint.comp A) := by
  rw [isSelfAdjoint_iff', adjoint_comp, adjoint_adjoint]

omit [CompleteSpace H] in
/-- A real multiple of the identity is self-adjoint. -/
theorem isSelfAdjoint_smul_one_real (c : ℝ) :
    IsSelfAdjoint (Complex.ofReal c • (1 : K →L[ℂ] K)) := by
  rw [isSelfAdjoint_iff, star_smul, star_one, Complex.star_def, Complex.conj_ofReal]

/-- Positive remainder `‖X‖² I - X₀* X₀ - gram`. -/
def commutantRemainder (X : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (gram : K →L[ℂ] K) : K →L[ℂ] K :=
  Complex.ofReal (‖X‖ ^ 2) • (1 : K →L[ℂ] K) -
    (coextensionCompress X J).adjoint.comp (coextensionCompress X J) - gram

/-- Real quadratic form of the commutant remainder. -/
theorem re_inner_commutantRemainder (X : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (gram : K →L[ℂ] K)
    (y : K) :
    RCLike.re ⟪commutantRemainder X J gram y, y⟫_ℂ =
      ‖X‖ ^ 2 * ‖y‖ ^ 2 - ‖coextensionCompress X J y‖ ^ 2 -
        RCLike.re ⟪gram y, y⟫_ℂ := by
  have hvec : commutantRemainder X J gram y =
      (Complex.ofReal (‖X‖ ^ 2) • (1 : K →L[ℂ] K)) y -
        ((coextensionCompress X J).adjoint.comp (coextensionCompress X J)) y - gram y := by
    simp [commutantRemainder, sub_apply]
  rw [hvec, inner_sub_left, inner_sub_left, map_sub (RCLike.re (K := ℂ)),
    map_sub (RCLike.re (K := ℂ)), re_inner_smul_one, re_inner_adjoint_comp_self]

/-- The remainder is self-adjoint when the accumulated Gram operator is. -/
theorem isSelfAdjoint_commutantRemainder (X : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K)
    {gram : K →L[ℂ] K} (hgram : IsSelfAdjoint gram) :
    IsSelfAdjoint (commutantRemainder X J gram) := by
  have h1 : IsSelfAdjoint (Complex.ofReal (‖X‖ ^ 2) • (1 : K →L[ℂ] K)) :=
    isSelfAdjoint_smul_one_real (‖X‖ ^ 2)
  have hX : IsSelfAdjoint
      ((coextensionCompress X J).adjoint.comp (coextensionCompress X J)) :=
    isSelfAdjoint_adjoint_comp_self _
  exact (h1.sub hX).sub hgram

/-- A quadratic upper bound makes the remainder positive. -/
theorem commutantRemainder_nonneg (X : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) {gram : K →L[ℂ] K}
    (hgram : IsSelfAdjoint gram)
    (hquad : ∀ y : K, ‖coextensionCompress X J y‖ ^ 2 + RCLike.re ⟪gram y, y⟫_ℂ ≤
      ‖X‖ ^ 2 * ‖y‖ ^ 2) :
    0 ≤ commutantRemainder X J gram := by
  rw [nonneg_iff_isPositive, isPositive_def']
  refine ⟨isSelfAdjoint_commutantRemainder X J hgram, fun y => ?_⟩
  rw [reApplyInnerSelf_apply, re_inner_commutantRemainder]
  linarith [hquad y]

/-- Square root of the commutant remainder. -/
def remainderSqrt (X : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (gram : K →L[ℂ] K) : K →L[ℂ] K :=
  CFC.sqrt (commutantRemainder X J gram)

/-- Squared norm of the remainder square root. -/
theorem norm_sq_remainderSqrt (X : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (gram : K →L[ℂ] K)
    (hR : 0 ≤ commutantRemainder X J gram) (y : K) :
    ‖remainderSqrt X J gram y‖ ^ 2 =
      RCLike.re ⟪commutantRemainder X J gram y, y⟫_ℂ := by
  have hmul : remainderSqrt X J gram * remainderSqrt X J gram =
      commutantRemainder X J gram :=
    CFC.sqrt_mul_sqrt_self _ hR
  have hadj : (remainderSqrt X J gram).adjoint = remainderSqrt X J gram := by
    rw [← star_eq_adjoint]
    exact (CFC.sqrt_nonneg _).star_eq
  rw [apply_norm_sq_eq_inner_adjoint_left, hadj, ← mul_def, hmul]

/-- The closed defect space is complete. -/
instance completeSpace_dilationDefectSpace (T : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K)
    (V : K →ₗᵢ[ℂ] K) : CompleteSpace (dilationDefectSpace T J V) :=
  Submodule.topologicalClosure.completeSpace
    (LinearMap.range (dilationDefect T J V).toLinearMap)

/-- State of the commutant-lifting block iteration. -/
structure CommutantLiftState (T X : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K) where
  /-- Sum of `Bₖ* Bₖ` for the blocks already constructed. -/
  gram : K →L[ℂ] K
  /-- The block that the next one must reproduce after composition with `V`. -/
  prev : K →L[ℂ] dilationDefectSpace T J V
  /-- The accumulated Gram operator is positive. -/
  gram_nonneg : 0 ≤ gram
  /-- Quadratic bound controlling the series. -/
  quad : ∀ y : K, ‖coextensionCompress X J y‖ ^ 2 + RCLike.re ⟪gram y, y⟫_ℂ ≤
    ‖X‖ ^ 2 * ‖y‖ ^ 2
  /-- Shift identity consumed by the next block. -/
  shift : ∀ y : K,
    ‖coextensionCompress X J (V y)‖ ^ 2 + RCLike.re ⟪gram (V y), V y⟫_ℂ =
      ‖coextensionCompress X J y‖ ^ 2 + RCLike.re ⟪gram y, y⟫_ℂ - ‖prev y‖ ^ 2

/-- The previous block is dominated by the remainder square root along `V`. -/
theorem commutantPrev_norm_le (T X : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (s : CommutantLiftState T X J V) (y : K) :
    ‖s.prev y‖ ≤ ‖(remainderSqrt X J s.gram).comp V.toContinuousLinearMap y‖ := by
  have hR : 0 ≤ commutantRemainder X J s.gram :=
    commutantRemainder_nonneg X J s.gram_nonneg.isSelfAdjoint s.quad
  have hsqrt := norm_sq_remainderSqrt X J s.gram hR
  have hform := re_inner_commutantRemainder X J s.gram
  have hshift := s.shift y
  have hVnorm : ‖V y‖ = ‖y‖ := V.norm_map y
  have hsq : ‖s.prev y‖ ^ 2 ≤
      ‖remainderSqrt X J s.gram (V y)‖ ^ 2 := by
    rw [hsqrt (V y), hform (V y), hVnorm]
    have hprev : ‖s.prev y‖ ^ 2 =
        ‖coextensionCompress X J y‖ ^ 2 + RCLike.re ⟪s.gram y, y⟫_ℂ -
          ‖coextensionCompress X J (V y)‖ ^ 2 -
          RCLike.re ⟪s.gram (V y), V y⟫_ℂ := by
      linarith
    linarith [hprev, s.quad y]
  have hle := (sq_le_sq).mp (by
    simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] using hsq)
  simpa [comp_apply] using hle

/-- The next commutant block, as a map into the defect space. -/
def commutantBlock (T X : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (s : CommutantLiftState T X J V) : K →L[ℂ] dilationDefectSpace T J V :=
  (contractionFactor (dilationDefectSpace T J V)
      ((remainderSqrt X J s.gram).comp V.toContinuousLinearMap) s.prev
      (commutantPrev_norm_le T X J V s)).comp
    (remainderSqrt X J s.gram)

/-- Each block reproduces the previous block on the range of `V`. -/
theorem commutantBlock_comp (T X : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (s : CommutantLiftState T X J V) :
    (commutantBlock T X J V s).comp V.toContinuousLinearMap = s.prev := by
  rw [commutantBlock, comp_assoc]
  exact contractionFactor_comp (dilationDefectSpace T J V)
    ((remainderSqrt X J s.gram).comp V.toContinuousLinearMap) s.prev
    (commutantPrev_norm_le T X J V s)

/-- A block is pointwise bounded by the remainder square root. -/
theorem norm_commutantBlock_le_sqrt (T X : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (s : CommutantLiftState T X J V) (y : K) :
    ‖commutantBlock T X J V s y‖ ≤ ‖remainderSqrt X J s.gram y‖ := by
  have hC : ‖contractionFactor (dilationDefectSpace T J V)
      ((remainderSqrt X J s.gram).comp V.toContinuousLinearMap) s.prev
      (commutantPrev_norm_le T X J V s)‖ ≤ 1 :=
    contractionFactor_norm_le _ _ _ _
  rw [commutantBlock, comp_apply]
  calc
    ‖contractionFactor (dilationDefectSpace T J V)
        ((remainderSqrt X J s.gram).comp V.toContinuousLinearMap) s.prev
        (commutantPrev_norm_le T X J V s) (remainderSqrt X J s.gram y)‖ ≤
      ‖contractionFactor (dilationDefectSpace T J V)
        ((remainderSqrt X J s.gram).comp V.toContinuousLinearMap) s.prev
        (commutantPrev_norm_le T X J V s)‖ * ‖remainderSqrt X J s.gram y‖ :=
      le_opNorm _ _
    _ ≤ 1 * ‖remainderSqrt X J s.gram y‖ :=
      mul_le_mul_of_nonneg_right hC (norm_nonneg _)
    _ = ‖remainderSqrt X J s.gram y‖ := one_mul _

/-- Inclusion of a block into `K` has the same pointwise norm. -/
theorem norm_subtype_commutantBlock (T X : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (s : CommutantLiftState T X J V) (y : K) :
    ‖((dilationDefectSpace T J V).subtypeL.comp (commutantBlock T X J V s)) y‖ =
      ‖commutantBlock T X J V s y‖ := by
  rw [comp_apply, Submodule.subtypeL_apply, Submodule.norm_coe]

/-- The Gram operator obtained by appending one block. -/
def commutantSuccGram (T X : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (s : CommutantLiftState T X J V) : K →L[ℂ] K :=
  s.gram + star ((dilationDefectSpace T J V).subtypeL.comp (commutantBlock T X J V s)) *
    ((dilationDefectSpace T J V).subtypeL.comp (commutantBlock T X J V s))

/-- Real quadratic form after appending one block. -/
theorem re_inner_succGram (T X : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (s : CommutantLiftState T X J V) (y : K) :
    RCLike.re ⟪commutantSuccGram T X J V s y, y⟫_ℂ =
      RCLike.re ⟪s.gram y, y⟫_ℂ + ‖commutantBlock T X J V s y‖ ^ 2 := by
  rw [commutantSuccGram, add_apply, inner_add_left, map_add (RCLike.re (K := ℂ)),
    star_eq_adjoint, mul_def, re_inner_adjoint_comp_self, norm_subtype_commutantBlock]

/-- Appending a block preserves the quadratic bound and the shift identity. -/
def commutantLiftSucc (T X : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (s : CommutantLiftState T X J V) : CommutantLiftState T X J V where
  gram := commutantSuccGram T X J V s
  prev := commutantBlock T X J V s
  gram_nonneg := add_nonneg s.gram_nonneg (star_mul_self_nonneg _)
  quad := by
    intro y
    have hR : 0 ≤ commutantRemainder X J s.gram :=
      commutantRemainder_nonneg X J s.gram_nonneg.isSelfAdjoint s.quad
    have hsqrt := norm_sq_remainderSqrt X J s.gram hR y
    have hform := re_inner_commutantRemainder X J s.gram y
    have hblock : ‖commutantBlock T X J V s y‖ ^ 2 ≤
        ‖remainderSqrt X J s.gram y‖ ^ 2 := by
      have hmul := mul_self_le_mul_self (norm_nonneg _)
        (norm_commutantBlock_le_sqrt T X J V s y)
      simpa [pow_two] using hmul
    rw [re_inner_succGram]
    linarith [hsqrt, hform, hblock]
  shift := by
    intro y
    rw [re_inner_succGram, re_inner_succGram]
    have hcomp := congrArg (fun A : K →L[ℂ] dilationDefectSpace T J V => A y)
      (commutantBlock_comp T X J V s)
    have hprev : ‖commutantBlock T X J V s (V y)‖ = ‖s.prev y‖ := by
      simpa [comp_apply] using congrArg norm hcomp
    rw [hprev]
    linarith [s.shift y]

/-- The defect of the compression, viewed in the defect space. -/
def commutantBasePrev (T X : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K) :
    K →L[ℂ] dilationDefectSpace T J V :=
  ((dilationDefect T J V).comp (coextensionCompress X J)).codRestrict
    (dilationDefectSpace T J V) fun y => by
      rw [comp_apply]
      exact dilationDefect_mem_space T J V (coextensionCompress X J y)

/-- Inclusion of the base block recovers the defect of the compression. -/
theorem subtype_commutantBasePrev (T X : H →L[ℂ] H) (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (y : K) :
    ((commutantBasePrev T X J V y : dilationDefectSpace T J V) : K) =
      dilationDefect T J V (coextensionCompress X J y) := by
  rw [commutantBasePrev, coe_codRestrict_apply, comp_apply]

/-- Initial state, with Gram zero and previous block the defect of `X₀`. -/
def commutantLiftBase (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) : CommutantLiftState T X J V where
  gram := 0
  prev := commutantBasePrev T X J V
  gram_nonneg := le_rfl
  quad := by
    intro y
    have hzero : RCLike.re ⟪(0 : K →L[ℂ] K) y, y⟫_ℂ = 0 := by simp
    rw [hzero, add_zero]
    exact coextensionCompress_apply_norm_sq_le X J y
  shift := by
    intro y
    have _hT := contraction_norm_apply_le T hT (coextensionCompress X J y)
    have hzero : ∀ z : K, RCLike.re ⟪(0 : K →L[ℂ] K) z, z⟫_ℂ = 0 := by
      intro z
      simp
    rw [hzero, hzero, add_zero, add_zero]
    have hD := norm_sq_dilationDefect T J V hcoin (coextensionCompress X J y)
    rw [coextensionCompress_apply_V T X hXT J V hcoin y] at hD
    have hnorm : ‖commutantBasePrev T X J V y‖ ^ 2 =
        ‖dilationDefect T J V (coextensionCompress X J y)‖ ^ 2 := by
      apply congrArg (fun t : ℝ => t ^ 2)
      rw [← Submodule.norm_coe, subtype_commutantBasePrev]
    rw [hnorm, hD]
    ring

/-- The block iteration. -/
def commutantLiftState (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) : ℕ → CommutantLiftState T X J V
  | 0 => commutantLiftBase T X hT hXT J V hcoin
  | n + 1 => commutantLiftSucc T X J V (commutantLiftState T X hT hXT J V hcoin n)

/-- The block attached to the `n`th state. -/
def commutantLiftBlock (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (n : ℕ) : K →L[ℂ] dilationDefectSpace T J V :=
  commutantBlock T X J V (commutantLiftState T X hT hXT J V hcoin n)

/-- Successive blocks satisfy `Bₙ₊₁ V = Bₙ`. -/
theorem commutantLiftBlock_succ_comp (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (n : ℕ) :
    (commutantLiftBlock T X hT hXT J V hcoin (n + 1)).comp V.toContinuousLinearMap =
      commutantLiftBlock T X hT hXT J V hcoin n := by
  simpa [commutantLiftBlock, commutantLiftState, commutantLiftSucc] using
    commutantBlock_comp T X J V
      (commutantLiftSucc T X J V (commutantLiftState T X hT hXT J V hcoin n))

/-- The first block reproduces the defect of the compression. -/
theorem commutantLiftBlock_zero_comp (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) :
    ((dilationDefectSpace T J V).subtypeL.comp
        (commutantLiftBlock T X hT hXT J V hcoin 0)).comp V.toContinuousLinearMap =
      (dilationDefect T J V).comp (coextensionCompress X J) := by
  ext y
  have hcomp := congrArg (fun A : K →L[ℂ] dilationDefectSpace T J V => A y)
    (commutantBlock_comp T X J V (commutantLiftBase T X hT hXT J V hcoin))
  simp only [commutantLiftBlock, commutantLiftState, comp_apply,
    Submodule.subtypeL_apply] at hcomp ⊢
  rw [hcomp, commutantLiftBase, subtype_commutantBasePrev]

/-- Real quadratic form of the accumulated Gram operator. -/
theorem re_inner_liftGram (T X : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (hXT : Commute X T)
    (J : H →ₗᵢ[ℂ] K) (V : K →ₗᵢ[ℂ] K)
    (hcoin : ∀ y : K, J.toContinuousLinearMap.adjoint (V y) =
      T (J.toContinuousLinearMap.adjoint y)) (n : ℕ) (y : K) :
    RCLike.re ⟪(commutantLiftState T X hT hXT J V hcoin n).gram y, y⟫_ℂ =
      ∑ k ∈ Finset.range n, ‖commutantLiftBlock T X hT hXT J V hcoin k y‖ ^ 2 := by
  induction n with
  | zero => simp [commutantLiftState, commutantLiftBase]
  | succ n ih =>
    rw [commutantLiftState, commutantLiftSucc, re_inner_succGram, Finset.sum_range_succ, ih,
      commutantLiftBlock]

end CKMA
