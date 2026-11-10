/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Arbitrary-index Hilbert frames and canonical duals

Coefficient energies are nonnegative extended sums over arbitrary index types. Finite upper
bounds give bounded analysis into l2; a positive lower bound characterizes invertibility of the
frame operator and surjectivity of synthesis. No countability or nonzero-space assumption is
built into the definitions.

Inner products are linear in the second variable. `frameOperatorOfAnalysis` is the bounded
operator `C^* ∘ C` for an arbitrary index. TauCeti's `frameOperator` is the finite-sum operator
of a finite family. The canonical dual has reversed reciprocal bounds, and both reconstruction
formulas are unconditional sums. Sources: GAPS 29.2 and 29.3.
The analysis construction uses Mathlib's `Memℓp` and
`lp.norm_le_of_tsum_le`; the operator criteria use Mathlib's
`ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map` and Banach open mapping theorem.
Unconditional synthesis and reconstruction use Mathlib's `lp.hasSum_single` and continuity of
bounded linear maps.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped BigOperators InnerProductSpace ENNReal

variable {𝕜 H ι : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The nonnegative coefficient energy, allowing infinite sums over arbitrary index types. -/
def frameEnergy (f : ι → H) (x : H) : ℝ≥0∞ := ∑' i, ENNReal.ofReal (‖⟪f i, x⟫_𝕜‖ ^ 2)

/-- The Bessel upper bound. -/
def IsBesselSequence (f : ι → H) (B : ℝ) : Prop :=
  0 ≤ B ∧ ∀ x, frameEnergy (𝕜 := 𝕜) f x ≤ ENNReal.ofReal (B * ‖x‖ ^ 2)

/-- A Hilbert frame with explicit positive lower and finite upper bounds. -/
def IsFrameWithBounds (f : ι → H) (A B : ℝ) : Prop :=
  0 < A ∧ A ≤ B ∧ ∀ x, ENNReal.ofReal (A * ‖x‖ ^ 2) ≤ frameEnergy (𝕜 := 𝕜) f x ∧
    frameEnergy (𝕜 := 𝕜) f x ≤ ENNReal.ofReal (B * ‖x‖ ^ 2)

/-- A frame admits some positive lower and finite upper bound. -/
def IsFrame (f : ι → H) : Prop := ∃ A B, IsFrameWithBounds (𝕜 := 𝕜) f A B

/-- A bounded operator is the analysis operator of `f` when its coordinates are the inner products.
  -/
def IsFrameAnalysis (f : ι → H) (C : H →L[𝕜] lp (fun _ : ι ↦ 𝕜) 2) : Prop :=
  ∀ x i, C x i = ⟪f i, x⟫_𝕜

omit [CompleteSpace H] in
/-- The energy of a family with bounded analysis equals the squared analysis norm. -/
theorem IsFrameAnalysis.frameEnergy_eq {f : ι → H}
    {C : H →L[𝕜] lp (fun _ : ι ↦ 𝕜) 2} (hC : IsFrameAnalysis f C) (x : H) :
    frameEnergy (𝕜 := 𝕜) f x = ENNReal.ofReal (‖C x‖ ^ 2) := by
  have hs : Summable (fun i ↦ ‖C x i‖ ^ 2) := by
    simpa using (lp.memℓp (C x)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hn : ‖C x‖ ^ 2 = ∑' i, ‖C x i‖ ^ 2 := by
    simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (C x)
  rw [hn, ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ sq_nonneg _) hs]
  simp only [frameEnergy, hC x]

omit [CompleteSpace H] in
/-- A bounded analysis operator defines a frame exactly when it is bounded below. -/
theorem IsFrameAnalysis.isFrame_iff_exists_lower_bound {f : ι → H}
    {C : H →L[𝕜] lp (fun _ : ι ↦ 𝕜) 2} (hC : IsFrameAnalysis f C) :
    IsFrame (𝕜 := 𝕜) f ↔ ∃ c > 0, ∀ x, c * ‖x‖ ≤ ‖C x‖ := by
  constructor
  · rintro ⟨A, B, hA, hAB, hf⟩
    refine ⟨Real.sqrt A, Real.sqrt_pos.2 hA, fun x ↦ ?_⟩
    have he : A * ‖x‖ ^ 2 ≤ ‖C x‖ ^ 2 := by
      exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp
        (hC.frameEnergy_eq x ▸ (hf x).1)
    have hs := Real.sq_sqrt hA.le
    nlinarith [norm_nonneg (C x), Real.sqrt_nonneg A, norm_nonneg x]
  · rintro ⟨c, hc, hlow⟩
    refine ⟨c ^ 2, max (c ^ 2) (‖C‖ ^ 2), sq_pos_of_pos hc, le_max_left _ _, fun x ↦ ?_⟩
    rw [hC.frameEnergy_eq]
    constructor
    · apply ENNReal.ofReal_le_ofReal
      have h := hlow x
      simpa only [mul_pow] using
        pow_le_pow_left₀ (mul_nonneg hc.le (norm_nonneg x)) h 2
    · apply ENNReal.ofReal_le_ofReal
      calc
        ‖C x‖ ^ 2 ≤ (‖C‖ * ‖x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (C.le_opNorm x) 2
        _ = ‖C‖ ^ 2 * ‖x‖ ^ 2 := mul_pow _ _ _
        _ ≤ max (c ^ 2) (‖C‖ ^ 2) * ‖x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)

omit [CompleteSpace H] in
/-- A Bessel family has a bounded analysis operator. -/
theorem IsBesselSequence.exists_analysis {f : ι → H} {B : ℝ} (hf : IsBesselSequence (𝕜 := 𝕜) f B) :
    ∃ C : H →L[𝕜] lp (fun _ : ι ↦ 𝕜) 2, IsFrameAnalysis f C := by
  have hmem (x : H) : Memℓp (fun i ↦ ⟪f i, x⟫_𝕜) 2 := by
    apply memℓp_gen
    have hfinite : frameEnergy (𝕜 := 𝕜) f x ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hf.2 x)
    simpa only [frameEnergy, ENNReal.toReal_ofReal (sq_nonneg _),
      ENNReal.toReal_ofNat, Real.rpow_two] using ENNReal.summable_toReal hfinite
  let L : H →ₗ[𝕜] lp (fun _ : ι ↦ 𝕜) 2 :=
    { toFun := fun x ↦ ⟨fun i ↦ ⟪f i, x⟫_𝕜, hmem x⟩
      map_add' := fun x y ↦ by ext i; exact inner_add_right _ _ _
      map_smul' := fun c x ↦ by ext i; exact inner_smul_right _ _ _ }
  have hbound (x : H) : ‖L x‖ ≤ Real.sqrt B * ‖x‖ := by
    apply lp.norm_le_of_tsum_le (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (by positivity)
    have heq : ENNReal.ofReal (∑' i, ‖L x i‖ ^ 2) = frameEnergy (𝕜 := 𝕜) f x := by
      exact ENNReal.ofReal_tsum_of_nonneg (fun i ↦ sq_nonneg _) (by
        simpa [L, ENNReal.toReal_ofNat, Real.rpow_two] using (hmem x).summable (by norm_num))
    have hle : ∑' i, ‖L x i‖ ^ 2 ≤ B * ‖x‖ ^ 2 :=
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hf.1 (sq_nonneg _))).mp (heq ▸ hf.2 x)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, mul_pow, Real.sq_sqrt hf.1] using hle
  exact ⟨L.mkContinuous (Real.sqrt B) hbound, fun _ _ ↦ rfl⟩

/-- The frame operator is analysis followed by synthesis. -/
def frameOperatorOfAnalysis (C : H →L[𝕜] lp (fun _ : ι ↦ 𝕜) 2) : H →L[𝕜] H := C.adjoint.comp C

/-- Applying an invertible representative of the frame operator is synthesis of the analysis. -/
theorem frameOperatorOfAnalysis_apply
    {C : H →L[𝕜] lp (fun _ : ι ↦ 𝕜) 2}
    (S : H ≃L[𝕜] H) (hS : S.toContinuousLinearMap = frameOperatorOfAnalysis C) (x : H) :
    S x = C.adjoint (C x) :=
  congrArg (fun T : H →L[𝕜] H ↦ T x) hS

/-- Analysis followed by synthesis inverts the inverse frame operator. -/
theorem frameOperatorOfAnalysis_adjoint_symm_apply
    {C : H →L[𝕜] lp (fun _ : ι ↦ 𝕜) 2}
    (S : H ≃L[𝕜] H) (hS : S.toContinuousLinearMap = frameOperatorOfAnalysis C) (x : H) :
    C.adjoint (C (S.symm x)) = x := by
  rw [← frameOperatorOfAnalysis_apply S hS (S.symm x), S.apply_symm_apply]

/-- Surjectivity of synthesis gives a lower frame bound by the open mapping theorem. -/
theorem IsFrameAnalysis.isFrame_of_surjective_adjoint {f : ι → H}
    {C : H →L[𝕜] lp (fun _ : ι ↦ 𝕜) 2} (hC : IsFrameAnalysis f C)
    (hsurj : Function.Surjective C.adjoint) : IsFrame (𝕜 := 𝕜) f := by
  obtain ⟨K, hK, hpre⟩ := C.adjoint.exists_preimage_norm_le hsurj
  apply hC.isFrame_iff_exists_lower_bound.2
  refine ⟨K⁻¹, inv_pos.2 hK, fun x ↦ ?_⟩
  obtain ⟨y, hy, hnorm⟩ := hpre x
  have hinner : ‖x‖ ^ 2 ≤ K * ‖x‖ * ‖C x‖ := calc
    ‖x‖ ^ 2 = ‖⟪x, x⟫_𝕜‖ := by simp [inner_self_eq_norm_sq_to_K]
    _ = ‖⟪y, C x⟫_𝕜‖ := by rw [← C.adjoint_inner_left, hy]
    _ ≤ ‖y‖ * ‖C x‖ := norm_inner_le_norm _ _
    _ ≤ (K * ‖x‖) * ‖C x‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
  by_cases hx : x = 0
  · simp [hx]
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hcancel : ‖x‖ ≤ K * ‖C x‖ := by nlinarith
    exact (inv_mul_le_iff₀ hK).2 hcancel

/-- **29.2**: a Bessel family is a frame precisely when its frame operator is boundedly invertible.
  -/
theorem isFrame_iff_frameOperatorOfAnalysis_invertible (f : ι → H)
    (C : H →L[𝕜] lp (fun _ : ι ↦ 𝕜) 2) (hC : IsFrameAnalysis f C) :
    IsFrame (𝕜 := 𝕜) f ↔ ∃ S : H ≃L[𝕜] H, S.toContinuousLinearMap = frameOperatorOfAnalysis C := by
  constructor
  · intro hf
    obtain ⟨c, hc, hlow⟩ := hC.isFrame_iff_exists_lower_bound.1 hf
    have hunit : IsUnit (frameOperatorOfAnalysis C) := by
      apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map (frameOperatorOfAnalysis C)
        (c := ⟨c ^ 2, sq_nonneg c⟩) (by exact_mod_cast sq_pos_of_pos hc)
      intro x
      change ‖x‖ ^ 2 * c ^ 2 ≤ ‖⟪C.adjoint (C x), x⟫_𝕜‖
      rw [C.adjoint_inner_left]
      simp only [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm]
      simpa only [mul_pow, mul_comm] using
        pow_le_pow_left₀ (mul_nonneg hc.le (norm_nonneg x)) (hlow x) 2
    obtain ⟨hinj, hsurj⟩ := ContinuousLinearMap.isUnit_iff_bijective.1 hunit
    exact ⟨ContinuousLinearEquiv.ofBijective (frameOperatorOfAnalysis C)
      (LinearMap.ker_eq_bot.2 hinj) (LinearMap.range_eq_top.2 hsurj), rfl⟩
  · rintro ⟨S, hS⟩
    apply hC.isFrame_of_surjective_adjoint
    intro x
    refine ⟨C (S.symm x), frameOperatorOfAnalysis_adjoint_symm_apply S hS x⟩

/-- The equivalent synthesis-surjectivity criterion. -/
theorem isFrame_iff_surjective_adjoint (f : ι → H)
    (C : H →L[𝕜] lp (fun _ : ι ↦ 𝕜) 2) (hC : IsFrameAnalysis f C) :
    IsFrame (𝕜 := 𝕜) f ↔ Function.Surjective C.adjoint := by
  constructor
  · intro hf
    obtain ⟨S, hS⟩ := (isFrame_iff_frameOperatorOfAnalysis_invertible f C hC).1 hf
    intro x
    refine ⟨C (S.symm x), frameOperatorOfAnalysis_adjoint_symm_apply S hS x⟩
  · exact hC.isFrame_of_surjective_adjoint

/-- The adjoint of analysis sends a single coefficient to the corresponding frame vector. -/
theorem IsFrameAnalysis.adjoint_single [DecidableEq ι] {f : ι → H}
    {C : H →L[𝕜] lp (fun _ : ι ↦ 𝕜) 2} (hC : IsFrameAnalysis f C)
    (i : ι) (c : 𝕜) : C.adjoint (lp.single 2 i c) = c • f i := by
  classical
  apply ext_inner_right 𝕜
  intro x
  rw [C.adjoint_inner_left, lp.inner_single_left, hC x i]
  simp [inner_smul_left, mul_comm]

/-- Synthesis is the unconditional sum of the coefficient multiples. -/
theorem IsFrameAnalysis.hasSum_synthesis {f : ι → H}
    {C : H →L[𝕜] lp (fun _ : ι ↦ 𝕜) 2} (hC : IsFrameAnalysis f C)
    (a : lp (fun _ : ι ↦ 𝕜) 2) : HasSum (fun i ↦ a i • f i) (C.adjoint a) := by
  classical
  simpa only [hC.adjoint_single] using
    C.adjoint.hasSum (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) a)

omit [CompleteSpace H] in
/-- A Bessel bound controls the norm of its bounded analysis operator. -/
theorem IsFrameAnalysis.norm_le_sqrt {f : ι → H}
    {C : H →L[𝕜] lp (fun _ : ι ↦ 𝕜) 2} (hC : IsFrameAnalysis f C)
    {B : ℝ} (hf : IsBesselSequence (𝕜 := 𝕜) f B) : ‖C‖ ≤ Real.sqrt B := by
  apply C.opNorm_le_bound (Real.sqrt_nonneg B)
  intro x
  have he : ‖C x‖ ^ 2 ≤ B * ‖x‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hf.1 (sq_nonneg _))).mp
      (hC.frameEnergy_eq x ▸ hf.2 x)
  have hs := Real.sq_sqrt hf.1
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg B) (norm_nonneg x))).1
  simpa only [mul_pow, hs] using he

/-- The canonical dual family for a supplied invertible frame operator. -/
def canonicalDualFrame (f : ι → H) (S : H ≃L[𝕜] H) : ι → H := fun i ↦ S.symm (f i)

/-- The analysis of the canonical dual is analysis composed with the inverse frame operator. -/
theorem IsFrameAnalysis.canonicalDualFrame {f : ι → H}
    {C : H →L[𝕜] lp (fun _ : ι ↦ 𝕜) 2} (hC : IsFrameAnalysis f C)
    (S : H ≃L[𝕜] H) (hS : S.toContinuousLinearMap = frameOperatorOfAnalysis C) :
    IsFrameAnalysis (canonicalDualFrame f S) (C.comp S.symm.toContinuousLinearMap) := by
  have hsym (x y : H) : ⟪S x, y⟫_𝕜 = ⟪x, S y⟫_𝕜 := by
    rw [frameOperatorOfAnalysis_apply S hS, frameOperatorOfAnalysis_apply S hS,
      C.adjoint_inner_left, C.adjoint_inner_right]
  intro x i
  apply (hC (S.symm x) i).trans
  change ⟪f i, S.symm x⟫_𝕜 = ⟪S.symm (f i), x⟫_𝕜
  simpa only [S.apply_symm_apply] using hsym (S.symm (f i)) (S.symm x)

/-- The canonical dual has the reciprocal reversed frame bounds. -/
theorem canonicalDualFrame_isFrameWithBounds (f : ι → H) {A B : ℝ}
    (hf : IsFrameWithBounds (𝕜 := 𝕜) f A B)
    (C : H →L[𝕜] lp (fun _ : ι ↦ 𝕜) 2) (hC : IsFrameAnalysis f C)
    (S : H ≃L[𝕜] H) (hS : S.toContinuousLinearMap = frameOperatorOfAnalysis C) :
    IsFrameWithBounds (𝕜 := 𝕜) (canonicalDualFrame f S) B⁻¹ A⁻¹ := by
  let D := C.comp S.symm.toContinuousLinearMap
  have hD : IsFrameAnalysis (canonicalDualFrame f S) D := hC.canonicalDualFrame S hS
  have henergy (x : H) : ‖D x‖ ^ 2 = RCLike.re ⟪S.symm x, x⟫_𝕜 := by
    change ‖C (S.symm x)‖ ^ 2 = _
    rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), ← C.adjoint_inner_right,
      ← frameOperatorOfAnalysis_apply S hS, S.apply_symm_apply]
  have hBpos : 0 < B := hf.1.trans_le hf.2.1
  have hnormC : ‖C‖ ≤ Real.sqrt B :=
    hC.norm_le_sqrt ⟨hBpos.le, fun x ↦ (hf.2.2 x).2⟩
  refine ⟨inv_pos.2 hBpos, (inv_le_inv₀ hBpos hf.1).2 hf.2.1, fun x ↦ ?_⟩
  rw [hD.frameEnergy_eq]
  constructor
  · apply ENNReal.ofReal_le_ofReal
    have hnorm : ‖x‖ ≤ Real.sqrt B * ‖D x‖ := calc
      ‖x‖ = ‖C.adjoint (C (S.symm x))‖ :=
        (congrArg norm (frameOperatorOfAnalysis_adjoint_symm_apply S hS x)).symm
      _ ≤ ‖C.adjoint‖ * ‖C (S.symm x)‖ := C.adjoint.le_opNorm _
      _ ≤ Real.sqrt B * ‖D x‖ := by
        change ‖C.adjoint‖ * ‖D x‖ ≤ _
        exact mul_le_mul_of_nonneg_right (by simpa using hnormC) (norm_nonneg _)
    have hs := pow_le_pow_left₀ (norm_nonneg x) hnorm 2
    rw [mul_pow, Real.sq_sqrt hBpos.le] at hs
    exact (inv_mul_le_iff₀ hBpos).2 hs
  · apply ENNReal.ofReal_le_ofReal
    have hlow : A * ‖S.symm x‖ ^ 2 ≤ ‖D x‖ ^ 2 := by
      exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp
        (hC.frameEnergy_eq (S.symm x) ▸ (hf.2.2 (S.symm x)).1)
    have hinner : ‖D x‖ ^ 2 ≤ ‖S.symm x‖ * ‖x‖ := by
      rw [henergy]
      exact re_inner_le_norm (𝕜 := 𝕜) _ _
    have hsinv : A * ‖S.symm x‖ ≤ ‖x‖ := by
      by_cases hx : S.symm x = 0
      · simp [hx]
      · have hxpos := norm_pos_iff.mpr hx
        nlinarith
    have hmul := mul_le_mul_of_nonneg_right hsinv (norm_nonneg x)
    have hfin : A * ‖D x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
      (mul_le_mul_of_nonneg_left hinner hf.1.le).trans (by nlinarith)
    exact (le_inv_mul_iff₀ hf.1).2 hfin

/-- **29.3**: the canonical dual has the reciprocal reversed bounds and both unconditional
  expansions. -/
theorem canonicalDualFrame_reconstruction (f : ι → H) {A B : ℝ}
    (hf : IsFrameWithBounds (𝕜 := 𝕜) f A B)
    (C : H →L[𝕜] lp (fun _ : ι ↦ 𝕜) 2) (hC : IsFrameAnalysis f C)
    (S : H ≃L[𝕜] H) (hS : S.toContinuousLinearMap = frameOperatorOfAnalysis C) :
    IsFrameWithBounds (𝕜 := 𝕜) (canonicalDualFrame f S) B⁻¹ A⁻¹ ∧ ∀ x : H,
      HasSum (fun i ↦ ⟪canonicalDualFrame f S i, x⟫_𝕜 • f i) x ∧
      HasSum (fun i ↦ ⟪f i, x⟫_𝕜 • canonicalDualFrame f S i) x := by
  let D := C.comp S.symm.toContinuousLinearMap
  have hD : IsFrameAnalysis (canonicalDualFrame f S) D := hC.canonicalDualFrame S hS
  refine ⟨canonicalDualFrame_isFrameWithBounds f hf C hC S hS, fun x ↦ ⟨?_, ?_⟩⟩
  · have hsum := hC.hasSum_synthesis (D x)
    have hout : C.adjoint (D x) = x := by
      change C.adjoint (C (S.symm x)) = x
      exact frameOperatorOfAnalysis_adjoint_symm_apply S hS x
    simpa only [hD x, hout] using hsum
  · have hsum := S.symm.toContinuousLinearMap.hasSum (hC.hasSum_synthesis (C x))
    have hout : S.symm (C.adjoint (C x)) = x := by
      rw [← frameOperatorOfAnalysis_apply S hS, S.symm_apply_apply]
    simpa only [ContinuousLinearEquiv.coe_coe, map_smul, hC x, hout,
      canonicalDualFrame] using hsum

end CKMA
