/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Operator.Dilation.Defect
public import CKMA.Analysis.Operator.Dilation.L2Shift
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# Schäffer's isometric coextension

On `H ⊕ ℓ²(ℕ, H)`, the operator sending `(h, f)` to `(T h, D_T h ⊕ S f)` is an isometry when
`T` is a contraction, and the copy of `H` is co-invariant. Minimality is obtained afterwards by
restricting to the closed forward orbit of that copy.
-/

@[expose] public section

noncomputable section

namespace CKMA

open scoped InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The carrier `H ⊕ ℓ²(ℕ, H)` of Schäffer's dilation. -/
abbrev SchafferSpace (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  WithLp 2 (H × lp (fun _ : ℕ => H) 2)

/-- The linear pair `(h, f) ↦ (T h, D_T h + S f)` underlying Schäffer's isometry. -/
def schafferPair (T : H →L[ℂ] H) :
    H × lp (fun _ : ℕ => H) 2 →ₗ[ℂ] H × lp (fun _ : ℕ => H) 2 where
  toFun p := (T p.1, l2InsertZero (defectOperator T p.1) + l2ShiftRight p.2)
  map_add' p q := by
    apply Prod.ext
    · simp
    · simp [map_add]
      abel_nf
  map_smul' c p := by
    apply Prod.ext
    · simp
    · simp [map_smul, smul_add]

/-- Evaluation of the Schäffer pair. -/
theorem schafferPair_apply (T : H →L[ℂ] H) (h : H) (f : lp (fun _ : ℕ => H) 2) :
    schafferPair T (h, f) =
      (T h, l2InsertZero (defectOperator T h) + l2ShiftRight f) :=
  rfl

/-- Schäffer's operator on `H ⊕ ℓ²(ℕ, H)`. -/
def schafferLinear (T : H →L[ℂ] H) : SchafferSpace H →ₗ[ℂ] SchafferSpace H :=
  (WithLp.linearEquiv 2 ℂ (H × lp (fun _ : ℕ => H) 2)).symm.toLinearMap ∘ₗ
    schafferPair T ∘ₗ
    (WithLp.linearEquiv 2 ℂ (H × lp (fun _ : ℕ => H) 2)).toLinearMap

/-- Evaluation of Schäffer's operator. -/
theorem schafferLinear_apply (T : H →L[ℂ] H) (z : SchafferSpace H) :
    schafferLinear T z = WithLp.toLp 2
      (T z.fst, l2InsertZero (defectOperator T z.fst) + l2ShiftRight z.snd) := by
  simp [schafferLinear, schafferPair, WithLp.linearEquiv_apply,
    WithLp.linearEquiv_symm_apply, WithLp.ofLp_fst, WithLp.ofLp_snd]

/-- Schäffer's operator is an isometry when `T` is a contraction. -/
theorem norm_schafferLinear (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (z : SchafferSpace H) :
    ‖schafferLinear T z‖ = ‖z‖ := by
  have hfst : (schafferLinear T z).fst = T z.fst := by
    rw [schafferLinear_apply]
    rfl
  have hsnd : (schafferLinear T z).snd =
      l2InsertZero (defectOperator T z.fst) + l2ShiftRight z.snd := by
    rw [schafferLinear_apply]
    rfl
  rw [← (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _))]
  rw [WithLp.prod_norm_sq_eq_of_L2 (schafferLinear T z), hfst, hsnd, norm_sq_l2Cons,
    ← add_assoc, norm_sq_add_norm_sq_defectOperator T hT, ← WithLp.prod_norm_sq_eq_of_L2 z]

/-- Schäffer's isometric coextension of a contraction. -/
def schafferIsometry (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    SchafferSpace H →ₗᵢ[ℂ] SchafferSpace H where
  toLinearMap := schafferLinear T
  norm_map' := norm_schafferLinear T hT

/-- Evaluation of the isometric coextension. -/
theorem schafferIsometry_apply (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (z : SchafferSpace H) :
    schafferIsometry T hT z = schafferLinear T z :=
  rfl

/-- The linear embedding of the original space as the first summand. -/
def schafferEmbedLinear : H →ₗ[ℂ] SchafferSpace H :=
  (WithLp.linearEquiv 2 ℂ (H × lp (fun _ : ℕ => H) 2)).symm.toLinearMap ∘ₗ
    LinearMap.inl ℂ H (lp (fun _ : ℕ => H) 2)

omit [CompleteSpace H] in
/-- The embedding sends `x` to `(x, 0)`. -/
theorem schafferEmbedLinear_apply (x : H) :
    schafferEmbedLinear x = WithLp.toLp 2 (x, 0) := by
  simp [schafferEmbedLinear, WithLp.linearEquiv_symm_apply]

omit [CompleteSpace H] in
/-- The embedding of the original space is isometric. -/
theorem norm_schafferEmbedLinear (x : H) : ‖schafferEmbedLinear x‖ = ‖x‖ := by
  rw [schafferEmbedLinear_apply]
  exact WithLp.norm_toLp_fst 2 H (lp (fun _ : ℕ => H) 2) x

/-- The isometric embedding of the original Hilbert space. -/
def schafferEmbed : H →ₗᵢ[ℂ] SchafferSpace H where
  toLinearMap := schafferEmbedLinear
  norm_map' := norm_schafferEmbedLinear

omit [CompleteSpace H] in
/-- Evaluation of the isometric embedding. -/
theorem schafferEmbed_apply (x : H) : schafferEmbed x = schafferEmbedLinear x :=
  rfl

/-- The adjoint of the embedding is projection onto the first summand. -/
theorem schafferEmbed_adjoint_apply (z : SchafferSpace H) :
    schafferEmbed.toContinuousLinearMap.adjoint z = z.fst := by
  refine ext_inner_right ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap]
  rw [schafferEmbed_apply, schafferEmbedLinear_apply, WithLp.prod_inner_apply]
  simp [WithLp.ofLp_fst, inner_zero_right]

/-- The embedded copy of `H` is co-invariant under Schäffer's isometry. -/
theorem schaffer_coinvariant (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (z : SchafferSpace H) :
    schafferEmbed.toContinuousLinearMap.adjoint ((schafferIsometry T hT) z) =
      T (schafferEmbed.toContinuousLinearMap.adjoint z) := by
  rw [schafferEmbed_adjoint_apply, schafferEmbed_adjoint_apply, schafferIsometry_apply,
    schafferLinear_apply]
  simp [WithLp.toLp_fst]

end CKMA
