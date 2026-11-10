/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Operator.TraceIdeals
public import TauCeti.LinearAlgebra.Eigenspace.Comp
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Birman–Schwinger kernel transport and bounded-generator RAGE

The Birman–Schwinger kernel equivalence is algebraic once the shifted free operator is
invertible; compactness and self-adjointness of the factor are not needed for this equivalence.
A positive self-adjoint free operator and a positive real shift provide the spectral setting.
The proof combines Mathlib's Hilbert coercivity criterion with the Tau Ceti contributors'
`Module.End.eigenspaceCompEquiv` for the algebraic kernel transport.

The bounded unitary evolution has sign `exp(-itA)`. The pure-point space is the closed span of
all real-eigenvalue eigenvectors. RAGE distinguishes its orthogonal complement by compactly
observed time-averaged energy, and the pure-point vectors by relative compactness of their
full unitary orbits. Sources: GAPS 22.38 and 22.63.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology MeasureTheory
open scoped InnerProductSpace

/-- The Birman–Schwinger kernel transport for a supplied invertible bounded operator.
It is algebraic over any nontrivially normed field, without a Hilbert or compactness hypothesis.
The transport uses TauCeti's equivalence of nonzero eigenspaces of two composites. -/
def birmanSchwingerKernelEquiv {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (A W : X →L[𝕜] X) (hA : IsUnit A) :
    LinearMap.ker ((A - W * W).toLinearMap) ≃ₗ[𝕜]
      LinearMap.ker ((1 - W * Ring.inverse A * W).toLinearMap) := by
  let f := W.toLinearMap
  let g := (Ring.inverse A * W).toLinearMap
  have hRA (x : X) : Ring.inverse A (A x) = x := by
    change (Ring.inverse A * A) x = x
    rw [Ring.inverse_mul_cancel A hA]
    rfl
  have hAR (x : X) : A (Ring.inverse A x) = x := by
    change (A * Ring.inverse A) x = x
    rw [Ring.mul_inverse_cancel A hA]
    rfl
  have hleft : LinearMap.ker ((A - W * W).toLinearMap) =
      Module.End.eigenspace (g ∘ₗ f) 1 := by
    ext x
    simp only [LinearMap.mem_ker, Module.End.mem_eigenspace_iff, one_smul]
    change A x - W (W x) = 0 ↔ Ring.inverse A (W (W x)) = x
    constructor
    · intro hx
      rw [← sub_eq_zero.mp hx]
      exact hRA x
    · intro hx
      apply sub_eq_zero.mpr
      calc
        A x = A (Ring.inverse A (W (W x))) := congrArg A hx.symm
        _ = W (W x) := hAR _
  have hright : LinearMap.ker ((1 - W * Ring.inverse A * W).toLinearMap) =
      Module.End.eigenspace (f ∘ₗ g) 1 := by
    ext x
    simp only [LinearMap.mem_ker, Module.End.mem_eigenspace_iff, one_smul]
    change x - W (Ring.inverse A (W x)) = 0 ↔ W (Ring.inverse A (W x)) = x
    exact sub_eq_zero.trans eq_comm
  exact (LinearEquiv.ofEq _ _ hleft).trans
    ((Module.End.eigenspaceCompEquiv f g isUnit_one).trans
      (LinearEquiv.ofEq _ _ hright.symm))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Birman–Schwinger operator for a supplied positive square root `W²=V`.
Totalized ring inversion is used in the definition; the theorem's hypotheses force invertibility. -/
def birmanSchwingerOperator (H₀ W : H →L[ℂ] H) (E : ℝ) : H →L[ℂ] H :=
  W * Ring.inverse (H₀ + (E : ℂ) • (1 : H →L[ℂ] H)) * W

/-- **22.38**, the bounded-operator eigenvalue/multiplicity clause. The conclusion is an
actual linear equivalence of eigenspaces, stronger than equality of finite dimensions.
Compactness and self-adjointness of the factor `W` are unnecessary for this algebraic clause. -/
theorem birman_schwinger_kernel_equiv (H₀ V W : H →L[ℂ] H)
    (hH : IsSelfAdjoint H₀) (hpos : ∀ x : H, 0 ≤ (⟪x, H₀ x⟫_ℂ).re)
    (hV : W * W = V) {E : ℝ} (hE : 0 < E) :
    Nonempty (LinearMap.ker ((H₀ - V + (E : ℂ) • (1 : H →L[ℂ] H)).toLinearMap) ≃ₗ[ℂ]
      LinearMap.ker ((1 - birmanSchwingerOperator H₀ W E).toLinearMap)) := by
  have hunit : IsUnit (H₀ + (E : ℂ) • (1 : H →L[ℂ] H)) := by
    apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map _
      (c := ⟨E, hE.le⟩) hE
    intro x
    calc
      ‖x‖ ^ 2 * E ≤ (⟪(H₀ + (E : ℂ) • (1 : H →L[ℂ] H)) x, x⟫_ℂ).re := by
        have hadj : H₀.adjoint = H₀ := hH
        have hs : ⟪H₀ x, x⟫_ℂ = ⟪x, H₀ x⟫_ℂ := by
          simpa only [hadj] using H₀.adjoint_inner_left x x
        simp only [add_apply, smul_apply, one_apply_eq_self, inner_add_left, inner_smul_left,
          Complex.conj_ofReal, hs, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero]
        have hn : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
        rw [hn]
        nlinarith [hpos x]
      _ ≤ ‖⟪(H₀ + (E : ℂ) • (1 : H →L[ℂ] H)) x, x⟫_ℂ‖ := Complex.re_le_norm _
  have heq : H₀ - V + (E : ℂ) • (1 : H →L[ℂ] H) =
      H₀ + (E : ℂ) • (1 : H →L[ℂ] H) - W * W := by
    rw [hV]
    abel
  rw [heq]
  exact ⟨birmanSchwingerKernelEquiv (H₀ + (E : ℂ) • (1 : H →L[ℂ] H)) W hunit⟩

/-- The unitary evolution generated by a bounded self-adjoint operator, with the `exp(-itA)` sign.
  -/
def boundedSpectralEvolution (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  NormedSpace.exp ((-(t : ℂ) * Complex.I) • A)

/-- The closed subspace spanned by the real eigenvectors of `A`. -/
def purePointOperatorSubspace (A : H →L[ℂ] H) : Submodule ℂ H :=
  (Submodule.span ℂ {x : H | ∃ a : ℝ, A x = (a : ℂ) • x}).topologicalClosure

/-- **22.63**, RAGE for a bounded self-adjoint generator: continuous vectors are exactly
those whose compactly observed time-averaged energy escapes. -/
theorem rage_continuous (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x : H) :
    x ∈ (purePointOperatorSubspace A).orthogonal ↔
      ∀ C : H →L[ℂ] H, IsCompactOperator C → Tendsto
        (fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T, ‖C (boundedSpectralEvolution A t x)‖ ^ 2)
        atTop (𝓝 0) := by
  sorry

/-- The pure-point RAGE criterion uses relative compactness of the full unitary orbit. -/
theorem rage_purePoint (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x : H) :
    x ∈ purePointOperatorSubspace A ↔
      IsCompact (closure (Set.range (fun t : ℝ ↦ boundedSpectralEvolution A t x))) := by
  sorry

end CKMA
