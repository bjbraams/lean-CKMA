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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Cauchy
import TauCeti.Analysis.InnerProductSpace.BorelCalculus.DiagonalMeasure

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
full unitary orbits. The argument reads atoms of TauCeti's diagonal measures by Lorentz
approximation, then applies Wiener's criterion to the polarized matrix coefficients.
Sources: GAPS 22.38 and 22.63.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology MeasureTheory
open scoped InnerProductSpace ComplexConjugate Pointwise

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

/-- A real multiple of `-I` is skew-adjoint in `ℂ`. -/
private lemma neg_I_mul_ofReal_mem_skewAdjoint (t : ℝ) :
    (-(t : ℂ) * Complex.I) ∈ skewAdjoint ℂ := by
  rw [skewAdjoint.mem_iff, Complex.star_def]
  simp [Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_neg, mul_comm]

/-- The bounded evolution is unitary. -/
private theorem boundedSpectralEvolution_mem_unitary (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (t : ℝ) : boundedSpectralEvolution A t ∈ unitary (H →L[ℂ] H) := by
  unfold boundedSpectralEvolution
  let +nondep : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ _
  exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    (IsSelfAdjoint.smul_mem_skewAdjoint (neg_I_mul_ofReal_mem_skewAdjoint t) hA)

/-- The bounded evolution preserves norms. -/
private theorem norm_boundedSpectralEvolution (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ)
    (x : H) : ‖boundedSpectralEvolution A t x‖ = ‖x‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (boundedSpectralEvolution_mem_unitary A hA t) x

/-- Adjoint of the evolution at time `t` is the evolution at time `-t`. -/
private theorem star_boundedSpectralEvolution (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    star (boundedSpectralEvolution A t) = boundedSpectralEvolution A (-t) := by
  unfold boundedSpectralEvolution
  rw [NormedSpace.star_exp, star_smul, hA.star_eq]
  congr 1
  simp [Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_neg, mul_comm]

omit [CompleteSpace H] in
/-- Powers of an operator act by powers of the eigenvalue. -/
private theorem pow_apply_of_eigenvector (B : H →L[ℂ] H) {v : H} {b : ℂ} (hv : B v = b • v)
    (n : ℕ) : (B ^ n) v = b ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, map_smul, hv, smul_smul, pow_succ]

/-- The exponential series acts by the scalar exponential on an eigenvector. -/
private theorem exp_apply_of_eigenvector (B : H →L[ℂ] H) {v : H} {b : ℂ} (hv : B v = b • v) :
    NormedSpace.exp B v = Complex.exp b • v := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  change (∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹) • B ^ n) v = Complex.exp b • v
  have hsum := (ContinuousLinearMap.apply ℂ H v).map_tsum
    (NormedSpace.expSeries_summable' (𝕂 := ℂ) B)
  rw [← ContinuousLinearMap.apply_apply, hsum]
  have hterm (n : ℕ) :
      (ContinuousLinearMap.apply ℂ H v) (((Nat.factorial n : ℂ)⁻¹) • B ^ n) =
        (((Nat.factorial n : ℂ)⁻¹) • b ^ n) • v := by
    rw [ContinuousLinearMap.apply_apply, smul_apply, pow_apply_of_eigenvector B hv, smul_assoc]
  have hfun :
      (fun n : ℕ => (ContinuousLinearMap.apply ℂ H v)
        (((Nat.factorial n : ℂ)⁻¹) • B ^ n)) =
        fun n : ℕ => (((Nat.factorial n : ℂ)⁻¹) • b ^ n) • v := by
    funext n
    exact hterm n
  have hexp : (∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹) • b ^ n) = Complex.exp b := by
    symm
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum ℂ]
  rw [hfun, (NormedSpace.expSeries_summable' (𝕂 := ℂ) b).tsum_smul_const v, hexp]

/-- An eigenvector evolves by the scalar phase `exp(-i t a)`. -/
private theorem boundedSpectralEvolution_apply_eigenvector (A : H →L[ℂ] H) {v : H} {a : ℝ}
    (hv : A v = (a : ℂ) • v) (t : ℝ) :
    boundedSpectralEvolution A t v =
      Complex.exp ((-(t : ℂ) * Complex.I) * a) • v := by
  unfold boundedSpectralEvolution
  have hsmul : ((-(t : ℂ) * Complex.I) • A) v =
      ((-(t : ℂ) * Complex.I) * a) • v := by
    rw [smul_apply, hv, smul_smul]
  exact exp_apply_of_eigenvector _ hsmul

/-- The evolution is the continuous functional calculus of `z ↦ exp(-i t z)`. -/
private theorem boundedSpectralEvolution_eq_cfc (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    boundedSpectralEvolution A t =
      cfc (fun z : ℂ => Complex.exp ((-(t : ℂ) * Complex.I) * z)) A := by
  have : IsStarNormal A := hA.isStarNormal
  unfold boundedSpectralEvolution
  rw [← CFC.complex_exp_eq_normedSpace_exp (a := (-(t : ℂ) * Complex.I) • A),
    ← cfc_comp_const_mul (-(t : ℂ) * Complex.I) Complex.exp A]

/-- Matrix element of the evolution against the backward orbit. -/
private theorem inner_boundedSpectralEvolution (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ)
    (x y : H) :
    ⟪y, boundedSpectralEvolution A t x⟫_ℂ =
      ⟪boundedSpectralEvolution A (-t) y, x⟫_ℂ := by
  rw [← (boundedSpectralEvolution A t).adjoint_inner_left x y,
    ← ContinuousLinearMap.star_eq_adjoint, star_boundedSpectralEvolution A hA t]

/-- Coefficients of the polarization identity for `⟪y, T x⟫`. -/
private def polCoeff : Fin 4 → ℂ
  | 0 => 4⁻¹
  | 1 => -(4⁻¹)
  | 2 => Complex.I * 4⁻¹
  | 3 => -(Complex.I * 4⁻¹)

/-- The four arguments of the polarization identity. -/
private def polVec (x y : H) : Fin 4 → H
  | 0 => x + y
  | 1 => x - y
  | 2 => x + Complex.I • y
  | 3 => x - Complex.I • y

/-- Polarization expresses `⟪y, T x⟫` by four diagonal matrix elements. -/
private theorem inner_eq_sum_pol (T : H →L[ℂ] H) (x y : H) :
    ⟪y, T x⟫_ℂ =
      ∑ j : Fin 4, polCoeff j * ⟪polVec x y j, T (polVec x y j)⟫_ℂ := by
  have hpol := inner_map_polarization (T.adjoint : H →ₗ[ℂ] H) x y
  simp only [ContinuousLinearMap.coe_coe] at hpol
  rw [← ContinuousLinearMap.adjoint_inner_left T x y, hpol]
  simp only [Fin.sum_univ_four, polCoeff, polVec, ContinuousLinearMap.adjoint_inner_left,
    mul_comm, div_eq_mul_inv]
  ring

/-- A real scalar is a self-adjoint complex number. -/
private lemma isSelfAdjoint_of_im_eq_zero {lam : ℂ} (hlam : lam.im = 0) : IsSelfAdjoint lam := by
  rw [isSelfAdjoint_iff, Complex.star_def]
  exact Complex.conj_eq_iff_im.mpr hlam

/-- The real translate `A - λ` of a self-adjoint operator is self-adjoint. -/
private lemma eigenShift_isSelfAdjoint (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {lam : ℂ}
    (hlam : lam.im = 0) : IsSelfAdjoint (A - lam • (1 : H →L[ℂ] H)) :=
  hA.sub ((isSelfAdjoint_of_im_eq_zero hlam).smul
    (IsSelfAdjoint.one (H →L[ℂ] H)))

/-- `A - λ` is the continuous functional calculus of `z ↦ z - λ`. -/
private lemma eigenShift_eq_cfc (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (lam : ℂ) :
    A - lam • (1 : H →L[ℂ] H) = cfc (fun z : ℂ => z - lam) A := by
  have : IsStarNormal A := hA.isStarNormal
  rw [cfc_sub (fun z : ℂ => z) (fun _ : ℂ => lam) A, cfc_id' ℂ A, cfc_const lam A]
  simp [Algebra.algebraMap_eq_smul_one]

/-- On a real scalar, the square agrees with the squared modulus. -/
private lemma sq_sub_eq_ofReal_norm_sq {z lam : ℂ} (hz : z.im = 0) (hlam : lam.im = 0) :
    (z - lam) ^ 2 = ↑(‖z - lam‖ ^ 2) := by
  have hz' : z = ↑z.re := Complex.ext rfl hz
  have hl' : lam = ↑lam.re := Complex.ext rfl hlam
  rw [hz', hl', ← Complex.ofReal_sub, ← Complex.ofReal_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- Lorentz symbol `ε² / (‖z - λ‖² + ε²)`. Division by zero is the Lean totalization. -/
private def eigenLorentzFun (lam : ℂ) (eps : ℝ) : ℂ → ℂ :=
  fun z => ↑(eps ^ 2 / (‖z - lam‖ ^ 2 + eps ^ 2))

/-- The Lorentz symbol is continuous for positive width. -/
private lemma continuous_eigenLorentzFun {lam : ℂ} {eps : ℝ} (heps : 0 < eps) :
    Continuous (eigenLorentzFun lam eps) := by
  unfold eigenLorentzFun
  refine Complex.continuous_ofReal.comp ?_
  refine Continuous.div continuous_const
      (((continuous_norm.comp (continuous_id.sub continuous_const)).pow 2).add
        continuous_const) ?_
  intro z
  exact ne_of_gt <| lt_of_lt_of_le (by positivity : 0 < eps ^ 2)
    (le_add_of_nonneg_left (sq_nonneg _))

/-- On real points the Lorentz symbol is the rational function of `(z - λ)²`. -/
private lemma eigenLorentzFun_eq_div {lam z : ℂ} (hlam : lam.im = 0) (hz : z.im = 0)
    {eps : ℝ} (_heps : 0 < eps) :
    eigenLorentzFun lam eps z = (eps : ℂ) ^ 2 / ((z - lam) ^ 2 + (eps : ℂ) ^ 2) := by
  rw [sq_sub_eq_ofReal_norm_sq hz hlam, eigenLorentzFun, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_add, ← Complex.ofReal_pow]

/-- Algebraic identity of the Lorentz symbol on real points. -/
private lemma eigenLorentz_symbol_id {lam z : ℂ} (hlam : lam.im = 0) (hz : z.im = 0)
    {eps : ℝ} (heps : 0 < eps) :
    (z - lam) ^ 2 * eigenLorentzFun lam eps z =
      (eps : ℂ) ^ 2 * (1 - eigenLorentzFun lam eps z) := by
  rw [eigenLorentzFun_eq_div hlam hz heps]
  have hd : (z - lam) ^ 2 + (eps : ℂ) ^ 2 ≠ 0 := by
    rw [sq_sub_eq_ofReal_norm_sq hz hlam, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Complex.ofReal_ne_zero]
    positivity
  field_simp
  ring

/-- Lorentz approximant, as a continuous functional calculus. -/
private def eigenLorentz (A : H →L[ℂ] H) (lam : ℂ) (eps : ℝ) : H →L[ℂ] H :=
  cfc (eigenLorentzFun lam eps) A

/-- The Lorentz approximant is self-adjoint for positive width. -/
private lemma eigenLorentz_isSelfAdjoint (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (lam : ℂ)
    {eps : ℝ} (_heps : 0 < eps) : IsSelfAdjoint (eigenLorentz A lam eps) := by
  have : IsStarNormal A := hA.isStarNormal
  rw [eigenLorentz, IsSelfAdjoint, ← cfc_star]
  exact cfc_congr fun _ _ => by simp [eigenLorentzFun, Complex.conj_ofReal]

/-- `B² φ = ε² (1 - φ)` for the Lorentz approximant `φ` of `B = A - λ`. -/
private lemma eigenLorentz_mul_shift_sq (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {lam : ℂ}
    (hlam : lam.im = 0) {eps : ℝ} (heps : 0 < eps) :
    (A - lam • (1 : H →L[ℂ] H)) ^ 2 * eigenLorentz A lam eps =
      (eps : ℂ) ^ 2 • (1 - eigenLorentz A lam eps) := by
  have : IsStarNormal A := hA.isStarNormal
  let shift : ℂ → ℂ := fun z => z - lam
  have hshift : ContinuousOn shift (spectrum ℂ A) :=
    (continuous_id.sub continuous_const).continuousOn
  have hφ : ContinuousOn (eigenLorentzFun lam eps) (spectrum ℂ A) :=
    (continuous_eigenLorentzFun heps).continuousOn
  have hsq : ContinuousOn (fun z : ℂ => shift z ^ 2) (spectrum ℂ A) := hshift.pow 2
  have hone : ContinuousOn (fun _ : ℂ => (1 : ℂ)) (spectrum ℂ A) := continuousOn_const
  rw [eigenShift_eq_cfc A hA lam, eigenLorentz, pow_two,
    ← cfc_mul shift shift A hshift hshift]
  have hpow : cfc (fun z : ℂ => shift z * shift z) A = cfc (fun z : ℂ => shift z ^ 2) A :=
    cfc_congr fun z _ => by simp [shift, pow_two]
  rw [hpow, ← cfc_mul (fun z : ℂ => shift z ^ 2) (eigenLorentzFun lam eps) A hsq hφ]
  have hdiff : cfc (fun z : ℂ => (1 : ℂ) - eigenLorentzFun lam eps z) A =
      1 - cfc (eigenLorentzFun lam eps) A := by
    rw [cfc_sub (fun _ : ℂ => (1 : ℂ)) (eigenLorentzFun lam eps) A hone hφ, cfc_const_one ℂ A]
  rw [← hdiff, ← cfc_const_mul ((eps : ℂ) ^ 2)
      (fun z : ℂ => (1 : ℂ) - eigenLorentzFun lam eps z) A
      ((continuous_const.sub (continuous_eigenLorentzFun heps)).continuousOn)]
  refine cfc_congr fun z hz => ?_
  simpa [shift] using eigenLorentz_symbol_id hlam (hA.im_eq_zero_of_mem_spectrum hz) heps

/-- The Lorentz approximant commutes with `A - λ`. -/
private lemma eigenLorentz_commute_shift (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {lam : ℂ}
    (_hlam : lam.im = 0) {eps : ℝ} (_heps : 0 < eps) :
    Commute (A - lam • (1 : H →L[ℂ] H)) (eigenLorentz A lam eps) := by
  have : IsStarNormal A := hA.isStarNormal
  rw [eigenShift_eq_cfc A hA lam, eigenLorentz]
  exact cfc_commute_cfc (fun z : ℂ => z - lam) (eigenLorentzFun lam eps) A

/-- Squared norm of the shifted Lorentz approximant. -/
private lemma eigenLorentz_shift_norm_sq (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {lam : ℂ}
    (hlam : lam.im = 0) {eps : ℝ} (heps : 0 < eps) (x : H) :
    let B := A - lam • (1 : H →L[ℂ] H)
    let φ := eigenLorentz A lam eps
    ‖B (φ x)‖ ^ 2 = eps ^ 2 * ((⟪x, φ x⟫_ℂ).re - ‖φ x‖ ^ 2) := by
  intro B φ
  have hBsa : IsSelfAdjoint B := eigenShift_isSelfAdjoint A hA hlam
  have hmul := eigenLorentz_mul_shift_sq A hA hlam heps
  have happ : B (B (φ x)) = (eps : ℂ) ^ 2 • (x - φ x) := by
    have hmulx : (B ^ 2 * φ) x = ((eps : ℂ) ^ 2 • (1 - φ)) x := congr_arg (· x) hmul
    rw [mul_apply_eq_comp, pow_two, mul_apply_eq_comp, smul_apply] at hmulx
    conv_rhs at hmulx => rw [sub_apply, one_apply_eq_self]
    exact hmulx
  have hswap : ⟪B (B (φ x)), φ x⟫_ℂ = ⟪B (φ x), B (φ x)⟫_ℂ := by
    calc
      ⟪B (B (φ x)), φ x⟫_ℂ = ⟪B (φ x), B.adjoint (φ x)⟫_ℂ :=
        (B.adjoint_inner_right (B (φ x)) (φ x)).symm
      _ = ⟪B (φ x), B (φ x)⟫_ℂ := by
        rw [← ContinuousLinearMap.star_eq_adjoint, hBsa.star_eq]
  have hcoe : (eps : ℂ) ^ 2 = ↑(eps ^ 2) := (Complex.ofReal_pow eps 2).symm
  have hstar : (starRingEnd ℂ) ((eps : ℂ) ^ 2) = (eps : ℂ) ^ 2 := by
    rw [hcoe, starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
  calc
    ‖B (φ x)‖ ^ 2 = RCLike.re ⟪B (φ x), B (φ x)⟫_ℂ := norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = RCLike.re ⟪B (B (φ x)), φ x⟫_ℂ := by rw [hswap]
    _ = RCLike.re ⟪(eps : ℂ) ^ 2 • (x - φ x), φ x⟫_ℂ := by rw [happ]
    _ = RCLike.re (((eps : ℂ) ^ 2) * (⟪x, φ x⟫_ℂ - ⟪φ x, φ x⟫_ℂ)) := by
      rw [inner_smul_left, hstar, inner_sub_left]
    _ = eps ^ 2 * ((⟪x, φ x⟫_ℂ).re - ‖φ x‖ ^ 2) := by
      have hsq : (((‖φ x‖ : ℂ) ^ 2).re) = ‖φ x‖ ^ 2 := by
        rw [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        ring
      rw [hcoe, inner_self_eq_norm_sq_to_K, RCLike.mul_re, RCLike.re_eq_complex_re,
        RCLike.im_eq_complex_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.sub_re]
      congr 1
      refine congrArg (fun t : ℝ => (⟪x, φ x⟫_ℂ).re - t) ?_
      exact hsq

/-- The Lorentz approximant is a contraction. -/
private lemma eigenLorentz_norm_apply_le (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {lam : ℂ}
    (hlam : lam.im = 0) {eps : ℝ} (heps : 0 < eps) (x : H) :
    ‖eigenLorentz A lam eps x‖ ≤ ‖x‖ := by
  set φx := eigenLorentz A lam eps x
  have hsq := eigenLorentz_shift_norm_sq A hA hlam heps x
  have hnn : 0 ≤ eps ^ 2 * ((⟪x, φx⟫_ℂ).re - ‖φx‖ ^ 2) := by
    rw [← hsq]
    exact sq_nonneg _
  have hre : ‖φx‖ ^ 2 ≤ (⟪x, φx⟫_ℂ).re := by
    have hpos : 0 < eps ^ 2 := by positivity
    have : 0 ≤ (⟪x, φx⟫_ℂ).re - ‖φx‖ ^ 2 :=
      (mul_nonneg_iff_of_pos_left hpos).mp hnn
    linarith
  have hcs : (⟪x, φx⟫_ℂ).re ≤ ‖x‖ * ‖φx‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  rcases eq_or_ne φx 0 with h0 | h0
  · simp [h0]
  · have hmul : ‖φx‖ * ‖φx‖ ≤ ‖x‖ * ‖φx‖ := by
      simpa [pow_two] using hre.trans hcs
    exact le_of_mul_le_mul_of_pos_right hmul (norm_pos_iff.mpr h0)

/-- The Lorentz approximant kills approximate range vectors up to the width. -/
private lemma eigenLorentz_apply_shift_le (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {lam : ℂ}
    (hlam : lam.im = 0) {eps : ℝ} (heps : 0 < eps) (y : H) :
    ‖eigenLorentz A lam eps ((A - lam • (1 : H →L[ℂ] H)) y)‖ ≤ eps * ‖y‖ := by
  have hcomm := eigenLorentz_commute_shift A hA hlam heps
  have hswap : eigenLorentz A lam eps ((A - lam • (1 : H →L[ℂ] H)) y) =
      (A - lam • (1 : H →L[ℂ] H)) (eigenLorentz A lam eps y) := by
    simpa only [mul_apply_eq_comp] using congrArg
      (fun T : H →L[ℂ] H => T y) hcomm.symm
  rw [hswap]
  have hsq := eigenLorentz_shift_norm_sq A hA hlam heps y
  have hre : (⟪y, eigenLorentz A lam eps y⟫_ℂ).re ≤ ‖y‖ * ‖eigenLorentz A lam eps y‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hle : ‖(A - lam • (1 : H →L[ℂ] H)) (eigenLorentz A lam eps y)‖ ^ 2 ≤
      eps ^ 2 * ‖y‖ ^ 2 := by
    rw [hsq]
    have hdiff : (⟪y, eigenLorentz A lam eps y⟫_ℂ).re - ‖eigenLorentz A lam eps y‖ ^ 2 ≤
        ‖y‖ * ‖eigenLorentz A lam eps y‖ := by
      have : 0 ≤ ‖eigenLorentz A lam eps y‖ ^ 2 := sq_nonneg _
      linarith
    have hnorm : ‖eigenLorentz A lam eps y‖ ≤ ‖y‖ :=
      eigenLorentz_norm_apply_le A hA hlam heps y
    have : (⟪y, eigenLorentz A lam eps y⟫_ℂ).re - ‖eigenLorentz A lam eps y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      have hmul : ‖y‖ * ‖eigenLorentz A lam eps y‖ ≤ ‖y‖ * ‖y‖ :=
        mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      linarith
    have heps0 : 0 ≤ eps ^ 2 := sq_nonneg _
    nlinarith
  have hnn : 0 ≤ eps := heps.le
  exact (le_of_sq_le_sq (by simpa [mul_pow] using hle) (mul_nonneg hnn (norm_nonneg _)))

/-- The Lorentz approximant fixes the eigenspace of `A - λ`. -/
private lemma eigenLorentz_apply_ker (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {lam : ℂ}
    (hlam : lam.im = 0) {eps : ℝ} (heps : 0 < eps) {v : H}
    (hv : (A - lam • (1 : H →L[ℂ] H)) v = 0) : eigenLorentz A lam eps v = v := by
  have hcomm := eigenLorentz_commute_shift A hA hlam heps
  have hBv : (A - lam • (1 : H →L[ℂ] H)) (eigenLorentz A lam eps v) = 0 := by
    have hswap := congrArg (fun T : H →L[ℂ] H => T v) hcomm
    simpa only [mul_apply_eq_comp, hv, map_zero] using hswap
  have happ : (A - lam • (1 : H →L[ℂ] H))
      ((A - lam • (1 : H →L[ℂ] H)) (eigenLorentz A lam eps v)) =
      (eps : ℂ) ^ 2 • (v - eigenLorentz A lam eps v) := by
    have hmul := congrArg (fun T : H →L[ℂ] H => T v)
      (eigenLorentz_mul_shift_sq A hA hlam heps)
    simpa only [mul_apply_eq_comp, pow_two, smul_apply, sub_apply, one_apply_eq_self,
      map_sub] using hmul
  have hzero : (eps : ℂ) ^ 2 • (v - eigenLorentz A lam eps v) = 0 := by
    rw [hBv, map_zero] at happ
    exact happ.symm
  have heps0 : (eps : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (pow_ne_zero 2 heps.ne')
  exact (sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_left heps0)).symm

/-- Lorentz approximants converge strongly to the eigenspace projection. -/
private theorem tendsto_eigenLorentz_apply (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {lam : ℂ}
    (hlam : lam.im = 0) (x : H) :
    Tendsto (fun n : ℕ => eigenLorentz A lam (1 / (n + 1 : ℝ)) x) atTop
      (𝓝 ((A - lam • (1 : H →L[ℂ] H)).ker.starProjection x)) := by
  let B := A - lam • (1 : H →L[ℂ] H)
  let P := B.ker.starProjection
  have hBsa := eigenShift_isSelfAdjoint A hA hlam
  have hnorm : IsStarNormal B := hBsa.isStarNormal
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hfix (n : ℕ) : eigenLorentz A lam (1 / (n + 1 : ℝ)) (P x) = P x :=
    eigenLorentz_apply_ker A hA hlam (by positivity : 0 < 1 / (n + 1 : ℝ))
      (by simpa [B, P] using LinearMap.mem_ker.mp (B.ker.starProjection_apply_mem x))
  have hdiff (n : ℕ) :
      eigenLorentz A lam (1 / (n + 1 : ℝ)) x - P x =
        eigenLorentz A lam (1 / (n + 1 : ℝ)) (x - P x) := by
    rw [map_sub, hfix n]
  have hnorm_eq : (fun n : ℕ => ‖eigenLorentz A lam (1 / (n + 1 : ℝ)) x - P x‖) =
      fun n : ℕ => ‖eigenLorentz A lam (1 / (n + 1 : ℝ)) (x - P x)‖ := by
    funext n
    rw [hdiff n]
  rw [hnorm_eq]
  let z := x - P x
  have hz : z ∈ B.range.topologicalClosure := by
    have horth : B.kerᗮ = B.range.topologicalClosure := by
      rw [← ContinuousLinearMap.IsStarNormal.orthogonal_range hnorm,
        Submodule.orthogonal_orthogonal_eq_closure]
    rw [← horth]
    simp [z, P]
  refine Metric.tendsto_atTop.2 fun eps heps => ?_
  obtain ⟨b, hb, hdist⟩ :=
    (Metric.mem_closure_iff.mp hz (eps / 2) (half_pos heps))
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hb
  rw [← hy] at hdist
  have htail : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ)) * ‖y‖) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa [div_eq_mul_inv, mul_comm] using
      (tendsto_inv_atTop_zero.comp hinv).const_mul ‖y‖
  rw [Metric.tendsto_atTop] at htail
  obtain ⟨N, hN⟩ := htail (eps / 2) (half_pos heps)
  refine ⟨N, fun n hn => ?_⟩
  have hepsn : 0 < 1 / (n + 1 : ℝ) := by positivity
  have htail_lt : (1 / (n + 1 : ℝ)) * ‖y‖ < eps / 2 := by
    have hlt := hN n hn
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hlt
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  calc
    ‖eigenLorentz A lam (1 / (n + 1 : ℝ)) z‖ =
        ‖eigenLorentz A lam (1 / (n + 1 : ℝ)) ((z - B y) + B y)‖ := by
      conv_lhs => rw [← sub_add_cancel z (B y)]
    _ = ‖eigenLorentz A lam (1 / (n + 1 : ℝ)) (z - B y) +
          eigenLorentz A lam (1 / (n + 1 : ℝ)) (B y)‖ := by
      rw [map_add]
    _ ≤ ‖eigenLorentz A lam (1 / (n + 1 : ℝ)) (z - B y)‖ +
        ‖eigenLorentz A lam (1 / (n + 1 : ℝ)) (B y)‖ := norm_add_le _ _
    _ ≤ ‖z - B y‖ + (1 / (n + 1 : ℝ)) * ‖y‖ := by
      gcongr
      · exact eigenLorentz_norm_apply_le A hA hlam hepsn _
      · simpa [B] using eigenLorentz_apply_shift_le A hA hlam hepsn y
    _ < eps / 2 + eps / 2 :=
      add_lt_add (by simpa [dist_eq_norm] using hdist) htail_lt
    _ = eps := add_halves eps

/-- The phase `exp(-i t z)` in the bounded evolution. -/
private def evolutionPhase (t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((-(t : ℂ) * Complex.I) * z)

/-- At a real frequency the phase lies on the unit circle. -/
private lemma norm_evolutionPhase_of_im_eq_zero (t : ℝ) {w : ℂ} (hw : w.im = 0) :
    ‖evolutionPhase t w‖ = 1 := by
  have hw' : w = ↑w.re := Complex.ext rfl hw
  rw [evolutionPhase, Complex.norm_exp, hw']
  have hre : ((-(t : ℂ) * Complex.I) * ↑w.re).re = 0 := by
    have hcomm : (-(t : ℂ) * Complex.I) * ↑w.re = (↑(-(t * w.re))) * Complex.I := by
      simp only [Complex.ofReal_neg, Complex.ofReal_mul]
      ring
    rw [hcomm, Complex.mul_I_re, Complex.ofReal_im, neg_zero]
  rw [hre, Real.exp_zero]

/-- Cesàro kernel of the phase, `(1/T) ∫_0^T exp(-i t w) dt`. -/
private def cesaroPhase (T : ℝ) (w : ℂ) : ℂ :=
  T⁻¹ * ∫ t in (0 : ℝ)..T, evolutionPhase t w

/-- The Cesàro kernel is a contraction at real frequencies. -/
private lemma norm_cesaroPhase_le {T : ℝ} (hT : 0 < T) {w : ℂ} (hw : w.im = 0) :
    ‖cesaroPhase T w‖ ≤ 1 := by
  have hle : ‖∫ t in (0 : ℝ)..T, evolutionPhase t w‖ ≤ T := by
    refine (intervalIntegral.norm_integral_le_integral_norm hT.le).trans ?_
    simp_rw [norm_evolutionPhase_of_im_eq_zero _ hw, intervalIntegral.integral_const,
      sub_zero, smul_eq_mul, mul_one]
    exact le_rfl
  rw [cesaroPhase, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hT.le)]
  calc
    T⁻¹ * ‖∫ t in (0 : ℝ)..T, evolutionPhase t w‖ ≤ T⁻¹ * T :=
      mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hT.le)
    _ = 1 := inv_mul_cancel₀ hT.ne'

/-- At frequency zero the Cesàro kernel equals one. -/
private lemma cesaroPhase_zero {T : ℝ} (hT : 0 < T) : cesaroPhase T 0 = 1 := by
  unfold cesaroPhase evolutionPhase
  simp only [mul_zero, Complex.exp_zero, intervalIntegral.integral_const, sub_zero]
  rw [Complex.real_smul, mul_one, Complex.ofReal_inv]
  exact inv_mul_cancel₀ (mod_cast hT.ne')

/-- The phase is differentiable, with derivative `(-i w) exp(-i t w)`. -/
private lemma hasDerivAt_evolutionPhase (w : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => evolutionPhase s w)
      (((-Complex.I) * w) * evolutionPhase t w) t := by
  unfold evolutionPhase
  simp_rw [show ∀ s : ℝ, (-(s : ℂ) * Complex.I) * w = (s : ℂ) * ((-Complex.I) * w) by
    intro s; ring]
  let c : ℂ := (-Complex.I) * w
  change HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * c))
    (c * Complex.exp ((t : ℂ) * c)) t
  rw [Complex.exp_eq_exp_ℂ, mul_comm c (NormedSpace.exp _)]
  exact ((hasDerivAt_exp (x := (t : ℂ) * c)).comp (t : ℂ)
    (hasDerivAt_mul_const c)).comp_ofReal

/-- Off zero, the Cesàro kernel of a real frequency tends to zero. -/
private lemma tendsto_cesaroPhase_of_ne_zero {w : ℂ} (hw : w.im = 0) (hw0 : w ≠ 0) :
    Tendsto (fun T : ℝ => cesaroPhase T w) atTop (𝓝 0) := by
  let c : ℂ := (-Complex.I) * w
  have hc0 : c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hw0
  have hder (T : ℝ) : ∀ x ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun s => evolutionPhase s w) (c * evolutionPhase x w) x := by
    intro x _
    simpa [c] using hasDerivAt_evolutionPhase w x
  have hint (T : ℝ) : IntervalIntegrable (fun s => c * evolutionPhase s w) volume 0 T :=
    (continuous_const.mul (by
      unfold evolutionPhase
      fun_prop)).intervalIntegrable _ _
  refine Metric.tendsto_atTop.2 fun eps heps => ?_
  let M : ℝ := 2 * ‖c‖⁻¹
  have hM : 0 ≤ M := by positivity
  let T0 : ℝ := max 1 (M / eps + 1)
  have hT0pos : 0 < T0 := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hT0eps : M / T0 < eps := by
    have hden : M / eps + 1 ≤ T0 := le_max_right _ _
    have hpos : 0 < M / eps + 1 := by positivity
    calc
      M / T0 ≤ M / (M / eps + 1) := by gcongr
      _ < eps := by
        rw [div_lt_iff₀ hpos]
        have : (M / eps + 1) * eps = M + eps := by
          rw [add_mul, div_mul_cancel₀ _ heps.ne', one_mul]
        linarith
  refine ⟨T0, fun T hT => ?_⟩
  have hTpos : 0 < T := lt_of_lt_of_le hT0pos hT
  have heq : ∫ s in (0 : ℝ)..T, evolutionPhase s w =
      c⁻¹ * (evolutionPhase T w - 1) := by
    have hsub : ∫ s in (0 : ℝ)..T, c * evolutionPhase s w =
        evolutionPhase T w - evolutionPhase 0 w :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (hder T) (hint T)
    rw [intervalIntegral.integral_const_mul] at hsub
    have h0 : evolutionPhase 0 w = 1 := by simp [evolutionPhase]
    rw [h0] at hsub
    apply mul_left_cancel₀ hc0
    rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    exact hsub
  rw [dist_zero_right, cesaroPhase, heq, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr hTpos.le), norm_inv]
  have hphase : ‖evolutionPhase T w - 1‖ ≤ 2 := by
    calc
      ‖evolutionPhase T w - 1‖ ≤ ‖evolutionPhase T w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [norm_evolutionPhase_of_im_eq_zero T hw, norm_one]
      _ = 2 := by ring
  calc
    T⁻¹ * (‖c‖⁻¹ * ‖evolutionPhase T w - 1‖) ≤ T⁻¹ * (‖c‖⁻¹ * 2) := by gcongr
    _ = M / T := by ring
    _ ≤ M / T0 := by gcongr
    _ < eps := hT0eps

/-- A real frequency conjugates to the phase of the opposite frequency. -/
private lemma evolutionPhase_mul_conj (t : ℝ) {s r : ℂ} (hr : r.im = 0) :
    evolutionPhase t s * conj (evolutionPhase t r) = evolutionPhase t (s - r) := by
  have hr' : conj r = r := (Complex.conj_eq_iff_im).2 hr
  unfold evolutionPhase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  rw [RingHom.map_mul (starRingEnd ℂ), hr']
  have hI : conj (-(t : ℂ) * Complex.I) = (t : ℂ) * Complex.I := by
    simp [mul_neg, Complex.conj_ofReal, Complex.conj_I, neg_mul, neg_neg]
  rw [hI]
  ring

/-- The Cesàro kernel depends continuously on the frequency. -/
private lemma continuous_cesaroPhase (T : ℝ) : Continuous (cesaroPhase T) := by
  unfold cesaroPhase
  refine Continuous.const_smul ?_ (T⁻¹)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun w t => evolutionPhase t w) (by
      unfold evolutionPhase
      fun_prop) 0 T

/-- The Lorentz symbol takes values in the unit disk. -/
private lemma eigenLorentzFun_norm_le {lam z : ℂ} {eps : ℝ} (heps : 0 < eps) :
    ‖eigenLorentzFun lam eps z‖ ≤ 1 := by
  rw [eigenLorentzFun, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    div_le_one (by positivity)]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- Lorentz symbols converge pointwise to the eigenvalue indicator. -/
private lemma tendsto_eigenLorentzFun (lam z : ℂ) :
    Tendsto (fun n : ℕ => eigenLorentzFun lam (1 / (n + 1 : ℝ)) z) atTop
      (𝓝 (if z = lam then (1 : ℂ) else 0)) := by
  by_cases h : z = lam
  · subst h
    refine tendsto_const_nhds.congr fun n => ?_
    rw [ite_eq_left rfl, eigenLorentzFun, sub_self, norm_zero, zero_pow two_ne_zero, zero_add]
    have hpos : (1 / (n + 1 : ℝ)) ^ 2 ≠ 0 := by positivity
    rw [div_self hpos, Complex.ofReal_one]
  · rw [ite_eq_right h]
    have hd : 0 < ‖z - lam‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h)) 2
    have hinv : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ)) ^ 2) atTop (𝓝 0) := by
      have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      simpa [one_div] using (tendsto_inv_atTop_zero.comp hnat).pow 2
    have hle (n : ℕ) : (1 / (n + 1 : ℝ)) ^ 2 /
        (‖z - lam‖ ^ 2 + (1 / (n + 1 : ℝ)) ^ 2) ≤
        (1 / (n + 1 : ℝ)) ^ 2 / ‖z - lam‖ ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg (1 / (n + 1 : ℝ))) hd
        (le_add_of_nonneg_right (sq_nonneg _))
    have hupper : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ)) ^ 2 / ‖z - lam‖ ^ 2)
        atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using hinv.mul_const (‖z - lam‖ ^ 2)⁻¹
    exact (Complex.continuous_ofReal.tendsto 0).comp
      (squeeze_zero (fun _ => by positivity) hle hupper)

/-- Integrating the Lorentz symbol recovers its diagonal matrix element. -/
private lemma integral_eigenLorentzFun_eq (A : H →L[ℂ] H) [IsStarNormal A] (ξ : H)
    (lam : ℂ) {eps : ℝ} (heps : 0 < eps) :
    ∫ x, eigenLorentzFun lam eps x ∂(A.diagMeasure ξ) =
      ⟪ξ, eigenLorentz A lam eps ξ⟫_ℂ := by
  simpa [eigenLorentz] using ContinuousLinearMap.integral_diagMeasure_eq_inner_cfc A ξ
    (eigenLorentzFun lam eps) (continuous_eigenLorentzFun heps).continuousOn

omit [CompleteSpace H] in
/-- Real eigenvectors lie in the pure-point subspace. -/
private lemma ker_le_purePointOperatorSubspace (A : H →L[ℂ] H) {lam : ℂ}
    (hlam : lam.im = 0) :
    (A - lam • (1 : H →L[ℂ] H)).ker ≤ purePointOperatorSubspace A := by
  intro v hv
  have hlam' : lam = (lam.re : ℂ) := Complex.ext rfl hlam
  have hAv : A v = (lam.re : ℂ) • v := by
    have hv0 : (A - lam • (1 : H →L[ℂ] H)) v = 0 := LinearMap.mem_ker.mp hv
    rw [sub_apply, smul_apply, one_apply_eq_self, sub_eq_zero] at hv0
    rw [← hlam']
    exact hv0
  exact (Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨lam.re, hAv⟩)

/-- A vector orthogonal to the pure-point subspace has no eigenprojection. -/
private lemma eigenProjection_eq_zero_of_mem_orthogonal (A : H →L[ℂ] H)
    {lam : ℂ} (hlam : lam.im = 0) {ξ : H}
    (hξ : ξ ∈ (purePointOperatorSubspace A)ᗮ) :
    (A - lam • (1 : H →L[ℂ] H)).ker.starProjection ξ = 0 := by
  let B := A - lam • (1 : H →L[ℂ] H)
  have hmem : B.ker.starProjection ξ ∈ purePointOperatorSubspace A :=
    ker_le_purePointOperatorSubspace A hlam (B.ker.starProjection_apply_mem ξ)
  have hinner : ⟪B.ker.starProjection ξ, ξ⟫_ℂ = 0 :=
    ((purePointOperatorSubspace A).mem_orthogonal ξ).1 hξ _ hmem
  have hnorm := B.ker.re_inner_starProjection_eq_normSq ξ
  rw [hinner, RCLike.zero_re] at hnorm
  rw [Submodule.starProjection_apply]
  exact congrArg Subtype.val (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm.symm))

/-- Diagonal measures of continuous vectors are non-atomic. -/
private lemma diagMeasure_real_singleton_eq_zero (A : H →L[ℂ] H) [IsStarNormal A]
    (hA : IsSelfAdjoint A) {ξ : H} (hξ : ξ ∈ (purePointOperatorSubspace A)ᗮ)
    (p : spectrum ℂ A) : (A.diagMeasure ξ).real {p} = 0 := by
  let lam : ℂ := p
  have hlam : lam.im = 0 := hA.im_eq_zero_of_mem_spectrum p.property
  let μ := A.diagMeasure ξ
  let F : ℕ → spectrum ℂ A → ℂ :=
    fun n x => eigenLorentzFun lam (1 / (n + 1 : ℝ)) (x : ℂ)
  let f : spectrum ℂ A → ℂ := fun x => if (x : ℂ) = lam then 1 else 0
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) μ :=
    ((continuous_eigenLorentzFun (by positivity : 0 < 1 / (n + 1 : ℝ))).comp
      continuous_subtype_val).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ x ∂μ, ‖F n x‖ ≤ 1 :=
    Eventually.of_forall fun x => eigenLorentzFun_norm_le (by positivity)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)) :=
    Eventually.of_forall fun x => by simpa [F, f] using tendsto_eigenLorentzFun lam (x : ℂ)
  have hint := tendsto_integral_of_dominated_convergence (μ := μ) (F := F) (f := f)
    (fun _ => 1) hmeas (integrable_const 1) hbound hlim
  have hinner : Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 0) := by
    have heq (n : ℕ) : ∫ x, F n x ∂μ =
        ⟪ξ, eigenLorentz A lam (1 / (n + 1 : ℝ)) ξ⟫_ℂ := by
      simpa [F] using integral_eigenLorentzFun_eq A ξ lam (by positivity)
    simp_rw [heq]
    have hproj := eigenProjection_eq_zero_of_mem_orthogonal A hlam hξ
    have hvec := tendsto_eigenLorentz_apply A hA hlam ξ
    have hcomp := ((innerSL ℂ ξ).continuous.tendsto
      ((A - lam • (1 : H →L[ℂ] H)).ker.starProjection ξ)).comp hvec
    have hcomp' : Tendsto
        (fun n : ℕ => ⟪ξ, eigenLorentz A lam (1 / (n + 1 : ℝ)) ξ⟫_ℂ) atTop
        (𝓝 ⟪ξ, (A - lam • (1 : H →L[ℂ] H)).ker.starProjection ξ⟫_ℂ) :=
      (tendsto_congr (f₁ := (innerSL ℂ ξ) ∘
          fun n : ℕ => eigenLorentz A lam (1 / (n + 1 : ℝ)) ξ)
        (fun n : ℕ => innerSL_apply_apply ℂ ξ
          (eigenLorentz A lam (1 / (n + 1 : ℝ)) ξ))).1 hcomp
    rw [hproj, inner_zero_right] at hcomp'
    exact hcomp'
  have hzero : ∫ x, f x ∂μ = 0 := tendsto_nhds_unique hint hinner
  have hfun : f = ({p} : Set (spectrum ℂ A)).indicator (fun _ => (1 : ℂ)) := by
    funext x
    by_cases hx : x = p
    · subst hx
      simp [f, lam, Set.indicator]
    · have hne : (x : ℂ) ≠ lam := fun h => hx (Subtype.ext h)
      simp [f, Set.indicator, hx, hne]
  rw [hfun, integral_indicator_const (1 : ℂ) (measurableSet_singleton p),
    Complex.real_smul, mul_one] at hzero
  exact Complex.ofReal_eq_zero.mp hzero

/-- The phase depends continuously on the frequency. -/
private lemma continuous_evolutionPhase (t : ℝ) : Continuous (evolutionPhase t) := by
  unfold evolutionPhase
  fun_prop

/-- Time integral of a phase is the scalar multiple of its Cesàro kernel. -/
private lemma integral_evolutionPhase_eq_mul_cesaro {T : ℝ} (hT : 0 < T) (w : ℂ) :
    ∫ t in (0 : ℝ)..T, evolutionPhase t w = (T : ℂ) * cesaroPhase T w := by
  unfold cesaroPhase
  rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hT.ne', Complex.ofReal_one, one_mul]

/-- Squared modulus of a diagonal matrix element, as a double phase integral. -/
private lemma ofReal_normSq_inner_evolution (A : H →L[ℂ] H) [IsStarNormal A]
    (hA : IsSelfAdjoint A) (ξ : H) (t : ℝ) :
    (‖⟪ξ, boundedSpectralEvolution A t ξ⟫_ℂ‖ ^ 2 : ℂ) =
      ∫ p, evolutionPhase t ((p.1 : ℂ) - (p.2 : ℂ))
        ∂((A.diagMeasure ξ).prod (A.diagMeasure ξ)) := by
  let μ := A.diagMeasure ξ
  have hinner : ⟪ξ, boundedSpectralEvolution A t ξ⟫_ℂ =
      ∫ x, evolutionPhase t (x : ℂ) ∂μ := by
    rw [boundedSpectralEvolution_eq_cfc A hA t]
    simpa [evolutionPhase] using
      (ContinuousLinearMap.integral_diagMeasure_eq_inner_cfc A ξ
        (fun z : ℂ => Complex.exp ((-(t : ℂ) * Complex.I) * z)) (by fun_prop)).symm
  have hmul : ⟪ξ, boundedSpectralEvolution A t ξ⟫_ℂ *
      conj ⟪ξ, boundedSpectralEvolution A t ξ⟫_ℂ =
      ∫ p, evolutionPhase t ((p.1 : ℂ) - (p.2 : ℂ)) ∂(μ.prod μ) := by
    rw [hinner, ← integral_conj, ← integral_prod_mul]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    exact evolutionPhase_mul_conj t (hA.im_eq_zero_of_mem_spectrum p.2.property)
  exact (Complex.mul_conj' _).symm.trans hmul

/-- The phase is integrable on a finite time interval against a product of diagonal measures. -/
private lemma integrable_phase_uncurry (A : H →L[ℂ] H) [IsStarNormal A]
    (hA : IsSelfAdjoint A) (ξ : H) (T : ℝ) :
    Integrable (fun q : ℝ × (spectrum ℂ A × spectrum ℂ A) =>
      evolutionPhase q.1 ((q.2.1 : ℂ) - (q.2.2 : ℂ)))
      ((volume.restrict (Set.uIoc 0 T)).prod
        ((A.diagMeasure ξ).prod (A.diagMeasure ξ))) := by
  have : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) T)) := by
    rw [isFiniteMeasure_restrict, Real.volume_uIoc]
    exact ENNReal.ofReal_ne_top
  have hcont : Continuous (fun q : ℝ × (spectrum ℂ A × spectrum ℂ A) =>
      evolutionPhase q.1 ((q.2.1 : ℂ) - (q.2.2 : ℂ))) := by
    unfold evolutionPhase
    fun_prop
  refine (integrable_const (1 : ℂ)).mono hcont.aestronglyMeasurable ?_
  refine Eventually.of_forall fun q => ?_
  have him : ((q.2.1 : ℂ) - (q.2.2 : ℂ)).im = 0 := by
    simp [Complex.sub_im, hA.im_eq_zero_of_mem_spectrum q.2.1.property,
      hA.im_eq_zero_of_mem_spectrum q.2.2.property]
  rw [norm_evolutionPhase_of_im_eq_zero q.1 him, norm_one]

/-- The diagonal Cesàro mean equals the real part of the averaged phase kernel. -/
private lemma cesaro_normSq_inner_eq_re (A : H →L[ℂ] H) [IsStarNormal A]
    (hA : IsSelfAdjoint A) (ξ : H) {T : ℝ} (hT : 0 < T) :
    T⁻¹ * ∫ t in (0 : ℝ)..T, ‖⟪ξ, boundedSpectralEvolution A t ξ⟫_ℂ‖ ^ 2 =
      RCLike.re (∫ p, cesaroPhase T ((p.1 : ℂ) - (p.2 : ℂ))
        ∂((A.diagMeasure ξ).prod (A.diagMeasure ξ))) := by
  let ν := (A.diagMeasure ξ).prod (A.diagMeasure ξ)
  have hswap := intervalIntegral_integral_swap
    (f := fun t (p : spectrum ℂ A × spectrum ℂ A) =>
      evolutionPhase t ((p.1 : ℂ) - (p.2 : ℂ)))
    (integrable_phase_uncurry A hA ξ T)
  have hcomplex : ∫ t in (0 : ℝ)..T,
      (‖⟪ξ, boundedSpectralEvolution A t ξ⟫_ℂ‖ ^ 2 : ℂ) =
      (T : ℂ) * ∫ p, cesaroPhase T ((p.1 : ℂ) - (p.2 : ℂ)) ∂ν := by
    simp_rw [ofReal_normSq_inner_evolution A hA ξ]
    rw [hswap]
    simp_rw [integral_evolutionPhase_eq_mul_cesaro hT]
    exact integral_const_mul (T : ℂ) _
  have hre_point (t : ℝ) :
      ‖⟪ξ, boundedSpectralEvolution A t ξ⟫_ℂ‖ ^ 2 =
        RCLike.re ((‖⟪ξ, boundedSpectralEvolution A t ξ⟫_ℂ‖ ^ 2 : ℂ)) := by
    rw [← Complex.ofReal_pow]
    exact (RCLike.ofReal_re _).symm
  have hint : IntervalIntegrable
      (fun t : ℝ => (‖⟪ξ, boundedSpectralEvolution A t ξ⟫_ℂ‖ ^ 2 : ℂ)) volume 0 T := by
    let +nondep : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ _
    refine Continuous.intervalIntegrable (by
      unfold boundedSpectralEvolution
      fun_prop) 0 T
  have hreint :=
    (ContinuousLinearMap.intervalIntegral_comp_comm RCLike.reCLM hint).trans
      (congrArg RCLike.re hcomplex)
  have hreal : ∫ t in (0 : ℝ)..T, ‖⟪ξ, boundedSpectralEvolution A t ξ⟫_ℂ‖ ^ 2 =
      RCLike.re ((T : ℂ) * ∫ p, cesaroPhase T ((p.1 : ℂ) - (p.2 : ℂ)) ∂ν) := by
    rw [← hreint]
    exact intervalIntegral.integral_congr (fun t _ => hre_point t)
  have hfactor : RCLike.re ((T : ℂ) *
        ∫ p, cesaroPhase T ((p.1 : ℂ) - (p.2 : ℂ)) ∂ν) =
      T * RCLike.re (∫ p, cesaroPhase T ((p.1 : ℂ) - (p.2 : ℂ)) ∂ν) :=
    Complex.re_ofReal_mul _ _
  rw [hfactor] at hreal
  calc
    T⁻¹ * ∫ t in (0 : ℝ)..T, ‖⟪ξ, boundedSpectralEvolution A t ξ⟫_ℂ‖ ^ 2
      = T⁻¹ * (T * RCLike.re (∫ p, cesaroPhase T ((p.1 : ℂ) - (p.2 : ℂ)) ∂ν)) := by
        rw [hreal]
    _ = RCLike.re (∫ p, cesaroPhase T ((p.1 : ℂ) - (p.2 : ℂ)) ∂ν) := by
        rw [← mul_assoc, inv_mul_cancel₀ hT.ne', one_mul]

/-- Averaged phase kernels of a non-atomic diagonal measure tend to zero. -/
private lemma tendsto_integral_cesaroPhase (A : H →L[ℂ] H) [IsStarNormal A]
    (hA : IsSelfAdjoint A) {ξ : H} (hξ : ξ ∈ (purePointOperatorSubspace A)ᗮ) :
    Tendsto (fun T : ℝ => ∫ p, cesaroPhase T ((p.1 : ℂ) - (p.2 : ℂ))
      ∂((A.diagMeasure ξ).prod (A.diagMeasure ξ))) atTop (𝓝 0) := by
  let μ := A.diagMeasure ξ
  let ν := μ.prod μ
  let diff : spectrum ℂ A × spectrum ℂ A → ℂ := fun p => (p.1 : ℂ) - (p.2 : ℂ)
  let f : spectrum ℂ A × spectrum ℂ A → ℂ := fun p => if p.1 = p.2 then 1 else 0
  have him (p : spectrum ℂ A × spectrum ℂ A) : (diff p).im = 0 := by
    simp [diff, Complex.sub_im, hA.im_eq_zero_of_mem_spectrum p.1.property,
      hA.im_eq_zero_of_mem_spectrum p.2.property]
  have hlim (p : spectrum ℂ A × spectrum ℂ A) :
      Tendsto (fun T => cesaroPhase T (diff p)) atTop (𝓝 (f p)) := by
    by_cases hp : p.1 = p.2
    · simp only [diff, hp, sub_self, f, ite_eq_left hp]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with T hT
      exact (cesaroPhase_zero hT).symm
    · have hne : diff p ≠ 0 := sub_ne_zero.mpr (Subtype.coe_injective.ne hp)
      simp only [f, ite_eq_right hp]
      exact tendsto_cesaroPhase_of_ne_zero (him p) hne
  have hmeas : ∀ᶠ T in atTop, AEStronglyMeasurable (fun p => cesaroPhase T (diff p)) ν :=
    Eventually.of_forall fun T =>
      ((continuous_cesaroPhase T).comp (by unfold diff; fun_prop)).aestronglyMeasurable
  have hbound : ∀ᶠ T in atTop, ∀ᵐ p ∂ν, ‖cesaroPhase T (diff p)‖ ≤ 1 := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    exact Eventually.of_forall fun p => norm_cesaroPhase_le hT (him p)
  have hint := tendsto_integral_filter_of_dominated_convergence
    (F := fun T p => cesaroPhase T (diff p)) (f := f) (bound := fun _ => 1)
    hmeas hbound (integrable_const 1) (Eventually.of_forall hlim)
  have hf0 : ∫ p, f p ∂ν = 0 := by
    let D : Set (spectrum ℂ A × spectrum ℂ A) := {p | p.1 = p.2}
    have hD : MeasurableSet D := (isClosed_eq continuous_fst continuous_snd).measurableSet
    have hf : f = D.indicator (fun _ => (1 : ℂ)) := by
      funext p
      by_cases hp : p.1 = p.2
      · simp [f, D, hp, Set.indicator]
      · simp [f, D, hp, Set.indicator]
    rw [hf]
    have hintD : Integrable (D.indicator (fun _ => (1 : ℂ))) ν := by
      refine (integrable_const (1 : ℂ)).mono
        (Measurable.indicator measurable_const hD).aestronglyMeasurable ?_
      refine Eventually.of_forall fun p => ?_
      by_cases hp : p ∈ D
      · simp [Set.indicator, hp]
      · simp [Set.indicator, hp, zero_le_one]
    rw [integral_prod_symm _ hintD]
    have hinner (r : spectrum ℂ A) :
        ∫ s, D.indicator (fun _ => (1 : ℂ)) (s, r) ∂μ = (μ.real {r} : ℂ) := by
      have hpoint : (fun s => D.indicator (fun _ => (1 : ℂ)) (s, r)) =
          ({r} : Set (spectrum ℂ A)).indicator (fun _ => (1 : ℂ)) := by
        funext s
        by_cases hs : s = r
        · simp [D, hs, Set.indicator]
        · simp [D, hs, Set.indicator]
      rw [hpoint, integral_indicator_const (1 : ℂ) (measurableSet_singleton r),
        Complex.real_smul, mul_one]
    rw [integral_congr_ae (Eventually.of_forall hinner)]
    refine integral_eq_zero_of_ae ?_
    filter_upwards with r
    exact congrArg Complex.ofReal (diagMeasure_real_singleton_eq_zero A hA hξ r)
  simpa [hf0] using hint

/-- Diagonal time averages vanish on the continuous subspace. -/
private lemma tendsto_cesaro_normSq_inner (A : H →L[ℂ] H) [IsStarNormal A]
    (hA : IsSelfAdjoint A) {ξ : H} (hξ : ξ ∈ (purePointOperatorSubspace A)ᗮ) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T,
      ‖⟪ξ, boundedSpectralEvolution A t ξ⟫_ℂ‖ ^ 2) atTop (𝓝 0) := by
  have hcomplex := tendsto_integral_cesaroPhase A hA hξ
  have hre := (RCLike.continuous_re.tendsto (0 : ℂ)).comp hcomplex
  rw [RCLike.zero_re] at hre
  refine hre.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  exact (cesaro_normSq_inner_eq_re A hA ξ hT).symm

/-- The squared modulus of an evolution matrix element depends continuously on time. -/
private lemma continuous_normSq_inner_evolution (A : H →L[ℂ] H) (x y : H) :
    Continuous fun t : ℝ => ‖⟪y, boundedSpectralEvolution A t x⟫_ℂ‖ ^ 2 := by
  let +nondep : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ _
  unfold boundedSpectralEvolution
  fun_prop

/-- Each polarization coefficient has modulus one quarter. -/
private lemma norm_polCoeff (j : Fin 4) : ‖polCoeff j‖ = (4 : ℝ)⁻¹ := by
  fin_cases j <;> simp [polCoeff, norm_neg, Complex.norm_I, norm_inv]

/-- A sum of four real numbers is controlled by the sum of their squares. -/
private lemma four_sq_sum_le (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

/-- Polarization bounds a matrix element by four diagonal matrix elements. -/
private lemma normSq_inner_pol_le (T : H →L[ℂ] H) (x y : H) :
    ‖⟪y, T x⟫_ℂ‖ ^ 2 ≤
      ((4 : ℝ)⁻¹) * ∑ j : Fin 4, ‖⟪polVec x y j, T (polVec x y j)⟫_ℂ‖ ^ 2 := by
  let a : Fin 4 → ℝ := fun j => ‖⟪polVec x y j, T (polVec x y j)⟫_ℂ‖
  have hsum : ‖⟪y, T x⟫_ℂ‖ ≤ ((4 : ℝ)⁻¹) * ∑ j, a j := by
    rw [inner_eq_sum_pol]
    refine (norm_sum_le _ _).trans ?_
    simp_rw [norm_mul, norm_polCoeff, ← Finset.mul_sum, a]
    exact le_rfl
  have hsq : (∑ j, a j) ^ 2 ≤ 4 * ∑ j, a j ^ 2 := by
    simpa [a, Fin.sum_univ_four] using four_sq_sum_le (a 0) (a 1) (a 2) (a 3)
  have habs : ‖⟪y, T x⟫_ℂ‖ ^ 2 ≤ (((4 : ℝ)⁻¹) * ∑ j, a j) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hsum 2
  calc
    ‖⟪y, T x⟫_ℂ‖ ^ 2 ≤ (((4 : ℝ)⁻¹) * ∑ j, a j) ^ 2 := habs
    _ = ((4 : ℝ)⁻¹) ^ 2 * (∑ j, a j) ^ 2 := by ring
    _ ≤ ((4 : ℝ)⁻¹) ^ 2 * (4 * ∑ j, a j ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = ((4 : ℝ)⁻¹) * ∑ j, ‖⟪polVec x y j, T (polVec x y j)⟫_ℂ‖ ^ 2 := by
      simp only [a]
      ring

/-- The evolution preserves the pure-point subspace. -/
private lemma boundedSpectralEvolution_mem_purePoint (A : H →L[ℂ] H) {v : H}
    (hv : v ∈ purePointOperatorSubspace A) (t : ℝ) :
    boundedSpectralEvolution A t v ∈ purePointOperatorSubspace A := by
  let s : Set H := {w | ∃ a : ℝ, A w = (a : ℂ) • w}
  let S := Submodule.span ℂ s
  have hspan : S ≤ (purePointOperatorSubspace A).comap
      (boundedSpectralEvolution A t).toLinearMap := by
    rw [Submodule.span_le]
    intro w hw
    obtain ⟨a, ha⟩ := hw
    rw [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe,
      boundedSpectralEvolution_apply_eigenvector A ha t]
    refine Submodule.le_topologicalClosure S ?_
    refine Submodule.subset_span ?_
    refine ⟨a, ?_⟩
    rw [map_smul, ha, smul_smul, mul_comm, ← smul_smul]
  have hclosed : IsClosed ((purePointOperatorSubspace A).comap
      (boundedSpectralEvolution A t).toLinearMap : Set H) := by
    rw [Submodule.comap_coe]
    exact isClosed_closure.preimage (boundedSpectralEvolution A t).continuous
  exact Submodule.topologicalClosure_minimal S hspan hclosed hv

/-- The evolution preserves the continuous subspace. -/
private lemma boundedSpectralEvolution_mem_orthogonal (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    {v : H} (hv : v ∈ (purePointOperatorSubspace A)ᗮ) (t : ℝ) :
    boundedSpectralEvolution A t v ∈ (purePointOperatorSubspace A)ᗮ := by
  rw [(purePointOperatorSubspace A).mem_orthogonal]
  intro u hu
  rw [inner_boundedSpectralEvolution A hA t]
  exact ((purePointOperatorSubspace A).mem_orthogonal v).1 hv _
    (boundedSpectralEvolution_mem_purePoint A hu (-t))

/-- The pure-point subspace is complete, so orthogonal projection onto it exists. -/
private instance completeSpace_purePointOperatorSubspace (A : H →L[ℂ] H) :
    CompleteSpace (purePointOperatorSubspace A) :=
  Submodule.topologicalClosure.completeSpace _

/-- The evolution commutes with the pure-point projection. -/
private lemma boundedSpectralEvolution_starProjection (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (t : ℝ) (x : H) :
    boundedSpectralEvolution A t ((purePointOperatorSubspace A).starProjection x) =
      (purePointOperatorSubspace A).starProjection (boundedSpectralEvolution A t x) := by
  let P := purePointOperatorSubspace A
  symm
  refine P.eq_starProjection_of_mem_orthogonal
    (boundedSpectralEvolution_mem_purePoint A (P.starProjection_apply_mem x) t) ?_
  have horth : x - P.starProjection x ∈ Pᗮ := by
    rw [← P.starProjection_orthogonal_val]
    exact Pᗮ.starProjection_apply_mem x
  simpa [map_sub] using boundedSpectralEvolution_mem_orthogonal A hA horth t

/-- Off-diagonal time averages of two continuous vectors vanish. -/
private lemma tendsto_cesaro_normSq_inner_both (A : H →L[ℂ] H) [IsStarNormal A]
    (hA : IsSelfAdjoint A) {x y : H} (hx : x ∈ (purePointOperatorSubspace A)ᗮ)
    (hy : y ∈ (purePointOperatorSubspace A)ᗮ) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T,
      ‖⟪y, boundedSpectralEvolution A t x⟫_ℂ‖ ^ 2) atTop (𝓝 0) := by
  have hpol (j : Fin 4) : polVec x y j ∈ (purePointOperatorSubspace A)ᗮ := by
    fin_cases j
    · exact Submodule.add_mem _ hx hy
    · exact Submodule.sub_mem _ hx hy
    · exact Submodule.add_mem _ hx (Submodule.smul_mem _ _ hy)
    · exact Submodule.sub_mem _ hx (Submodule.smul_mem _ _ hy)
  let upper : ℝ → ℝ := fun T => ((4 : ℝ)⁻¹) * ∑ j : Fin 4, T⁻¹ *
    ∫ t in (0 : ℝ)..T, ‖⟪polVec x y j,
      boundedSpectralEvolution A t (polVec x y j)⟫_ℂ‖ ^ 2
  have hupper : Tendsto upper atTop (𝓝 0) := by
    simpa using (Tendsto.const_mul ((4 : ℝ)⁻¹) (tendsto_finsetSum Finset.univ
      fun j _ => tendsto_cesaro_normSq_inner A hA (hpol j)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with T hT
    refine mul_nonneg (inv_nonneg.mpr hT.le) ?_
    refine intervalIntegral.integral_nonneg hT.le ?_
    intro _ _
    exact sq_nonneg _
  · filter_upwards [eventually_gt_atTop 0] with T hT
    have hf : IntervalIntegrable
        (fun t : ℝ => ‖⟪y, boundedSpectralEvolution A t x⟫_ℂ‖ ^ 2) volume 0 T :=
      (continuous_normSq_inner_evolution A x y).intervalIntegrable 0 T
    have hg : IntervalIntegrable (fun t : ℝ => ((4 : ℝ)⁻¹) * ∑ j : Fin 4,
        ‖⟪polVec x y j, boundedSpectralEvolution A t (polVec x y j)⟫_ℂ‖ ^ 2) volume 0 T := by
      refine IntervalIntegrable.const_mul ?_ _
      refine IntervalIntegrable.sum Finset.univ fun j _ => ?_
      exact (continuous_normSq_inner_evolution A (polVec x y j)
        (polVec x y j)).intervalIntegrable 0 T
    have hint := intervalIntegral.integral_mono hT.le hf hg
      fun t => normSq_inner_pol_le (boundedSpectralEvolution A t) x y
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
      fun j _ => (continuous_normSq_inner_evolution A (polVec x y j)
        (polVec x y j)).intervalIntegrable 0 T] at hint
    have hTinv : 0 ≤ T⁻¹ := inv_nonneg.mpr hT.le
    calc
      T⁻¹ * ∫ t in (0 : ℝ)..T, ‖⟪y, boundedSpectralEvolution A t x⟫_ℂ‖ ^ 2
        ≤ T⁻¹ * (((4 : ℝ)⁻¹) * ∑ j : Fin 4, ∫ t in (0 : ℝ)..T,
            ‖⟪polVec x y j, boundedSpectralEvolution A t (polVec x y j)⟫_ℂ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hint hTinv
      _ = upper T := by rw [mul_left_comm, Finset.mul_sum]

/-- A continuous vector has vanishing time averages against every vector. -/
private lemma tendsto_cesaro_normSq_inner_right (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    {x : H} (hx : x ∈ (purePointOperatorSubspace A)ᗮ) (y : H) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T,
      ‖⟪y, boundedSpectralEvolution A t x⟫_ℂ‖ ^ 2) atTop (𝓝 0) := by
  have : IsStarNormal A := hA.isStarNormal
  let P := purePointOperatorSubspace A
  have hy : y - P.starProjection y ∈ Pᗮ := by
    rw [← P.starProjection_orthogonal_val]
    exact Pᗮ.starProjection_apply_mem y
  have horth (t : ℝ) : ⟪P.starProjection y, boundedSpectralEvolution A t x⟫_ℂ = 0 := by
    exact ((P.mem_orthogonal (boundedSpectralEvolution A t x)).1
      (boundedSpectralEvolution_mem_orthogonal A hA hx t)) _ (P.starProjection_apply_mem y)
  have heq (t : ℝ) : ⟪y, boundedSpectralEvolution A t x⟫_ℂ =
      ⟪y - P.starProjection y, boundedSpectralEvolution A t x⟫_ℂ := by
    rw [← add_zero ⟪y - P.starProjection y, boundedSpectralEvolution A t x⟫_ℂ, ← horth t,
      ← inner_add_left, sub_add_cancel]
  simp_rw [heq]
  exact tendsto_cesaro_normSq_inner_both A hA hx hy

/-- Squared norm of a finite-rank orthogonal projection, expanded in an orthonormal basis. -/
private lemma normSq_starProjection_eq_sum {F : Submodule ℂ H} [FiniteDimensional ℂ F]
    [CompleteSpace F] (z : H) :
    ‖F.starProjection z‖ ^ 2 =
      ∑ i, ‖⟪(stdOrthonormalBasis ℂ F i : H), z⟫_ℂ‖ ^ 2 := by
  rw [Submodule.starProjection_apply, Submodule.norm_coe,
    ← (stdOrthonormalBasis ℂ F).sum_sq_norm_inner_right (F.orthogonalProjectionOnto z)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]

/-- Orthogonal projection onto the span of a finite set is a compact operator. -/
private lemma isCompactOperator_span_starProjection {s : Set H}
    [FiniteDimensional ℂ (Submodule.span ℂ s)] [CompleteSpace (Submodule.span ℂ s)] :
    IsCompactOperator (Submodule.span ℂ s).starProjection := by
  let F := Submodule.span ℂ s
  have : LocallyCompactSpace F := LocallyCompactSpace.of_finiteDimensional_of_complete ℂ F
  exact (isCompactOperator_of_locallyCompactSpace_dom
    (F.orthogonalProjectionOnto : H →L[ℂ] F)).clm_comp F.subtypeL

/-- Compact observations of a continuous vector have vanishing time-averaged energy. -/
private lemma tendsto_cesaro_normSq_compact (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) {x : H}
    (hx : x ∈ (purePointOperatorSubspace A)ᗮ) {C : H →L[ℂ] H} (hC : IsCompactOperator C) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, ‖C (boundedSpectralEvolution A t x)‖ ^ 2)
      atTop (𝓝 0) := by
  have : IsStarNormal A := hA.isStarNormal
  refine Metric.tendsto_atTop.2 fun eps heps => ?_
  let δ : ℝ := Real.sqrt (eps / 4)
  have hδ : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  have hδsq : 2 * δ ^ 2 = eps / 2 := by
    rw [Real.sq_sqrt (by positivity)]
    ring
  let K := closure (C '' Metric.closedBall (0 : H) ‖x‖)
  have hK : IsCompact K := hC.isCompact_closure_image_closedBall ‖x‖
  obtain ⟨t, -, ht, hcover⟩ := hK.finite_cover_balls hδ
  let F := Submodule.span ℂ t
  let : FiniteDimensional ℂ F := FiniteDimensional.span_of_finite ℂ ht
  let : CompleteSpace F := FiniteDimensional.complete ℂ F
  have hdist (y : H) (hy : y ∈ K) : ‖y - F.starProjection y‖ < δ := by
    have hycover := hcover hy
    simp only [Set.mem_iUnion, Metric.mem_ball] at hycover
    obtain ⟨z, hz, hyz⟩ := hycover
    rw [← dist_eq_norm, F.dist_starProjection_eq_infDist]
    exact (Metric.infDist_le_dist_of_mem (Submodule.subset_span hz)).trans_lt hyz
  have hpoint (s : ℝ) : ‖C (boundedSpectralEvolution A s x)‖ ^ 2 ≤
      2 * ‖F.starProjection (C (boundedSpectralEvolution A s x))‖ ^ 2 + 2 * δ ^ 2 := by
    have hmem : C (boundedSpectralEvolution A s x) ∈ K :=
      subset_closure ⟨boundedSpectralEvolution A s x, by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact (norm_boundedSpectralEvolution A hA s x).le, rfl⟩
    set a : ℝ := ‖F.starProjection (C (boundedSpectralEvolution A s x))‖
    set b : ℝ := ‖C (boundedSpectralEvolution A s x) -
      F.starProjection (C (boundedSpectralEvolution A s x))‖
    have hb : b < δ := by simpa [b] using hdist _ hmem
    have hle : ‖C (boundedSpectralEvolution A s x)‖ ≤ a + b := by
      simpa [a, b, add_sub_cancel] using norm_add_le
        (F.starProjection (C (boundedSpectralEvolution A s x)))
        (C (boundedSpectralEvolution A s x) -
          F.starProjection (C (boundedSpectralEvolution A s x)))
    have hb2 : b ^ 2 ≤ δ ^ 2 := le_of_lt ((sq_lt_sq₀ (norm_nonneg _) hδ.le).2 hb)
    calc
      ‖C (boundedSpectralEvolution A s x)‖ ^ 2 ≤ (a + b) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ ≤ 2 * (a ^ 2 + b ^ 2) := add_sq_le
      _ ≤ 2 * (a ^ 2 + δ ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hb2 _) (by norm_num)
      _ = 2 * a ^ 2 + 2 * δ ^ 2 := by ring
  let b := stdOrthonormalBasis ℂ F
  have hcont (i) : Continuous fun s : ℝ =>
      ‖⟪(b i : H), C (boundedSpectralEvolution A s x)⟫_ℂ‖ ^ 2 := by
    let +nondep : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ _
    unfold boundedSpectralEvolution
    fun_prop
  have hfun : (fun T : ℝ => T⁻¹ * ∫ s in (0 : ℝ)..T,
      ‖F.starProjection (C (boundedSpectralEvolution A s x))‖ ^ 2) =
      fun T : ℝ => ∑ i, T⁻¹ * ∫ s in (0 : ℝ)..T,
        ‖⟪(b i : H), C (boundedSpectralEvolution A s x)⟫_ℂ‖ ^ 2 := by
    funext T
    simp_rw [normSq_starProjection_eq_sum]
    rw [intervalIntegral.integral_finsetSum fun i _ => (hcont i).intervalIntegrable 0 T,
      Finset.mul_sum]
  have hinner (i) : Tendsto (fun T : ℝ => T⁻¹ * ∫ s in (0 : ℝ)..T,
      ‖⟪(b i : H), C (boundedSpectralEvolution A s x)⟫_ℂ‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [← C.adjoint_inner_left (boundedSpectralEvolution A _ x) (b i)]
    exact tendsto_cesaro_normSq_inner_right A hA hx (C.adjoint (b i : H))
  have hQ : Tendsto (fun T : ℝ => T⁻¹ * ∫ s in (0 : ℝ)..T,
      ‖F.starProjection (C (boundedSpectralEvolution A s x))‖ ^ 2) atTop (𝓝 0) := by
    rw [hfun]
    simpa using tendsto_finsetSum Finset.univ fun i _ => hinner i
  obtain ⟨T0, hT0⟩ := Metric.tendsto_atTop.1 hQ (eps / 4) (by positivity)
  refine ⟨max T0 1, fun T hT => ?_⟩
  have hT0le : T0 ≤ T := (max_le_iff.mp hT).1
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one (max_le_iff.mp hT).2
  have hnnQ : 0 ≤ T⁻¹ * ∫ s in (0 : ℝ)..T,
      ‖F.starProjection (C (boundedSpectralEvolution A s x))‖ ^ 2 := by
    refine mul_nonneg (inv_nonneg.mpr hTpos.le) ?_
    refine intervalIntegral.integral_nonneg hTpos.le ?_
    intro _ _
    exact sq_nonneg _
  have hQlt : T⁻¹ * ∫ s in (0 : ℝ)..T,
      ‖F.starProjection (C (boundedSpectralEvolution A s x))‖ ^ 2 < eps / 4 := by
    have hdistQ := hT0 T hT0le
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hnnQ] at hdistQ
    exact hdistQ
  have hf : IntervalIntegrable
      (fun s : ℝ => ‖C (boundedSpectralEvolution A s x)‖ ^ 2) volume 0 T :=
    (by
      let +nondep : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ _
      unfold boundedSpectralEvolution
      fun_prop : Continuous fun s : ℝ => ‖C (boundedSpectralEvolution A s x)‖ ^ 2).intervalIntegrable
        0 T
  have hg : IntervalIntegrable (fun s : ℝ =>
      2 * ‖F.starProjection (C (boundedSpectralEvolution A s x))‖ ^ 2 + 2 * δ ^ 2) volume 0 T := by
    refine IntervalIntegrable.add ?_ (continuous_const.intervalIntegrable 0 T)
    refine IntervalIntegrable.const_mul ?_ _
    refine Continuous.intervalIntegrable ?_ 0 T
    let +nondep : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ _
    unfold boundedSpectralEvolution
    fun_prop
  have hint := intervalIntegral.integral_mono hT.le hf hg hpoint
  rw [intervalIntegral.integral_add
      ((IntervalIntegrable.const_mul (by
        refine Continuous.intervalIntegrable ?_ 0 T
        let +nondep : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ _
        unfold boundedSpectralEvolution
        fun_prop) _) 0 T)
      (continuous_const.intervalIntegrable 0 T),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, sub_zero,
    smul_eq_mul] at hint
  have hTinv : 0 ≤ T⁻¹ := inv_nonneg.mpr hTpos.le
  have havg : T⁻¹ * ∫ s in (0 : ℝ)..T, ‖C (boundedSpectralEvolution A s x)‖ ^ 2 ≤
      2 * (T⁻¹ * ∫ s in (0 : ℝ)..T,
        ‖F.starProjection (C (boundedSpectralEvolution A s x))‖ ^ 2) + 2 * δ ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hint hTinv
    simpa [mul_add, mul_left_comm, mul_assoc, hTpos.ne'] using hmul
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg
    (le_trans (by positivity) havg)]
  calc
    T⁻¹ * ∫ s in (0 : ℝ)..T, ‖C (boundedSpectralEvolution A s x)‖ ^ 2
      ≤ 2 * (T⁻¹ * ∫ s in (0 : ℝ)..T,
          ‖F.starProjection (C (boundedSpectralEvolution A s x))‖ ^ 2) + 2 * δ ^ 2 := havg
    _ < 2 * (eps / 4) + eps / 2 := by
      rw [hδsq]
      gcongr
    _ = eps := by ring

/-- Vectors whose full unitary orbit is relatively compact. -/
private def precompactOrbitSubmodule (A : H →L[ℂ] H) : Submodule ℂ H where
  carrier := {y | IsCompact (closure (Set.range (fun t : ℝ => boundedSpectralEvolution A t y)))}
  zero_mem' := by
    have hsub : Set.range (fun t : ℝ => boundedSpectralEvolution A t (0 : H)) ⊆ {(0 : H)} := by
      intro w hw
      obtain ⟨t, rfl⟩ := hw
      simp
    exact IsCompact.of_isClosed_subset isCompact_singleton isClosed_closure
      (closure_minimal hsub isClosed_singleton)
  add_mem' := by
    intro y z hy hz
    have hsub : Set.range (fun t : ℝ => boundedSpectralEvolution A t (y + z)) ⊆
        closure (Set.range (fun t : ℝ => boundedSpectralEvolution A t y)) +
          closure (Set.range (fun t : ℝ => boundedSpectralEvolution A t z)) := by
      intro w hw
      obtain ⟨t, rfl⟩ := hw
      change boundedSpectralEvolution A t (y + z) ∈ _
      rw [map_add, Set.mem_add]
      exact ⟨boundedSpectralEvolution A t y, subset_closure ⟨t, rfl⟩,
        boundedSpectralEvolution A t z, subset_closure ⟨t, rfl⟩, rfl⟩
    have hsum : IsCompact (closure (Set.range (fun t : ℝ => boundedSpectralEvolution A t y)) +
        closure (Set.range (fun t : ℝ => boundedSpectralEvolution A t z))) := by
      rw [← Set.add_image_prod]
      exact (IsCompact.prod hy hz).image (Continuous.add continuous_fst continuous_snd)
    exact IsCompact.of_isClosed_subset hsum isClosed_closure (closure_minimal hsub hsum.isClosed)
  smul_mem' := by
    intro c y hy
    have hsub : Set.range (fun t : ℝ => boundedSpectralEvolution A t (c • y)) ⊆
        c • closure (Set.range (fun t : ℝ => boundedSpectralEvolution A t y)) := by
      intro w hw
      obtain ⟨t, rfl⟩ := hw
      change boundedSpectralEvolution A t (c • y) ∈ _
      rw [map_smul, Set.mem_smul_set]
      exact ⟨boundedSpectralEvolution A t y, subset_closure ⟨t, rfl⟩, rfl⟩
    exact IsCompact.of_isClosed_subset (IsCompact.smul c hy) isClosed_closure
      (closure_minimal hsub (IsCompact.smul c hy).isClosed)

/-- An eigenvector has relatively compact unitary orbit. -/
private lemma precompactOrbit_eigenvector (A : H →L[ℂ] H) {v : H} {a : ℝ}
    (hv : A v = (a : ℂ) • v) :
    IsCompact (closure (Set.range (fun t : ℝ => boundedSpectralEvolution A t v))) := by
  have hsub : Set.range (fun t : ℝ => boundedSpectralEvolution A t v) ⊆
      (fun z : ℂ => z • v) '' Metric.sphere (0 : ℂ) 1 := by
    intro w hw
    obtain ⟨t, rfl⟩ := hw
    refine ⟨evolutionPhase t a, ?_, ?_⟩
    · rw [Metric.mem_sphere, dist_zero_right]
      exact norm_evolutionPhase_of_im_eq_zero t (Complex.ofReal_im a)
    · simpa [evolutionPhase] using (boundedSpectralEvolution_apply_eigenvector A hv t).symm
  have himg : IsCompact ((fun z : ℂ => z • v) '' Metric.sphere (0 : ℂ) 1) :=
    (isCompact_sphere (0 : ℂ) 1).image (by fun_prop)
  exact IsCompact.of_isClosed_subset himg isClosed_closure (closure_minimal hsub himg.isClosed)

/-- The pure-point subspace consists of relatively compact orbits. -/
private lemma purePoint_le_precompactOrbit (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    purePointOperatorSubspace A ≤ precompactOrbitSubmodule A := by
  refine Submodule.topologicalClosure_minimal _ ?_ ?_
  · rw [Submodule.span_le]
    intro v hv
    obtain ⟨a, ha⟩ := hv
    exact precompactOrbit_eigenvector A ha
  · refine IsSeqClosed.isClosed ?_
    intro u x hu hx
    change IsCompact (closure (Set.range (fun t : ℝ => boundedSpectralEvolution A t x)))
    rw [isCompact_iff_totallyBounded_isComplete]
    refine ⟨TotallyBounded.closure ?_, isClosed_closure.isComplete⟩
    rw [Metric.totallyBounded_iff]
    intro eps heps
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hx (eps / 2) (by positivity)
    have hrange : TotallyBounded
        (Set.range (fun t : ℝ => boundedSpectralEvolution A t (u N))) :=
      TotallyBounded.subset subset_closure (isCompact_iff_totallyBounded_isComplete.1 (hu N)).1
    obtain ⟨t, ht, hcover⟩ := (Metric.totallyBounded_iff.1 hrange) (eps / 2) (by positivity)
    refine ⟨t, ht, ?_⟩
    intro z hz
    obtain ⟨s, rfl⟩ := hz
    have hnear : dist (boundedSpectralEvolution A s x)
        (boundedSpectralEvolution A s (u N)) < eps / 2 := by
      rw [dist_eq_norm, ← map_sub, norm_boundedSpectralEvolution A hA, ← dist_eq_norm, dist_comm]
      exact hN N le_rfl
    have hball := hcover ⟨s, rfl⟩
    simp only [Set.mem_iUnion, Metric.mem_ball] at hball
    obtain ⟨y, hy, hyd⟩ := hball
    refine Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨hy, ?_⟩⟩
    rw [Metric.mem_ball]
    exact (dist_triangle _ _ _).trans_lt (by linarith)

/-- **22.63**, RAGE for a bounded self-adjoint generator: continuous vectors are exactly
those whose compactly observed time-averaged energy escapes. -/
theorem rage_continuous (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x : H) :
    x ∈ (purePointOperatorSubspace A).orthogonal ↔
      ∀ C : H →L[ℂ] H, IsCompactOperator C → Tendsto
        (fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T, ‖C (boundedSpectralEvolution A t x)‖ ^ 2)
        atTop (𝓝 0) := by
  constructor
  · intro hx C hC
    exact tendsto_cesaro_normSq_compact A hA hx hC
  · intro havg
    by_contra hx
    let s : Set H := {w | ∃ a : ℝ, A w = (a : ℂ) • w}
    have hx' : x ∉ (Submodule.span ℂ s)ᗮ := by
      rwa [purePointOperatorSubspace, Submodule.orthogonal_closure] at hx
    rw [Submodule.mem_orthogonal] at hx'
    push Not at hx'
    obtain ⟨u, hu, hu0⟩ := hx'
    obtain ⟨l, hl⟩ := (Finsupp.mem_span_iff_linearCombination ℂ s u).1 hu
    have hsum : ⟪(Finsupp.linearCombination ℂ (Subtype.val : s → H)) l, x⟫_ℂ ≠ 0 := by
      simpa [hl] using hu0
    rw [Finsupp.linearCombination_apply, Finsupp.sum_inner] at hsum
    have hv : ∃ v : s, ⟪(v : H), x⟫_ℂ ≠ 0 := by
      by_contra hnone
      push Not at hnone
      apply hsum
      rw [Finsupp.sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [inner_smul_left, hnone i, mul_zero]
    obtain ⟨v, hv⟩ := hv
    obtain ⟨a, ha⟩ := v.property
    have hv0 : (v : H) ≠ 0 := by
      intro h0
      apply hv
      simp [h0]
    let uN : H := (‖(v : H)‖⁻¹ : ℂ) • (v : H)
    have hu_norm : ‖uN‖ = 1 := by
      rw [norm_smul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (norm_nonneg _)]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)
    have hu_eig : A uN = (a : ℂ) • uN := by
      unfold uN
      rw [map_smul, ha, smul_smul, mul_comm, ← smul_smul]
    have hu_inner : ⟪uN, x⟫_ℂ ≠ 0 := by
      rw [inner_smul_left, starRingEnd_apply, Complex.star_def, Complex.conj_inv,
        Complex.conj_ofReal]
      exact mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr
        (norm_ne_zero_iff.mpr hv0))) hv
    let C : H →L[ℂ] H :=
      (ContinuousLinearMap.toSpanSingleton ℂ uN).comp (innerSL ℂ uN)
    have hC : IsCompactOperator C := by
      have hdom : IsCompactOperator (innerSL ℂ uN : H →L[ℂ] ℂ) :=
        isCompactOperator_of_locallyCompactSpace_dom _
      simpa [C, ContinuousLinearMap.coe_comp] using
        hdom.clm_comp (ContinuousLinearMap.toSpanSingleton ℂ uN)
    have hnorm (t : ℝ) : ‖C (boundedSpectralEvolution A t x)‖ = ‖⟪uN, x⟫_ℂ‖ := by
      have happly : C (boundedSpectralEvolution A t x) =
          ⟪uN, boundedSpectralEvolution A t x⟫_ℂ • uN := by
        simp [C, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
          ContinuousLinearMap.toSpanSingleton_apply]
      rw [happly, norm_smul, hu_norm, mul_one, inner_boundedSpectralEvolution A hA t]
      have hphase := boundedSpectralEvolution_apply_eigenvector A hu_eig (-t)
      rw [hphase, inner_smul_left, starRingEnd_apply, Complex.star_def, norm_mul,
        Complex.norm_conj]
      have hphase1 : ‖Complex.exp ((-↑(-t) * Complex.I) * (a : ℂ))‖ = 1 := by
        simpa [evolutionPhase] using
          norm_evolutionPhase_of_im_eq_zero (-t) (Complex.ofReal_im a)
      rw [hphase1, one_mul]
    have hlim : Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T,
        ‖C (boundedSpectralEvolution A t x)‖ ^ 2) atTop (𝓝 (‖⟪uN, x⟫_ℂ‖ ^ 2)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with T hT
      simp_rw [hnorm, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hT.ne', one_mul]
    have hzero := tendsto_nhds_unique (havg C hC) hlim
    exact (pow_ne_zero 2 (norm_ne_zero_iff.mpr hu_inner)).symm hzero

/-- The pure-point RAGE criterion uses relative compactness of the full unitary orbit. -/
theorem rage_purePoint (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x : H) :
    x ∈ purePointOperatorSubspace A ↔
      IsCompact (closure (Set.range (fun t : ℝ ↦ boundedSpectralEvolution A t x))) := by
  constructor
  · intro hx
    exact purePoint_le_precompactOrbit A hA hx
  · intro hcomp
    let P := purePointOperatorSubspace A
    let y : H := x - P.starProjection x
    have hy : y ∈ Pᗮ := by
      unfold y
      rw [← P.starProjection_orthogonal_val]
      exact Pᗮ.starProjection_apply_mem x
    have horb : IsCompact (closure (Set.range
        (fun t : ℝ => boundedSpectralEvolution A t y))) := by
      have hcont : Continuous fun z : H => z - P.starProjection z := by fun_prop
      have hsub : Set.range (fun t : ℝ => boundedSpectralEvolution A t y) ⊆
          (fun z : H => z - P.starProjection z) ''
            closure (Set.range (fun t : ℝ => boundedSpectralEvolution A t x)) := by
        intro w hw
        obtain ⟨t, rfl⟩ := hw
        refine ⟨boundedSpectralEvolution A t x, subset_closure ⟨t, rfl⟩, ?_⟩
        change boundedSpectralEvolution A t x -
          P.starProjection (boundedSpectralEvolution A t x) =
            boundedSpectralEvolution A t y
        unfold y
        rw [map_sub, boundedSpectralEvolution_starProjection A hA t x]
      have himg : IsCompact ((fun z : H => z - P.starProjection z) ''
          closure (Set.range (fun t : ℝ => boundedSpectralEvolution A t x))) :=
        hcomp.image hcont
      exact IsCompact.of_isClosed_subset himg isClosed_closure
        (closure_minimal hsub himg.isClosed)
    have hy0 : y = 0 := by
      refine norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm ?_ (sq_nonneg _)))
      refine le_of_forall_pos_le_add fun eps heps => ?_
      let δ : ℝ := Real.sqrt (eps / 2)
      have hδ : 0 < δ := Real.sqrt_pos.mpr (by positivity)
      have hδsq : 2 * δ ^ 2 = eps := by
        rw [Real.sq_sqrt (by positivity)]
        ring
      obtain ⟨t, -, ht, hcover⟩ := horb.finite_cover_balls hδ
      let F := Submodule.span ℂ t
      let : FiniteDimensional ℂ F := FiniteDimensional.span_of_finite ℂ ht
      let : CompleteSpace F := FiniteDimensional.complete ℂ F
      have hdist (z : H) (hz : z ∈ closure (Set.range
          (fun s : ℝ => boundedSpectralEvolution A s y))) :
          ‖z - F.starProjection z‖ < δ := by
        have hzcover := hcover hz
        simp only [Set.mem_iUnion, Metric.mem_ball] at hzcover
        obtain ⟨w, hw, hzw⟩ := hzcover
        rw [← dist_eq_norm, F.dist_starProjection_eq_infDist]
        exact (Metric.infDist_le_dist_of_mem (Submodule.subset_span hw)).trans_lt hzw
      have hpoint (s : ℝ) : ‖boundedSpectralEvolution A s y‖ ^ 2 ≤
          2 * ‖F.starProjection (boundedSpectralEvolution A s y)‖ ^ 2 + 2 * δ ^ 2 := by
        have hmem : boundedSpectralEvolution A s y ∈ closure (Set.range
            (fun r : ℝ => boundedSpectralEvolution A r y)) :=
          subset_closure ⟨s, rfl⟩
        set aN : ℝ := ‖F.starProjection (boundedSpectralEvolution A s y)‖
        set bN : ℝ := ‖boundedSpectralEvolution A s y -
          F.starProjection (boundedSpectralEvolution A s y)‖
        have hb : bN < δ := by simpa [bN] using hdist _ hmem
        have hle : ‖boundedSpectralEvolution A s y‖ ≤ aN + bN := by
          simpa [aN, bN, add_sub_cancel] using norm_add_le
            (F.starProjection (boundedSpectralEvolution A s y))
            (boundedSpectralEvolution A s y -
              F.starProjection (boundedSpectralEvolution A s y))
        have hb2 : bN ^ 2 ≤ δ ^ 2 :=
          le_of_lt ((sq_lt_sq₀ (norm_nonneg _) hδ.le).2 hb)
        calc
          ‖boundedSpectralEvolution A s y‖ ^ 2 ≤ (aN + bN) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hle 2
          _ ≤ 2 * (aN ^ 2 + bN ^ 2) := add_sq_le
          _ ≤ 2 * (aN ^ 2 + δ ^ 2) :=
            mul_le_mul_of_nonneg_left (add_le_add_right hb2 _) (by norm_num)
          _ = 2 * aN ^ 2 + 2 * δ ^ 2 := by ring
      have hQ : Tendsto (fun T : ℝ => T⁻¹ * ∫ s in (0 : ℝ)..T,
          ‖F.starProjection (boundedSpectralEvolution A s y)‖ ^ 2) atTop (𝓝 0) :=
        tendsto_cesaro_normSq_compact A hA hy
          (isCompactOperator_span_starProjection (s := t))
      have hbound : Tendsto (fun T : ℝ => 2 * (T⁻¹ * ∫ s in (0 : ℝ)..T,
          ‖F.starProjection (boundedSpectralEvolution A s y)‖ ^ 2) + 2 * δ ^ 2)
          atTop (𝓝 eps) := by
        have : Tendsto (fun T : ℝ => 2 * (T⁻¹ * ∫ s in (0 : ℝ)..T,
            ‖F.starProjection (boundedSpectralEvolution A s y)‖ ^ 2) + 2 * δ ^ 2)
            atTop (𝓝 (2 * 0 + 2 * δ ^ 2)) :=
          (hQ.const_mul 2).add tendsto_const_nhds
        simpa [hδsq] using this
      have hle : ∀ᶠ T in atTop, ‖y‖ ^ 2 ≤ 2 * (T⁻¹ * ∫ s in (0 : ℝ)..T,
          ‖F.starProjection (boundedSpectralEvolution A s y)‖ ^ 2) + 2 * δ ^ 2 := by
        filter_upwards [eventually_gt_atTop 0] with T hT
        have hconst : T⁻¹ * ∫ s in (0 : ℝ)..T, ‖boundedSpectralEvolution A s y‖ ^ 2 =
            ‖y‖ ^ 2 := by
          simp_rw [norm_boundedSpectralEvolution A hA]
          rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, ← mul_assoc,
            inv_mul_cancel₀ hT.ne', one_mul]
        rw [← hconst]
        have hf : IntervalIntegrable
            (fun s : ℝ => ‖boundedSpectralEvolution A s y‖ ^ 2) volume 0 T := by
          simp_rw [norm_boundedSpectralEvolution A hA]
          exact continuous_const.intervalIntegrable 0 T
        have hg : IntervalIntegrable (fun s : ℝ =>
            2 * ‖F.starProjection (boundedSpectralEvolution A s y)‖ ^ 2 + 2 * δ ^ 2)
            volume 0 T := by
          refine IntervalIntegrable.add (IntervalIntegrable.const_mul ?_ _)
            (continuous_const.intervalIntegrable 0 T)
          refine Continuous.intervalIntegrable ?_ 0 T
          let +nondep : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ _
          unfold boundedSpectralEvolution
          fun_prop
        have hint := intervalIntegral.integral_mono hT.le hf hg hpoint
        rw [intervalIntegral.integral_add (IntervalIntegrable.const_mul (by
          refine Continuous.intervalIntegrable ?_ 0 T
          let +nondep : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ _
          unfold boundedSpectralEvolution
          fun_prop) _) (continuous_const.intervalIntegrable 0 T),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const, sub_zero,
          smul_eq_mul] at hint
        have hmul := mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hT.le)
        simpa [mul_add, mul_left_comm, mul_assoc, hT.ne'] using hmul
      simpa using ge_of_tendsto hbound hle
    have hxmem : x = P.starProjection x := by
      rw [← sub_eq_zero]
      exact hy0
    rw [hxmem]
    exact P.starProjection_apply_mem x

end CKMA
