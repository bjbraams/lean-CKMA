/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import CKMA.Analysis.Operator.Fredholm
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Analytic Fredholm families and simple eigenvalue branches

For a holomorphic compact-operator family invertible at one point of a connected domain,
exceptional parameters are discrete and the inverse is analytic elsewhere. Genuine inverse
poles have positive order, a nonzero analytic regularization at the base point, and invertibility
on a punctured neighborhood. At-most-pole regularizations are kept as a separate weaker notion.

An algebraically simple eigenpair is expressed by a rank-one projection and a two-sided reduced
resolvent identity. Its analytic continuation supplies an eigenvalue and a nonzero eigenvector
branch. Sources: GAPS 21.15 and 22.34; finite-rank principal parts are outside the displayed pole
  clause.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Filter Topology ContinuousLinearMap Metric

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The noninvertibility set of a compact Fredholm family inside its parameter domain. -/
def fredholmExceptionalSet (K : ℂ → X →L[ℂ] X) (U : Set ℂ) : Set ℂ :=
  {z ∈ U | ¬ IsUnit (1 - K z)}

/-- A finite-order analytic regularization of the totalized inverse. Order zero is allowed,
so this weaker condition also includes removable singularities and regular points. -/
def HasFiniteOrderInverseRegularization (K : ℂ → X →L[ℂ] X) (a : ℂ) : Prop :=
  ∃ m : ℕ, ∃ F : ℂ → X →L[ℂ] X, AnalyticAt ℂ F a ∧
    ∀ᶠ z in 𝓝[≠] a, (z - a) ^ m • Ring.inverse (1 - K z) = F z

/-- A genuine inverse pole: the family is invertible on a punctured neighborhood and a
positive-order regularization is analytic with nonzero value at the base point. -/
def HasOperatorInversePole (K : ℂ → X →L[ℂ] X) (a : ℂ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ F : ℂ → X →L[ℂ] X, AnalyticAt ℂ F a ∧ F a ≠ 0 ∧
    (∀ᶠ z in 𝓝[≠] a, IsUnit (1 - K z)) ∧
    ∀ᶠ z in 𝓝[≠] a, (z - a) ^ m • Ring.inverse (1 - K z) = F z

omit [CompleteSpace X] in
/-- Every genuine inverse pole has a finite-order analytic regularization. -/
theorem HasOperatorInversePole.hasFiniteOrderInverseRegularization
    {K : ℂ → X →L[ℂ] X} {a : ℂ} (h : HasOperatorInversePole K a) :
    HasFiniteOrderInverseRegularization K a := by
  obtain ⟨m, _, F, hF, _, _, heq⟩ := h
  exact ⟨m, F, hF, heq⟩

/-- **21.15**: if the family is invertible at one point, exceptional points are discrete,
the inverse is analytic off them, and every exceptional point has a finite-order pole. -/
theorem analytic_fredholm {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (K : ℂ → X →L[ℂ] X) (hK : DifferentiableOn ℂ K U)
    (hc : ∀ z ∈ U, IsCompactOperator (K z))
    (hunit : ∃ z ∈ U, IsUnit (1 - K z)) :
    (∀ a ∈ fredholmExceptionalSet K U, ∃ r : ℝ, 0 < r ∧
      ∀ z ∈ fredholmExceptionalSet K U, dist z a < r → z = a) ∧
    DifferentiableOn ℂ (fun z ↦ Ring.inverse (1 - K z)) (U \ fredholmExceptionalSet K U) ∧
    ∀ a ∈ fredholmExceptionalSet K U, HasOperatorInversePole K a := by
  sorry

/-- Partial derivative in `(z, u)` of `(φ u - 1, A u - z • u)`. -/
private def simpleEigenPartial (A0 : X →L[ℂ] X) (z₀ : ℂ) (u₀ : X) (phi : X →L[ℂ] ℂ) :
    (ℂ × X) →L[ℂ] ℂ × X :=
  (phi.comp (snd ℂ ℂ X)).prod
    (((A0 - z₀ • (1 : X →L[ℂ] X)).comp (snd ℂ ℂ X)) - (fst ℂ ℂ X).smulRight u₀)

/-- Reduced-resolvent inverse of `simpleEigenPartial` at a simple eigenpair. -/
private def simpleEigenPartialInv (u₀ : X) (phi : X →L[ℂ] ℂ) (R : X →L[ℂ] X) :
    (ℂ × X) →L[ℂ] ℂ × X :=
  let P := phi.smulRight u₀
  let Q := (1 : X →L[ℂ] X) - P
  let coeff := fst ℂ ℂ X - phi.comp ((R.comp Q).comp (snd ℂ ℂ X))
  ( (-phi.comp (snd ℂ ℂ X)).prod
      (coeff.smulRight u₀ + (R.comp Q).comp (snd ℂ ℂ X)) )

omit [CompleteSpace X] in
/-- The eigenfunctional annihilates the residual operator of a simple eigenpair. -/
private theorem phi_residual_eq_zero (A0 : X →L[ℂ] X) (z₀ : ℂ) (u₀ : X) (phi : X →L[ℂ] ℂ)
    (R : X →L[ℂ] X) (hphi : phi u₀ = 1) (hAu : A0 u₀ = z₀ • u₀)
    (hLeft : (A0 - z₀ • (1 : X →L[ℂ] X)) * R = 1 - phi.smulRight u₀)
    (hRight : R * (A0 - z₀ • (1 : X →L[ℂ] X)) = 1 - phi.smulRight u₀) :
    phi.comp (A0 - z₀ • (1 : X →L[ℂ] X)) = 0 := by
  let B : X →L[ℂ] X := A0 - z₀ • (1 : X →L[ℂ] X)
  let P : X →L[ℂ] X := phi.smulRight u₀
  have hBu : B u₀ = 0 := by
    simp [B, hAu]
  have hBP : B * P = 0 := by
    ext x
    simp [mul_def, P, hBu, map_smul]
  have hsum : P + (1 - P) = 1 := by
    rw [sub_eq_add_neg, ← add_assoc, add_comm P 1, add_assoc, add_neg_cancel, add_zero]
  have hB : B = (1 - P) * B := by
    calc B
        = B * 1 := by rw [mul_one]
      _ = B * (P + (1 - P)) := by rw [hsum]
      _ = B * P + B * (1 - P) := by rw [mul_add]
      _ = B * (1 - P) := by rw [hBP, zero_add]
      _ = B * (R * B) := by rw [hRight]
      _ = (B * R) * B := by rw [mul_assoc]
      _ = (1 - P) * B := by rw [hLeft]
  have hPB : P * B = 0 := by
    calc P * B
        = (1 - (1 - P)) * B := by
          exact congrArg (fun T : X →L[ℂ] X => T * B) (sub_sub_cancel _ P).symm
      _ = 1 * B - (1 - P) * B := by rw [sub_mul]
      _ = B - B := by rw [one_mul, ← hB]
      _ = 0 := sub_self _
  ext x
  have hsmul : phi (B x) • u₀ = 0 := by
    simpa [mul_def, P] using congr_fun (congrArg DFunLike.coe hPB) x
  have hu : u₀ ≠ 0 := by
    intro hu0
    have : phi u₀ = 0 := by simp [hu0]
    exact one_ne_zero (hphi.symm.trans this)
  exact (smul_eq_zero.mp hsmul).resolve_right hu

omit [CompleteSpace X] in
/-- At a simple eigenpair the eigenvalue-eigenvector partial is a Banach automorphism. -/
private theorem simpleEigenPartial_isInvertible (A0 : X →L[ℂ] X) (z₀ : ℂ) (u₀ : X)
    (phi : X →L[ℂ] ℂ) (R : X →L[ℂ] X) (hphi : phi u₀ = 1) (hAu : A0 u₀ = z₀ • u₀)
    (hLeft : (A0 - z₀ • (1 : X →L[ℂ] X)) * R = 1 - phi.smulRight u₀)
    (hRight : R * (A0 - z₀ • (1 : X →L[ℂ] X)) = 1 - phi.smulRight u₀) :
    (simpleEigenPartial A0 z₀ u₀ phi).IsInvertible := by
  let B : X →L[ℂ] X := A0 - z₀ • (1 : X →L[ℂ] X)
  let P : X →L[ℂ] X := phi.smulRight u₀
  let Q : X →L[ℂ] X := 1 - P
  have hphiB : phi.comp B = 0 := phi_residual_eq_zero A0 z₀ u₀ phi R hphi hAu hLeft hRight
  have hBu : B u₀ = 0 := by simp [B, hAu]
  have hQu : Q u₀ = 0 := by simp [Q, P, hphi]
  have hPP : P * P = P := by
    ext x
    simp [mul_def, P, map_smul, hphi]
  have hB : B = Q * B := by
    have hBP : B * P = 0 := by
      ext x
      simp [mul_def, P, hBu, map_smul]
    calc B
        = B * 1 := by rw [mul_one]
      _ = B * (P + Q) := by simp [Q]
      _ = B * P + B * Q := by rw [mul_add]
      _ = B * Q := by rw [hBP, zero_add]
      _ = B * (R * B) := by rw [hRight]
      _ = (B * R) * B := by rw [mul_assoc]
      _ = Q * B := by rw [hLeft]
  have hQB : Q * B = B := hB.symm
  have hQQ : Q * Q = Q := by
    calc Q * Q
        = (1 - P) * (1 - P) := rfl
      _ = 1 * (1 - P) - P * (1 - P) := by rw [sub_mul]
      _ = (1 - P) - P * (1 - P) := by rw [one_mul]
      _ = (1 - P) - (P * 1 - P * P) := by rw [mul_sub]
      _ = (1 - P) - (P - P) := by rw [mul_one, hPP]
      _ = Q := by rw [sub_self, sub_zero]
  have happL (w : ℂ) (x : X) :
      simpleEigenPartial A0 z₀ u₀ phi (w, x) = (phi x, B x - w • u₀) := by
    simp [simpleEigenPartial, B, prod_apply, comp_apply, smulRight_apply, coe_fst', coe_snd']
  have happS (alpha : ℂ) (y : X) :
      simpleEigenPartialInv u₀ phi R (alpha, y) =
        (-phi y, (alpha - phi (R (Q y))) • u₀ + R (Q y)) := by
    simp [simpleEigenPartialInv, Q, P, prod_apply, comp_apply, smulRight_apply, coe_fst',
      coe_snd', map_sub]
  have hLS : simpleEigenPartial A0 z₀ u₀ phi ∘L simpleEigenPartialInv u₀ phi R =
      .id ℂ (ℂ × X) := by
    refine ext fun v => ?_
    obtain ⟨alpha, y⟩ := v
    have hphiS : phi ((alpha - phi (R (Q y))) • u₀ + R (Q y)) = alpha := by
      rw [map_add, map_smul, hphi, smul_eq_mul, mul_one, sub_add_cancel]
    have hBS : B ((alpha - phi (R (Q y))) • u₀ + R (Q y)) - (-phi y) • u₀ = y := by
      rw [map_add, map_smul, hBu, smul_zero, zero_add, neg_smul, sub_neg_eq_add]
      have hBR : B (R (Q y)) = Q y := by
        show (B * R) (Q y) = Q y
        rw [hLeft]
        exact congr_fun (congrArg DFunLike.coe hQQ) y
      rw [hBR]
      simp [Q, P]
    refine Prod.ext ?_ ?_
    · simpa [comp_apply, happL, happS] using hphiS
    · simpa [comp_apply, id_apply, happL, happS] using hBS
  have hSL : simpleEigenPartialInv u₀ phi R ∘L simpleEigenPartial A0 z₀ u₀ phi =
      .id ℂ (ℂ × X) := by
    refine ext fun v => ?_
    obtain ⟨w, x⟩ := v
    have hy : Q (B x - w • u₀) = B x := by
      rw [map_sub, map_smul, hQu, smul_zero, sub_zero]
      simpa [mul_def] using congr_fun (congrArg DFunLike.coe hQB) x
    have hphiR : phi (R (Q (B x - w • u₀))) = 0 := by
      rw [hy]
      have hRB : R (B x) = Q x := by
        show (R * B) x = Q x
        rw [hRight]
      rw [hRB]
      simp [Q, P, hphi]
    have hw : -phi (B x - w • u₀) = w := by
      have hBx : phi (B x) = 0 := by
        simpa [comp_apply] using congr_fun (congrArg DFunLike.coe hphiB) x
      rw [map_sub, map_smul, hphi, hBx, zero_sub, neg_neg, smul_eq_mul, mul_one]
    have hx : (phi x - phi (R (Q (B x - w • u₀)))) • u₀ + R (Q (B x - w • u₀)) = x := by
      rw [hphiR, sub_zero, hy]
      have hRB : R (B x) = Q x := by
        show (R * B) x = Q x
        rw [hRight]
      rw [hRB]
      simp [Q, P]
    refine Prod.ext ?_ ?_
    · simpa [comp_apply, happL, happS] using hw
    · simpa [comp_apply, id_apply, happL, happS] using hx
  exact IsInvertible.of_inverse hLS hSL

/-- Algebraic simplicity in a concrete reduced-resolvent form.
Geometric multiplicity one alone is insufficient: a Jordan block would permit branching. -/
def IsSimpleSpectralEigenpair (A : X →L[ℂ] X) (z : ℂ) (u : X) : Prop :=
  ∃ φ : X →L[ℂ] ℂ, φ u = 1 ∧ A u = z • u ∧ ∃ R : X →L[ℂ] X,
    (A - z • (1 : X →L[ℂ] X)) * R = 1 - φ.smulRight u ∧
    R * (A - z • (1 : X →L[ℂ] X)) = 1 - φ.smulRight u

/-- **22.34**, the bounded type-(A) simple-eigenvalue clause: an actual analytic eigenvector
and eigenvalue branch through the specified algebraically simple eigenpair. -/
theorem analytic_simple_eigenpair (A : ℂ → X →L[ℂ] X) (hA : AnalyticAt ℂ A 0)
    {z₀ : ℂ} {u₀ : X} (hpair : IsSimpleSpectralEigenpair (A 0) z₀ u₀) :
    ∃ r : ℝ, 0 < r ∧ ∃ z : ℂ → ℂ, ∃ u : ℂ → X,
      DifferentiableOn ℂ z (Metric.ball 0 r) ∧ DifferentiableOn ℂ u (Metric.ball 0 r) ∧
      z 0 = z₀ ∧ u 0 = u₀ ∧
      ∀ t ∈ Metric.ball 0 r, u t ≠ 0 ∧ A t (u t) = z t • u t := by
  obtain ⟨phi, hphi, hAu, R, hLeft, hRight⟩ := hpair
  let eigen (p : ℂ × ℂ × X) : ℂ × X :=
    (phi p.2.2 - 1, (A p.1) p.2.2 - p.2.1 • p.2.2)
  let base : ℂ × ℂ × X := (0, (z₀, u₀))
  have hzero : eigen base = 0 := by
    simp [eigen, base, hphi, hAu]
  have hone : (1 : WithTop ℕ∞) ≠ 0 := by decide
  have hA1 : ContDiffAt ℂ 1 A 0 := hA.contDiffAt
  have hcd : ContDiffAt ℂ 1 eigen base := by
    have ht : ContDiffAt ℂ 1 (fun p : ℂ × ℂ × X => p.1) base := contDiffAt_fst
    have hu : ContDiffAt ℂ 1 (fun p : ℂ × ℂ × X => p.2.2) base :=
      contDiffAt_snd.comp base contDiffAt_snd
    have hz : ContDiffAt ℂ 1 (fun p : ℂ × ℂ × X => p.2.1) base :=
      contDiffAt_fst.comp base contDiffAt_snd
    have happ := (hA1.comp base ht).clm_apply hu
    have hsmul := hz.smul hu
    have hphiC : ContDiffAt ℂ 1 (fun p : ℂ × ℂ × X => phi p.2.2 - 1) base :=
      (phi.contDiff.contDiffAt.comp base hu).sub (contDiffAt_const (c := (1 : ℂ)))
    simpa [eigen] using hphiC.prodMk (happ.sub hsmul)
  have hinv : (fderiv ℂ eigen base ∘L inr ℂ ℂ (ℂ × X)).IsInvertible := by
    let point : ℂ × X := (z₀, u₀)
    have hphiF : fderiv ℂ (fun y : ℂ × X => phi (y.2) - 1) point = phi.comp (snd ℂ ℂ X) := by
      rw [fderiv_sub_const]
      rw [fderiv_fun_comp (f := fun y : ℂ × X => y.2) (g := fun u : X => phi u) (x := point)
        phi.differentiableAt (differentiableAt_snd (p := point)), phi.fderiv, fderiv_snd]
    have hOpF : fderiv ℂ (fun y : ℂ × X => (A 0) (y.2)) point = (A 0).comp (snd ℂ ℂ X) := by
      rw [fderiv_fun_comp (f := fun y : ℂ × X => y.2) (g := fun u : X => (A 0) u) (x := point)
        (A 0).differentiableAt (differentiableAt_snd (p := point)), (A 0).fderiv, fderiv_snd]
    have hSmF : fderiv ℂ (fun y : ℂ × X => y.1 • y.2) point =
        z₀ • snd ℂ ℂ X + (fst ℂ ℂ X).smulRight u₀ := by
      rw [fderiv_fun_smul (c := fun y : ℂ × X => y.1) (f := fun y : ℂ × X => y.2)
        (differentiableAt_fst (p := point)) (differentiableAt_snd (p := point))]
      rw [fderiv_fst, fderiv_snd]
    have hDer : (A 0).comp (snd ℂ ℂ X) - (z₀ • snd ℂ ℂ X + (fst ℂ ℂ X).smulRight u₀) =
        ((A 0) - z₀ • (1 : X →L[ℂ] X)).comp (snd ℂ ℂ X) - (fst ℂ ℂ X).smulRight u₀ := by
      refine ext fun v => ?_
      simp only [sub_apply, comp_apply, smul_apply, one_apply_eq_self, smulRight_apply,
        coe_fst', coe_snd', sub_add_eq_sub_sub]
    have hDop : DifferentiableAt ℂ (fun y : ℂ × X => (A 0) y.2) point :=
      DifferentiableAt.fun_comp' (f := fun y : ℂ × X => y.2) (g := fun u : X => (A 0) u)
        (x := point) (A 0).differentiableAt (differentiableAt_snd (p := point))
    have hDsm : DifferentiableAt ℂ (fun y : ℂ × X => y.1 • y.2) point :=
      DifferentiableAt.fun_smul (c := fun y : ℂ × X => y.1) (f := fun y : ℂ × X => y.2)
        (differentiableAt_fst (p := point)) (differentiableAt_snd (p := point))
    have hvecF : fderiv ℂ (fun y : ℂ × X => (A 0) y.2 - y.1 • y.2) point =
        ((A 0) - z₀ • (1 : X →L[ℂ] X)).comp (snd ℂ ℂ X) - (fst ℂ ℂ X).smulRight u₀ := by
      rw [fderiv_fun_sub (f := fun y : ℂ × X => (A 0) y.2) (g := fun y : ℂ × X => y.1 • y.2)
        (x := point) hDop hDsm, hOpF, hSmF, hDer]
    have hDphi : DifferentiableAt ℂ (fun y : ℂ × X => phi y.2 - 1) point :=
      (DifferentiableAt.fun_comp' (f := fun y : ℂ × X => y.2) (g := fun u : X => phi u)
        (x := point) phi.differentiableAt (differentiableAt_snd (p := point))).sub_const 1
    have hprod : fderiv ℂ (fun y : ℂ × X => (phi y.2 - 1, (A 0) y.2 - y.1 • y.2)) point =
        (phi.comp (snd ℂ ℂ X)).prod
          (((A 0) - z₀ • (1 : X →L[ℂ] X)).comp (snd ℂ ℂ X) -
            (fst ℂ ℂ X).smulRight u₀) := by
      rw [DifferentiableAt.fderiv_prodMk (f₁ := fun y : ℂ × X => phi y.2 - 1)
        (f₂ := fun y : ℂ × X => (A 0) y.2 - y.1 • y.2) hDphi (hDop.sub hDsm), hphiF, hvecF]
    have hslice : fderiv ℂ (fun y : ℂ × X => eigen ((0 : ℂ), y)) point =
        simpleEigenPartial (A 0) z₀ u₀ phi := by
      simpa [eigen, simpleEigenPartial, point] using hprod
    have hincl : HasFDerivAt (fun y : ℂ × X => ((0 : ℂ), y)) (inr ℂ ℂ (ℂ × X)) point :=
      (hasFDerivAt_const (0 : ℂ) point).prodMk (hasFDerivAt_id point)
    have hchain := (hcd.differentiableAt hone).hasFDerivAt.comp point hincl
    have hcomp : fderiv ℂ (fun y : ℂ × X => eigen ((0 : ℂ), y)) point =
        fderiv ℂ eigen base ∘L inr ℂ ℂ (ℂ × X) := by
      have hfun : (fun y : ℂ × X => eigen ((0 : ℂ), y)) =
          eigen ∘ fun y : ℂ × X => ((0 : ℂ), y) := by
        funext y
        rfl
      rw [hfun]
      exact hchain.fderiv
    rw [← hcomp, hslice]
    exact simpleEigenPartial_isInvertible (A 0) z₀ u₀ phi R hphi hAu hLeft hRight
  let branch := hcd.implicitFunction hone hinv
  have hbranch0 : branch 0 = (z₀, u₀) := hcd.implicitFunction_apply_self hone hinv
  have hevent := hcd.eventually_apply_implicitFunction hone hinv
  obtain ⟨s, hs, hson⟩ := hcd.contDiffAt_implicitFunction hone hinv |>.contDiffOn le_rfl
    (fun h => by simp at h)
  obtain ⟨eps, heps, heps_s⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨del, hdel, hdel_eq⟩ := Metric.mem_nhds_iff.mp hevent
  let radius := min eps del
  have hradius : 0 < radius := lt_min heps hdel
  have hballS : ball (0 : ℂ) radius ⊆ s :=
    (ball_subset_ball (min_le_left eps del)).trans heps_s
  have hballD : ball (0 : ℂ) radius ⊆ ball (0 : ℂ) del :=
    ball_subset_ball (min_le_right eps del)
  refine ⟨radius, hradius, fun t => (branch t).1, fun t => (branch t).2, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((hson.mono hballS).differentiableOn hone).fst
  · exact ((hson.mono hballS).differentiableOn hone).snd
  · simp [hbranch0]
  · simp [hbranch0]
  · intro t ht
    have hf := hdel_eq (hballD ht)
    rw [hzero] at hf
    have hphi1 : phi (branch t).2 = 1 := by
      have hfst : phi (branch t).2 - 1 = 0 := by
        simpa [eigen, branch] using congrArg Prod.fst hf
      exact sub_eq_zero.mp hfst
    have heig : A t ((branch t).2) = (branch t).1 • (branch t).2 := by
      have hsub : A t ((branch t).2) - (branch t).1 • (branch t).2 = 0 := by
        simpa [eigen] using congrArg Prod.snd hf
      exact sub_eq_zero.mp hsub
    refine ⟨?_, heig⟩
    intro hzeroU
    simp [hzeroU] at hphi1

end CKMA
