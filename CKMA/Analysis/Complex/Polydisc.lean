/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
public import CKMA.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Topology.UniformSpace.UniformApproximation
import TauCeti.Analysis.Complex.UniformLimit

/-!
# Full-polydisc Taylor expansion

Coordinate polyradii define open and closed polydiscs. Cauchy integrals over the
distinguished boundary give multiindex Taylor coefficients, their estimates and normal
convergence on the full open polydisc. Locally uniform limits on open subsets of ℂⁿ
remain holomorphic, by TauCeti's theorem on uniform limits of holomorphic maps on complex
normed spaces. Torus integration reuses TauCeti's polydisc Cauchy integral API; the coefficient
bound uses Mathlib's norm estimate for torus integrals.

Source: GAPS 45.2.

## Main definitions

* `CKMA.polydisc`, `CKMA.closedPolydisc`: open and closed polydiscs in `ℂⁿ`.
* `CKMA.polydiscTaylorCoefficient`: multivariable Cauchy integral Taylor coefficient.

## Main results

* `CKMA.norm_polydiscTaylorCoefficient_le`: Cauchy's estimate for multiindex Taylor coefficients.
* `CKMA.polydisc_taylor`: normally convergent Taylor expansion on an open polydisc.
* `CKMA.differentiableOn_of_locallyUniformLimit`: Weierstrass theorem for locally uniform limits
  of holomorphic functions on open subsets of `ℂⁿ`.
-/

@[expose] public section

noncomputable section

namespace CKMA

open Complex Filter MeasureTheory Metric Real Set Topology
open scoped BigOperators

/-- An open polydisc with unequal polyradii. -/
def polydisc {n : ℕ} (c : Fin n → ℂ) (R : Fin n → ℝ) : Set (Fin n → ℂ) :=
  {z | ∀ j, ‖z j - c j‖ < R j}

/-- A closed polydisc with unequal polyradii. -/
def closedPolydisc {n : ℕ} (c : Fin n → ℂ) (R : Fin n → ℝ) : Set (Fin n → ℂ) :=
  {z | ∀ j, ‖z j - c j‖ ≤ R j}

/-- Multivariable Cauchy coefficients on the distinguished boundary. -/
def polydiscTaylorCoefficient {n : ℕ} (f : (Fin n → ℂ) → ℂ)
    (c : Fin n → ℂ) (R : Fin n → ℝ) (α : Fin n → ℕ) : ℂ :=
  (2 * Real.pi * Complex.I) ^ (-(n : ℤ)) *
    ∯ z in T(c, R), (∏ j, (z j - c j) ^ (-(α j : ℤ) - 1)) * f z

/-- A closed polydisc is the product of the closed discs of the given polyradii. -/
private lemma closedPolydisc_eq_pi_closedBall {n : ℕ} (c : Fin n → ℂ) (R : Fin n → ℝ) :
    closedPolydisc c R = univ.pi fun i ↦ closedBall (c i) (R i) := by
  ext z
  simp [closedPolydisc, mem_closedBall, dist_eq_norm]

/-- An open polydisc is the product of the open discs of the given polyradii. -/
private lemma polydisc_eq_pi_ball {n : ℕ} (c : Fin n → ℂ) (R : Fin n → ℝ) :
    polydisc c R = univ.pi fun i ↦ ball (c i) (R i) := by
  ext z
  simp [polydisc, mem_ball, dist_eq_norm]

/-- The torus Jacobian has norm equal to the product of the absolute polyradii. -/
private lemma norm_torusJacobian {n : ℕ} (R : Fin n → ℝ) (θ : Fin n → ℝ) :
    ‖∏ i, (R i : ℂ) * exp (θ i * I) * I‖ = ∏ i, |R i| := by
  rw [norm_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [norm_mul, norm_mul, norm_real, Real.norm_eq_abs, norm_exp_ofReal_mul_I, norm_I,
    mul_one, mul_one]

/-- Nonnegative summable real series have a summable product over multiindices. -/
private lemma summable_nonneg_multiindex_prod {n : ℕ} {a : Fin n → ℕ → ℝ}
    (ha : ∀ i, Summable (a i)) (ha0 : ∀ i k, 0 ≤ a i k) :
    Summable fun α : Fin n → ℕ ↦ ∏ i, a i (α i) := by
  induction n with
  | zero =>
    have hfun : (fun α : Fin 0 → ℕ ↦ ∏ i, a i (α i)) = fun _ ↦ 1 := by
      ext α
      exact Fin.prod_univ_zero _
    rw [hfun]
    exact (hasSum_unique fun _ : Fin 0 → ℕ ↦ (1 : ℝ)).summable
  | succ n ih =>
    let e : ℕ × (Fin n → ℕ) ≃ (Fin (n + 1) → ℕ) := Fin.consEquiv fun _ ↦ ℕ
    have htail : Summable fun β : Fin n → ℕ ↦ ∏ i, a i.succ (β i) :=
      ih (fun i ↦ ha i.succ) fun i k ↦ ha0 i.succ k
    have hmul : Summable fun p : ℕ × (Fin n → ℕ) ↦ a 0 p.1 * ∏ i, a i.succ (p.2 i) :=
      (ha 0).mul_of_nonneg htail (fun k ↦ ha0 0 k)
        fun β ↦ Finset.prod_nonneg fun i _ ↦ ha0 i.succ (β i)
    have hcomp : (fun α : Fin (n + 1) → ℕ ↦ ∏ i, a i (α i)) ∘ e =
        fun p ↦ a 0 p.1 * ∏ i, a i.succ (p.2 i) := by
      ext p
      rw [Function.comp_apply, show e p = Fin.cons p.1 p.2 from rfl, Fin.prod_univ_succ,
        Fin.cons_zero]
      refine congrArg (a 0 p.1 * ·) ?_
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [Fin.cons_succ]
    have hmul' : Summable ((fun α : Fin (n + 1) → ℕ ↦ ∏ i, a i (α i)) ∘ e) := by
      rw [hcomp]
      exact hmul
    exact (e.summable_iff (f := fun α : Fin (n + 1) → ℕ ↦ ∏ i, a i (α i))).1 hmul'

/-- Absolute convergence passes to the finite product indexed by multiindices. -/
private lemma summable_norm_multiindex_prod {n : ℕ} {g : Fin n → ℕ → ℂ}
    (hg : ∀ i, Summable fun k ↦ ‖g i k‖) :
    Summable fun α : Fin n → ℕ ↦ ‖∏ i, g i (α i)‖ := by
  have hreal : Summable fun α : Fin n → ℕ ↦ ∏ i, ‖g i (α i)‖ :=
    summable_nonneg_multiindex_prod hg fun _ _ ↦ norm_nonneg _
  simpa [norm_prod] using hreal

/-- The product of absolutely summable series, summed over multiindices. -/
private lemma hasSum_multiindex_prod {n : ℕ} {g : Fin n → ℕ → ℂ}
    (hg : ∀ i, Summable fun k ↦ ‖g i k‖) :
    HasSum (fun α : Fin n → ℕ ↦ ∏ i, g i (α i)) (∏ i, ∑' k, g i k) := by
  induction n with
  | zero =>
    have hfun : (fun α : Fin 0 → ℕ ↦ ∏ i, g i (α i)) = fun _ ↦ 1 := by
      ext α
      exact Fin.prod_univ_zero _
    rw [hfun, Fin.prod_univ_zero]
    exact hasSum_unique _
  | succ n ih =>
    let e : ℕ × (Fin n → ℕ) ≃ (Fin (n + 1) → ℕ) := Fin.consEquiv fun _ ↦ ℕ
    have h0 : Summable fun k ↦ ‖g 0 k‖ := hg 0
    have htailN : ∀ i : Fin n, Summable fun k : ℕ ↦ ‖g (Fin.succ i) k‖ :=
      fun i ↦ hg (Fin.succ i)
    have htail := ih htailN
    have hmulSum : Summable fun p : ℕ × (Fin n → ℕ) ↦
        g 0 p.1 * ∏ i, g (Fin.succ i) (p.2 i) :=
      summable_mul_of_summable_norm h0 (summable_norm_multiindex_prod htailN)
    have hs0 : HasSum (fun p : ℕ × (Fin n → ℕ) ↦ g 0 p.1 * ∏ i, g (Fin.succ i) (p.2 i))
        ((∑' k, g 0 k) * ∏ i, ∑' k, g (Fin.succ i) k) := by
      have hs := hmulSum.hasSum
      rw [← tsum_mul_tsum_of_summable_norm h0 (summable_norm_multiindex_prod htailN),
        htail.tsum_eq] at hs
      exact hs
    have hcomp : (fun α : Fin (n + 1) → ℕ ↦ ∏ i, g i (α i)) ∘ e =
        fun p ↦ g 0 p.1 * ∏ i, g (Fin.succ i) (p.2 i) := by
      ext p
      rw [Function.comp_apply, show e p = Fin.cons p.1 p.2 from rfl, Fin.prod_univ_succ,
        Fin.cons_zero]
      refine congrArg (g 0 p.1 * ·) ?_
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [Fin.cons_succ]
    have hs' : HasSum ((fun α ↦ ∏ i, g i (α i)) ∘ e) (∏ i, ∑' k, g i k) := by
      rw [hcomp, Fin.prod_univ_succ]
      exact hs0
    exact (e.hasSum_iff).1 hs'

/-- One Cauchy factor expands as a geometric series inside its circle. -/
private lemma hasSum_cauchyFactor_geometric {c z zeta : ℂ} (hzeta : 0 < ‖zeta - c‖)
    (hz : ‖z - c‖ < ‖zeta - c‖) :
    HasSum (fun k : ℕ ↦ (z - c) ^ k * (zeta - c) ^ (-(k : ℤ) - 1)) ((zeta - z)⁻¹) := by
  have hzetane : zeta ≠ c := by
    intro h
    simp [h, norm_zero] at hzeta
  have hzeta0 : zeta - c ≠ 0 := sub_ne_zero.2 hzetane
  let ratio : ℂ := (z - c) / (zeta - c)
  have hratio : ‖ratio‖ < 1 := by
    rw [norm_div]
    exact (div_lt_one hzeta).2 hz
  have hmul := (hasSum_geometric_of_norm_lt_one hratio).mul_left (zeta - c)⁻¹
  have hterm : ∀ k : ℕ, (zeta - c)⁻¹ * ratio ^ k =
      (z - c) ^ k * (zeta - c) ^ (-(k : ℤ) - 1) := by
    intro k
    have hexp : -(k : ℤ) - 1 = -(k : ℤ) + (-1) := by ring
    have hgeo : (z - c) ^ k * (zeta - c) ^ (-(k : ℤ) - 1) =
        ratio ^ k * (zeta - c)⁻¹ := by
      calc
        (z - c) ^ k * (zeta - c) ^ (-(k : ℤ) - 1)
            = (z - c) ^ k * ((zeta - c) ^ (-(k : ℤ)) * (zeta - c) ^ (-1 : ℤ)) := by
              rw [hexp, zpow_add₀ hzeta0]
        _ = (z - c) ^ k * (((zeta - c) ^ k)⁻¹ * (zeta - c)⁻¹) := by
              rw [zpow_neg, zpow_natCast, zpow_neg_one]
        _ = ((z - c) ^ k * ((zeta - c) ^ k)⁻¹) * (zeta - c)⁻¹ := by ring
        _ = ((z - c) ^ k / (zeta - c) ^ k) * (zeta - c)⁻¹ := by
            congr 1
        _ = ((z - c) / (zeta - c)) ^ k * (zeta - c)⁻¹ := by rw [← div_pow]
        _ = ratio ^ k * (zeta - c)⁻¹ := by simp [ratio]
    calc
      (zeta - c)⁻¹ * ratio ^ k = ratio ^ k * (zeta - c)⁻¹ := by ring
      _ = (z - c) ^ k * (zeta - c) ^ (-(k : ℤ) - 1) := by rw [← hgeo]
  have hsub : zeta - z = (zeta - c) * (1 - ratio) := by
    have hratioMul : ratio * (zeta - c) = z - c := by
      simp [ratio, div_mul_cancel₀ _ hzeta0]
    calc
      zeta - z = (zeta - c) - (z - c) := by ring
      _ = (zeta - c) - ratio * (zeta - c) := by rw [hratioMul]
      _ = (zeta - c) * (1 - ratio) := by ring
  have hval : (zeta - c)⁻¹ * (1 - ratio)⁻¹ = (zeta - z)⁻¹ := by
    calc
      (zeta - c)⁻¹ * (1 - ratio)⁻¹ = (1 - ratio)⁻¹ * (zeta - c)⁻¹ := by ring
      _ = ((zeta - c) * (1 - ratio))⁻¹ := by rw [← mul_inv_rev]
      _ = (zeta - z)⁻¹ := by rw [← hsub]
  have hfun : (fun k : ℕ ↦ (zeta - c)⁻¹ * ratio ^ k) =
      fun k : ℕ ↦ (z - c) ^ k * (zeta - c) ^ (-(k : ℤ) - 1) := by
    ext k
    exact hterm k
  rw [hfun, hval] at hmul
  exact hmul

/-- The geometric Cauchy factor is absolutely summable inside its circle. -/
private lemma summable_norm_cauchyFactor {c z zeta : ℂ} (hzeta : 0 < ‖zeta - c‖)
    (hz : ‖z - c‖ < ‖zeta - c‖) :
    Summable fun k : ℕ ↦ ‖(z - c) ^ k * (zeta - c) ^ (-(k : ℤ) - 1)‖ := by
  have hq0 : 0 ≤ ‖z - c‖ / ‖zeta - c‖ := div_nonneg (norm_nonneg _) hzeta.le
  have hq1 : ‖z - c‖ / ‖zeta - c‖ < 1 := (div_lt_one hzeta).2 hz
  have hnorm : ∀ k : ℕ, ‖(z - c) ^ k * (zeta - c) ^ (-(k : ℤ) - 1)‖ =
      ‖zeta - c‖⁻¹ * (‖z - c‖ / ‖zeta - c‖) ^ k := by
    intro k
    have hexp : -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) := by omega
    rw [norm_mul, norm_pow, hexp, norm_zpow, zpow_neg, zpow_natCast]
    calc
      ‖z - c‖ ^ k * (‖zeta - c‖ ^ (k + 1))⁻¹
          = ‖z - c‖ ^ k * (‖zeta - c‖ ^ k * ‖zeta - c‖)⁻¹ := by rw [pow_succ]
      _ = ‖z - c‖ ^ k * (‖zeta - c‖⁻¹ * (‖zeta - c‖ ^ k)⁻¹) := by rw [mul_inv_rev]
      _ = (‖z - c‖ ^ k * (‖zeta - c‖ ^ k)⁻¹) * ‖zeta - c‖⁻¹ := by ring
      _ = (‖z - c‖ ^ k / ‖zeta - c‖ ^ k) * ‖zeta - c‖⁻¹ := by
          congr 1
      _ = (‖z - c‖ / ‖zeta - c‖) ^ k * ‖zeta - c‖⁻¹ := by rw [← div_pow]
      _ = ‖zeta - c‖⁻¹ * (‖z - c‖ / ‖zeta - c‖) ^ k := by ring
  simp_rw [hnorm]
  exact (summable_geometric_of_lt_one hq0 hq1).mul_left _

/-- The polydisc Cauchy kernel is the product of the coordinate geometric series. -/
private lemma hasSum_polydisc_kernel {n : ℕ} {c z : Fin n → ℂ} {R : Fin n → ℝ}
    (hR : ∀ j, 0 < R j) (hz : z ∈ polydisc c R) (θ : Fin n → ℝ) :
    HasSum (fun α : Fin n → ℕ ↦ (∏ j, (z j - c j) ^ α j) *
        ∏ j, (torusMap c R θ j - c j) ^ (-(α j : ℤ) - 1))
      (∏ j, (torusMap c R θ j - z j)⁻¹) := by
  have hsphere : ∀ j, ‖torusMap c R θ j - c j‖ = R j := by
    intro j
    have hh := TauCeti.torusMap_mem_pi_sphere (c := c) (fun j ↦ (hR j).le) θ j (mem_univ j)
    simpa [mem_sphere, dist_eq_norm] using hh
  let g : Fin n → ℕ → ℂ := fun j k ↦
    (z j - c j) ^ k * (torusMap c R θ j - c j) ^ (-(k : ℤ) - 1)
  have hg : ∀ j, Summable fun k ↦ ‖g j k‖ := by
    intro j
    exact summable_norm_cauchyFactor (by simpa [hsphere] using hR j)
      (by simpa [hsphere] using hz j)
  have hsum := hasSum_multiindex_prod hg
  have htsum : ∀ j, ∑' k, g j k = (torusMap c R θ j - z j)⁻¹ := by
    intro j
    exact (hasSum_cauchyFactor_geometric (by simpa [hsphere] using hR j)
      (by simpa [hsphere] using hz j)).tsum_eq
  have hfun : (fun α : Fin n → ℕ ↦ ∏ j, g j (α j)) =
      fun α : Fin n → ℕ ↦ (∏ j, (z j - c j) ^ α j) *
        ∏ j, (torusMap c R θ j - c j) ^ (-(α j : ℤ) - 1) := by
    ext α
    simp [g, Finset.prod_mul_distrib]
  have hrhs : (∏ j, ∑' k, g j k) = ∏ j, (torusMap c R θ j - z j)⁻¹ :=
    Finset.prod_congr rfl fun j _ ↦ htsum j
  rw [← hfun, ← hrhs]
  exact hsum

/-- Termwise integration of the geometric kernel produces the Taylor series. -/
private lemma hasSum_polydiscTaylor_of_mem {n : ℕ} (f : (Fin n → ℂ) → ℂ)
    (c : Fin n → ℂ) (R : Fin n → ℝ) (hR : ∀ j, 0 < R j)
    {U : Set (Fin n → ℂ)} (hsub : closedPolydisc c R ⊆ U) (hf : DifferentiableOn ℂ f U)
    {z : Fin n → ℂ} (hz : z ∈ polydisc c R) :
    HasSum (fun α : Fin n → ℕ ↦ polydiscTaylorCoefficient f c R α *
      ∏ j, (z j - c j) ^ α j) (f z) := by
  have hclosed : IsCompact (closedPolydisc c R) := by
    rw [closedPolydisc_eq_pi_closedBall]
    exact isCompact_univ_pi fun i ↦ isCompact_closedBall (c i) (R i)
  obtain ⟨M, hM⟩ := hclosed.exists_bound_of_continuousOn (hf.continuousOn.mono hsub)
  have hsphere : ∀ θ : Fin n → ℝ, ∀ j, ‖torusMap c R θ j - c j‖ = R j := by
    intro θ j
    have hh := TauCeti.torusMap_mem_pi_sphere (c := c) (fun j ↦ (hR j).le) θ j (mem_univ j)
    simpa [mem_sphere, dist_eq_norm] using hh
  let cube : Set (Fin n → ℝ) := Icc (0 : Fin n → ℝ) fun _ ↦ 2 * Real.pi
  let jac : (Fin n → ℝ) → ℂ := fun θ ↦ ∏ i, (R i : ℂ) * exp (θ i * I) * I
  let monomial : (Fin n → ℕ) → ℂ := fun α ↦ ∏ j, (z j - c j) ^ α j
  let kern : (Fin n → ℕ) → (Fin n → ℂ) → ℂ :=
    fun α zeta ↦ ∏ j, (zeta j - c j) ^ (-(α j : ℤ) - 1)
  let Fser : (Fin n → ℕ) → (Fin n → ℝ) → ℂ := fun α θ ↦
    jac θ * (monomial α * (kern α (torusMap c R θ) * f (torusMap c R θ)))
  let target : (Fin n → ℝ) → ℂ := fun θ ↦
    jac θ * ((∏ j, (torusMap c R θ j - z j)⁻¹) * f (torusMap c R θ))
  let q : Fin n → ℝ := fun j ↦ ‖z j - c j‖ / R j
  let B : (Fin n → ℕ) → ℝ := fun α ↦ M * ∏ j, q j ^ α j
  have hmapMem : ∀ θ, torusMap c R θ ∈ closedPolydisc c R := by
    intro θ j
    simpa [closedPolydisc] using (hsphere θ j).le
  have htorusCont : Continuous (torusMap c R) := TauCeti.continuous_torusMap c R
  have hfθ : Continuous fun θ ↦ f (torusMap c R θ) :=
    (hf.continuousOn.mono hsub).comp_continuous htorusCont hmapMem
  have hjacC : Continuous jac := by
    refine continuous_finsetProd _ fun i _ ↦ ?_
    fun_prop
  have hFC : ∀ α, Continuous (Fser α) := by
    intro α
    have hkerC : Continuous fun θ ↦ kern α (torusMap c R θ) := by
      refine continuous_finsetProd _ fun j _ ↦ ?_
      exact Continuous.zpow₀ (((continuous_apply j).comp htorusCont).sub continuous_const)
        (-(α j : ℤ) - 1) fun θ ↦ Or.inl <| by
          change torusMap c R θ j - c j ≠ 0
          rw [← norm_pos_iff, hsphere θ j]
          exact hR j
    exact hjacC.mul (continuous_const.mul (hkerC.mul hfθ))
  have hnormJac : ∀ θ, ‖jac θ‖ = ∏ j, R j := by
    intro θ
    rw [norm_torusJacobian]
    exact Finset.prod_congr rfl fun j _ ↦ abs_of_pos (hR j)
  have hnormF : ∀ α θ, ‖Fser α θ‖ ≤ B α := by
    intro α θ
    have hmon : ‖monomial α‖ = ∏ j, ‖z j - c j‖ ^ α j := by
      simp [monomial, norm_prod, norm_pow]
    have hkerN : ‖kern α (torusMap c R θ)‖ = ∏ j, (R j)⁻¹ ^ (α j + 1) := by
      simp only [kern, norm_prod]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      have hexp : -(α j : ℤ) - 1 = -((α j + 1 : ℕ) : ℤ) := by omega
      rw [hexp, norm_zpow, zpow_neg, zpow_natCast, inv_pow, hsphere]
    have hfN : ‖f (torusMap c R θ)‖ ≤ M := hM _ (hmapMem θ)
    have hprod : ‖Fser α θ‖ =
        ‖jac θ‖ * ‖monomial α‖ * ‖kern α (torusMap c R θ)‖ *
          ‖f (torusMap c R θ)‖ := by
      unfold Fser
      rw [norm_mul, norm_mul, norm_mul]
      ring
    rw [hprod, hnormJac, hmon, hkerN]
    have hcancel : (∏ j, R j) * (∏ j, ‖z j - c j‖ ^ α j) *
        (∏ j, (R j)⁻¹ ^ (α j + 1)) = ∏ j, q j ^ α j := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      calc
        R j * ‖z j - c j‖ ^ α j * (R j)⁻¹ ^ (α j + 1)
            = R j * ‖z j - c j‖ ^ α j * ((R j)⁻¹ ^ α j * (R j)⁻¹) := by rw [pow_succ]
        _ = (R j * (R j)⁻¹) * (‖z j - c j‖ ^ α j * (R j)⁻¹ ^ α j) := by ring
        _ = ‖z j - c j‖ ^ α j * (R j)⁻¹ ^ α j := by
            rw [mul_inv_cancel₀ (hR j).ne', one_mul]
        _ = (‖z j - c j‖ * (R j)⁻¹) ^ α j := by rw [← mul_pow]
        _ = (‖z j - c j‖ / R j) ^ α j := by rw [← div_eq_mul_inv]
        _ = q j ^ α j := by simp [q]
    have hle : (∏ j, q j ^ α j) * ‖f (torusMap c R θ)‖ ≤
        (∏ j, q j ^ α j) * M :=
      mul_le_mul_of_nonneg_left hfN (Finset.prod_nonneg fun j _ ↦ pow_nonneg
        (div_nonneg (norm_nonneg _) (hR j).le) _)
    calc
      (∏ j, R j) * (∏ j, ‖z j - c j‖ ^ α j) *
          (∏ j, (R j)⁻¹ ^ (α j + 1)) * ‖f (torusMap c R θ)‖
          = (∏ j, q j ^ α j) * ‖f (torusMap c R θ)‖ := by rw [hcancel]
      _ ≤ (∏ j, q j ^ α j) * M := hle
      _ = B α := by simp [B, mul_comm]
  have hBsum : Summable B := by
    have hgeom : ∀ j, Summable fun k : ℕ ↦ q j ^ k := by
      intro j
      exact summable_geometric_of_lt_one (div_nonneg (norm_nonneg _) (hR j).le)
        ((div_lt_one (hR j)).2 (hz j))
    exact (summable_nonneg_multiindex_prod hgeom
      fun j k ↦ pow_nonneg (div_nonneg (norm_nonneg _) (hR j).le) k).mul_left M
  have hpoint : ∀ θ, HasSum (fun α ↦ Fser α θ) (target θ) := by
    intro θ
    have hker := (hasSum_polydisc_kernel hR hz θ).mul_left
      (jac θ * f (torusMap c R θ))
    have hfunθ : (fun α ↦ (jac θ * f (torusMap c R θ)) *
        ((∏ j, (z j - c j) ^ α j) *
          ∏ j, (torusMap c R θ j - c j) ^ (-(α j : ℤ) - 1))) =
        fun α ↦ Fser α θ := by
      ext α
      simp [Fser, monomial, kern]
      ring
    have ht : (jac θ * f (torusMap c R θ)) * (∏ j, (torusMap c R θ j - z j)⁻¹) =
        target θ := by
      simp [target]
      ring
    rw [hfunθ, ht] at hker
    exact hker
  have hdom : Integrable (fun _ : Fin n → ℝ ↦ ∑' α, B α) (volume.restrict cube) := by
    simpa [IntegrableOn] using integrableOn_const (μ := volume) (s := cube)
      (C := ∑' α, B α) (hs := (lt_top_iff_ne_top.mp measure_Icc_lt_top))
  have hDCT := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := volume.restrict cube) (F := Fser) (f := target) (bound := fun α _ ↦ B α)
    (fun α ↦ (hFC α).stronglyMeasurable.aestronglyMeasurable)
    (fun α ↦ ae_of_all _ fun θ ↦ hnormF α θ)
    (ae_of_all _ fun _ ↦ hBsum)
    hdom
    (ae_of_all _ hpoint)
  have hterm : ∀ α, ∫ θ in cube, Fser α θ =
      monomial α * ∯ zeta in T(c, R), kern α zeta * f zeta := by
    intro α
    have hEq : EqOn (Fser α) (fun θ ↦ monomial α *
        (jac θ * (kern α (torusMap c R θ) * f (torusMap c R θ)))) cube :=
      fun θ _ ↦ by simp [Fser]; ring
    rw [setIntegral_congr_fun measurableSet_Icc hEq, integral_const_mul]
    congr 1
  have htargetInt : ∫ θ in cube, target θ =
      ∯ zeta in T(c, R), (∏ j, (zeta j - z j)⁻¹) * f zeta := by
    have hEq : EqOn target (fun θ ↦ jac θ *
        ((∏ j, (torusMap c R θ j - z j)⁻¹) * f (torusMap c R θ))) cube :=
      fun _ _ ↦ by simp [target]
    rw [setIntegral_congr_fun measurableSet_Icc hEq]
    simp only [torusIntegral, smul_eq_mul, jac]
  have hcauchy :
      (∯ zeta in T(c, R), (∏ j, (zeta j - z j)⁻¹) • f zeta) =
        (2 * Real.pi * I) ^ n • f z := by
    have hd : DifferentiableOn ℂ f (univ.pi fun i ↦ closedBall (c i) (R i)) := by
      rw [← closedPolydisc_eq_pi_closedBall]
      exact hf.mono hsub
    have hw : z ∈ univ.pi fun i ↦ ball (c i) (R i) := by
      rw [← polydisc_eq_pi_ball]
      exact hz
    simpa [Finset.prod_inv_distrib] using hd.torusIntegral_prod_sub_inv_smul hw
  have hscaled := hDCT.mul_left ((2 * Real.pi * I) ^ (-(n : ℤ)))
  have hfunI : (fun α ↦ (2 * Real.pi * I) ^ (-(n : ℤ)) * ∫ θ in cube, Fser α θ) =
      fun α ↦ polydiscTaylorCoefficient f c R α * monomial α := by
    ext α
    rw [hterm, polydiscTaylorCoefficient]
    ring
  have hval : (2 * Real.pi * I) ^ (-(n : ℤ)) * ∫ θ in cube, target θ = f z := by
    rw [htargetInt]
    have hsmul : (∯ zeta in T(c, R), (∏ j, (zeta j - z j)⁻¹) * f zeta) =
        ∯ zeta in T(c, R), (∏ j, (zeta j - z j)⁻¹) • f zeta := by
      simp [smul_eq_mul]
    rw [hsmul, hcauchy, smul_eq_mul, ← mul_assoc, zpow_neg, zpow_natCast,
      inv_mul_cancel₀ (pow_ne_zero _ two_pi_I_ne_zero), one_mul]
  rw [hfunI, hval] at hscaled
  simpa [monomial] using hscaled

/-- Cauchy's multiindex bound on the contour coefficient.
The estimate uses only the distinguished-boundary bound and requires no holomorphy. -/
theorem norm_polydiscTaylorCoefficient_le {n : ℕ}
    (f : (Fin n → ℂ) → ℂ) (c : Fin n → ℂ) (R : Fin n → ℝ)
    (hR : ∀ j, 0 < R j) {M : ℝ}
    (hbound : ∀ z, (∀ j, ‖z j - c j‖ = R j) → ‖f z‖ ≤ M) (α : Fin n → ℕ) :
    ‖polydiscTaylorCoefficient f c R α‖ ≤ M * ∏ j, (R j)⁻¹ ^ α j := by
  have hnorm : ∀ θ : Fin n → ℝ, ∀ j,
      ‖torusMap c R θ j - c j‖ = R j := by
    intro θ j
    have hh := TauCeti.torusMap_mem_pi_sphere (c := c) (fun j ↦ (hR j).le) θ j (Set.mem_univ j)
    simpa only [Metric.mem_sphere, dist_eq_norm] using hh
  have hprod : ∀ θ : Fin n → ℝ,
      ‖∏ j, (torusMap c R θ j - c j) ^ (-(α j : ℤ) - 1)‖ =
        ∏ j, (R j)⁻¹ ^ (α j + 1) := by
    intro θ
    rw [norm_prod]
    apply Finset.prod_congr rfl
    intro j _
    have he : -(α j : ℤ) - 1 = -((α j + 1 : ℕ) : ℤ) := by omega
    rw [he, norm_zpow, zpow_neg, zpow_natCast, inv_pow, hnorm]
  have hi := norm_torusIntegral_le_of_norm_le_const (c := c) (R := R)
    (f := fun z ↦ (∏ j, (z j - c j) ^ (-(α j : ℤ) - 1)) * f z)
    (C := (∏ j, (R j)⁻¹ ^ (α j + 1)) * M) (fun θ ↦ by
      rw [norm_mul, hprod]
      exact mul_le_mul_of_nonneg_left (hbound _ (hnorm θ))
        (Finset.prod_nonneg fun j _ ↦ pow_nonneg (inv_nonneg.mpr (hR j).le) _))
  have hK : ‖(2 * Real.pi * Complex.I : ℂ) ^ (-(n : ℤ))‖ =
      ((2 * Real.pi) ^ n)⁻¹ := by
    rw [norm_zpow, zpow_neg, zpow_natCast]
    simp [abs_of_pos Real.pi_pos]
  have habs : (∏ j, |R j|) = ∏ j, R j := by
    exact Finset.prod_congr rfl fun j _ ↦ abs_of_pos (hR j)
  have hcancel : (∏ j, R j) * (∏ j, (R j)⁻¹ ^ (α j + 1)) =
      ∏ j, (R j)⁻¹ ^ α j := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [pow_succ]
    calc R j * ((R j)⁻¹ ^ α j * (R j)⁻¹) =
        (R j * (R j)⁻¹) * (R j)⁻¹ ^ α j := by ring
      _ = _ := by rw [mul_inv_cancel₀ (hR j).ne', one_mul]
  have hA : (2 * Real.pi) ^ n ≠ 0 := pow_ne_zero _ (by positivity)
  calc
    ‖polydiscTaylorCoefficient f c R α‖ =
      ((2 * Real.pi) ^ n)⁻¹ *
        ‖∯ z in T(c, R), (∏ j, (z j - c j) ^ (-(α j : ℤ) - 1)) * f z‖ := by
      rw [polydiscTaylorCoefficient, norm_mul, hK]
    _ ≤ ((2 * Real.pi) ^ n)⁻¹ *
        (((2 * Real.pi) ^ n * ∏ j, |R j|) *
          ((∏ j, (R j)⁻¹ ^ (α j + 1)) * M)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = M * ∏ j, (R j)⁻¹ ^ α j := by
      rw [habs]
      calc ((2 * Real.pi) ^ n)⁻¹ *
          (((2 * Real.pi) ^ n * ∏ j, R j) *
            ((∏ j, (R j)⁻¹ ^ (α j + 1)) * M)) =
          (((2 * Real.pi) ^ n)⁻¹ * (2 * Real.pi) ^ n) *
            ((∏ j, R j) * (∏ j, (R j)⁻¹ ^ (α j + 1))) * M := by ring
        _ = _ := by rw [inv_mul_cancel₀ hA, one_mul, hcancel]; ring

/-- Cauchy's estimate gives normal convergence of the Taylor series on the open polydisc. -/
private lemma normallySummableOn_polydiscTaylor {n : ℕ} (f : (Fin n → ℂ) → ℂ)
    (c : Fin n → ℂ) (R : Fin n → ℝ) (hR : ∀ j, 0 < R j)
    {U : Set (Fin n → ℂ)} (hsub : closedPolydisc c R ⊆ U) (hf : DifferentiableOn ℂ f U) :
    NormallySummableOn (fun α : Fin n → ℕ ↦ fun z ↦
      polydiscTaylorCoefficient f c R α * ∏ j, (z j - c j) ^ α j) (polydisc c R) := by
  have hclosed : IsCompact (closedPolydisc c R) := by
    rw [closedPolydisc_eq_pi_closedBall]
    exact isCompact_univ_pi fun i ↦ isCompact_closedBall (c i) (R i)
  obtain ⟨M, hM⟩ := hclosed.exists_bound_of_continuousOn (hf.continuousOn.mono hsub)
  have hM0 : 0 ≤ M := by
    have hc : c ∈ closedPolydisc c R := by
      intro j
      simpa [closedPolydisc] using (hR j).le
    exact (norm_nonneg (f c)).trans (hM c hc)
  have htorus : ∀ zeta, (∀ j, ‖zeta j - c j‖ = R j) → ‖f zeta‖ ≤ M := by
    intro zeta hzeta
    exact hM zeta fun j ↦ (hzeta j).le
  intro K hK hKsub
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · refine ⟨fun _ ↦ ?_, ?_⟩
    · rw [image_empty]
      exact bddAbove_empty
    · simp only [image_empty, Real.sSup_empty]
      exact summable_zero
  · let term : (Fin n → ℕ) → (Fin n → ℂ) → ℂ := fun α w ↦
      polydiscTaylorCoefficient f c R α * ∏ j, (w j - c j) ^ α j
    let ρ : Fin n → ℝ := fun j ↦ sSup ((fun w ↦ ‖w j - c j‖) '' K)
    have hcont : ∀ j, ContinuousOn (fun w : Fin n → ℂ ↦ ‖w j - c j‖) K := fun j ↦
      (continuous_norm.comp ((continuous_apply j).sub continuous_const)).continuousOn
    have hρle : ∀ j, ∀ w ∈ K, ‖w j - c j‖ ≤ ρ j := fun j w hw ↦
      le_csSup (hK.bddAbove_image (hcont j)) (mem_image_of_mem _ hw)
    have hρlt : ∀ j, ρ j < R j := by
      intro j
      obtain ⟨w, hw, hmax⟩ := hK.exists_isMaxOn hKne (hcont j)
      have hEq : ρ j = ‖w j - c j‖ := by
        apply le_antisymm
        · refine csSup_le (hKne.image _) ?_
          rintro _ ⟨w', hw', rfl⟩
          exact hmax hw'
        · exact le_csSup (hK.bddAbove_image (hcont j)) (mem_image_of_mem _ hw)
      rw [hEq]
      exact (hKsub hw) j
    let majorant : (Fin n → ℕ) → ℝ := fun α ↦ M * ∏ j, (ρ j / R j) ^ α j
    have hρ0 : ∀ j, 0 ≤ ρ j := fun j ↦
      (norm_nonneg ((hKne.some) j - c j)).trans (hρle j hKne.some hKne.some_mem)
    have hmajor : Summable majorant := by
      have hgeom : ∀ j, Summable fun k : ℕ ↦ (ρ j / R j) ^ k := fun j ↦
        summable_geometric_of_lt_one (div_nonneg (hρ0 j) (hR j).le)
          ((div_lt_one (hR j)).2 (hρlt j))
      exact (summable_nonneg_multiindex_prod hgeom fun j k ↦
        pow_nonneg (div_nonneg (hρ0 j) (hR j).le) k).mul_left M
    have hle : ∀ α, ∀ w ∈ K, ‖term α w‖ ≤ majorant α := by
      intro α w hw
      have hcoef := norm_polydiscTaylorCoefficient_le f c R hR htorus α
      have hpow : ∏ j, ‖w j - c j‖ ^ α j ≤ ∏ j, ρ j ^ α j :=
        Finset.prod_le_prod₀ (fun j _ ↦ pow_nonneg (norm_nonneg _) _) fun j _ ↦
          pow_le_pow_left₀ (norm_nonneg _) (hρle j w hw) _
      have hfac : (∏ j, (R j)⁻¹ ^ α j) * ∏ j, ρ j ^ α j =
          ∏ j, (ρ j / R j) ^ α j := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun j _ ↦ ?_
        rw [mul_comm, ← mul_pow, div_eq_mul_inv]
      calc
        ‖term α w‖ = ‖polydiscTaylorCoefficient f c R α‖ *
            ∏ j, ‖w j - c j‖ ^ α j := by simp [term, norm_prod, norm_pow]
        _ ≤ (M * ∏ j, (R j)⁻¹ ^ α j) * ∏ j, ρ j ^ α j :=
            mul_le_mul hcoef hpow
              (Finset.prod_nonneg fun j _ ↦ pow_nonneg (norm_nonneg _) _)
              (mul_nonneg hM0 (Finset.prod_nonneg fun j _ ↦
                pow_nonneg (inv_nonneg.mpr (hR j).le) _))
        _ = M * ((∏ j, (R j)⁻¹ ^ α j) * ∏ j, ρ j ^ α j) := by ring
        _ = M * ∏ j, (ρ j / R j) ^ α j := by rw [hfac]
        _ = majorant α := rfl
    refine ⟨fun α ↦ ⟨majorant α, fun t ht ↦ ?_⟩, ?_⟩
    · obtain ⟨w, hw, rfl⟩ := ht
      exact hle α w hw
    · refine Summable.of_nonneg_of_le (fun α ↦ ?_) (fun α ↦ ?_) hmajor
      · obtain ⟨w, hw⟩ := hKne
        exact (norm_nonneg _).trans (le_csSup ⟨majorant α, fun t ht ↦ by
          obtain ⟨w', hw', rfl⟩ := ht
          exact hle α w' hw'⟩
          (mem_image_of_mem (fun w ↦ ‖term α w‖) hw))
      · exact csSup_le (hKne.image _) fun t ht ↦ by
          obtain ⟨w, hw, rfl⟩ := ht
          exact hle α w hw

/-- **45.2**: Taylor expansion on the full open polydisc, with normal convergence. -/
theorem polydisc_taylor {n : ℕ} (f : (Fin n → ℂ) → ℂ)
    (c : Fin n → ℂ) (R : Fin n → ℝ) (hR : ∀ j, 0 < R j)
    {U : Set (Fin n → ℂ)} (hsub : closedPolydisc c R ⊆ U)
    (hf : DifferentiableOn ℂ f U) :
    (∀ z ∈ polydisc c R, HasSum (fun α : Fin n → ℕ ↦
      polydiscTaylorCoefficient f c R α * ∏ j, (z j - c j) ^ α j) (f z)) ∧
    NormallySummableOn (fun α : Fin n → ℕ ↦ fun z ↦
      polydiscTaylorCoefficient f c R α * ∏ j, (z j - c j) ^ α j) (polydisc c R) :=
  ⟨fun z hz ↦ hasSum_polydiscTaylor_of_mem f c R hR hsub hf hz,
    normallySummableOn_polydiscTaylor f c R hR hsub hf⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The several-variable Weierstrass theorem on open subsets of `ℂⁿ`: a locally uniform limit of
holomorphic functions is holomorphic. This is TauCeti's `TendstoUniformlyOn.differentiableOn`
applied on small balls, whose closures are compact. -/
theorem differentiableOn_of_locallyUniformLimit [CompleteSpace E] {n : ℕ}
    {F : ℕ → (Fin n → ℂ) → E} {f : (Fin n → ℂ) → E} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hF : ∀ k, DifferentiableOn ℂ (F k) U)
    (hlim : TendstoLocallyUniformlyOn F f atTop U) : DifferentiableOn ℂ f U := by
  intro z hz
  obtain ⟨R, hR, hRs⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hz)
  have hunif : TendstoUniformlyOn F f atTop (ball z R) :=
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_closedBall z R)).1
      (hlim.mono hRs)).mono ball_subset_closedBall
  have hd : DifferentiableOn ℂ f (ball z R) := hunif.differentiableOn
    (Eventually.of_forall fun k ↦ (hF k).mono (ball_subset_closedBall.trans hRs)) isOpen_ball
  exact (hd.differentiableAt (ball_mem_nhds z hR)).differentiableWithinAt

end CKMA
