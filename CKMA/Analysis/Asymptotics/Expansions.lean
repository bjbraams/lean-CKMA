/-
Copyright (c) 2026 CKMA contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CKMA contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import TauCeti.Analysis.Asymptotics.AsymptoticExpansion
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Sectorial expansions, Watson's lemma, Laplace's method and Karamata's theorem

Complex sectors support Borel–Ritt realization of formal power series by holomorphic functions
with uniform sectorial expansions. Watson's lemma controls the remainders of Laplace integrals
`∫_0^∞ e^{-x t} a(t) dt` of amplitudes `a` with values in a real Banach space, and gives their
full expansion in the scale `x ^ (-(n + α))` in the sense of TauCeti's
`Asymptotics.HasAsymptoticExpansion`; by `Asymptotics.HasAsymptoticExpansion.unique` and
`CKMA.isAsymptoticScale_rpow_neg` its coefficients are unique. An interior strict
nondegenerate minimum of the phase gives the leading Laplace term. The Watson proofs use
Mathlib's Gamma integral and its exponential-decay integrability criterion. The
interior-minimum proof uses Mathlib's Taylor theorem, dominated convergence, and the Gaussian
integral. Karamata's equivalence relates positive half-line measures, their
Laplace–Stieltjes transforms and regularly varying cumulative mass.

Sources: GAPS 50.6, 50.9, 50.11 and 50.29. Asymptotic scales and Poincaré expansions are
TauCeti's `Asymptotics.IsAsymptoticScale` and `Asymptotics.HasAsymptoticExpansion`.

## Main definitions

* `CKMA.complexSector`, `CKMA.closedComplexSector`: open and closed complex sectors.
* `CKMA.HasSectorialPowerExpansion`: uniform asymptotic power expansion on subsectors.
* `CKMA.asymptoticLaplaceIntegral`: Laplace integral on `(0, ∞)`.
* `CKMA.HasExponentialTailBound`: exponential growth bound at infinity.
* `CKMA.IsSlowlyVarying`: Karamata slow variation at infinity.
* `CKMA.nonnegativeCumulativeMass`, `CKMA.laplaceStieltjesTransform`: cumulative mass and
  Laplace–Stieltjes transform of a measure.

## Main results

* `CKMA.borel_ritt`: Borel–Ritt realization of formal power series on sectors.
* `CKMA.isAsymptoticScale_rpow_neg`: the powers `x ^ (-(n + α))` form an asymptotic scale.
* `CKMA.watson_laplace_remainder`, `CKMA.watson_laplace_expansion`: Watson's lemma.
* `CKMA.laplace_interior_minimum`: Laplace's method at an interior minimum.
* `CKMA.karamata_tauberian`: Karamata's Tauberian theorem.
-/

public section

noncomputable section

namespace CKMA

open MeasureTheory Filter Topology Asymptotics
open scoped BigOperators

/-- The open complex sector centered on angle `θ` with opening `ω`, excluding its vertex. -/
@[expose]
def complexSector (θ ω : ℝ) : Set ℂ :=
  {z | z ≠ 0 ∧ |Complex.arg (Complex.exp (-(θ : ℂ) * Complex.I) * z)| < ω / 2}

/-- Membership in `CKMA.complexSector`. -/
theorem mem_complexSector_iff {θ ω : ℝ} {z : ℂ} :
    z ∈ complexSector θ ω ↔
      z ≠ 0 ∧ |Complex.arg (Complex.exp (-(θ : ℂ) * Complex.I) * z)| < ω / 2 :=
  Iff.rfl

/-- A closed proper subsector, with vertex still omitted. -/
@[expose]
def closedComplexSector (θ ω : ℝ) : Set ℂ :=
  {z | z ≠ 0 ∧ |Complex.arg (Complex.exp (-(θ : ℂ) * Complex.I) * z)| ≤ ω / 2}

/-- Membership in `CKMA.closedComplexSector`. -/
theorem mem_closedComplexSector_iff {θ ω : ℝ} {z : ℂ} :
    z ∈ closedComplexSector θ ω ↔
      z ≠ 0 ∧ |Complex.arg (Complex.exp (-(θ : ℂ) * Complex.I) * z)| ≤ ω / 2 :=
  Iff.rfl

/-- The open sector lies in the closed sector of the same opening. -/
theorem complexSector_subset_closedComplexSector (θ ω : ℝ) :
    complexSector θ ω ⊆ closedComplexSector θ ω :=
  fun _ hz ↦ ⟨hz.1, hz.2.le⟩

/-- Sectorial power expansion with estimates uniform on every closed proper subsector.
The conventional `O(z^N)` remainder is required at every order. -/
@[expose]
def HasSectorialPowerExpansion (f : ℂ → ℂ) (a : ℕ → ℂ) (θ ω : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → η < ω → ∀ N : ℕ, ∃ C r : ℝ, 0 < C ∧ 0 < r ∧
    ∀ z ∈ closedComplexSector θ η, ‖z‖ < r →
      ‖f z - ∑ n ∈ Finset.range N, a n * z ^ n‖ ≤ C * ‖z‖ ^ N

/-- The defining property of `CKMA.HasSectorialPowerExpansion`. -/
theorem hasSectorialPowerExpansion_iff {f : ℂ → ℂ} {a : ℕ → ℂ} {θ ω : ℝ} :
    HasSectorialPowerExpansion f a θ ω ↔
      ∀ η : ℝ, 0 < η → η < ω → ∀ N : ℕ, ∃ C r : ℝ, 0 < C ∧ 0 < r ∧
        ∀ z ∈ closedComplexSector θ η, ‖z‖ < r →
          ‖f z - ∑ n ∈ Finset.range N, a n * z ^ n‖ ≤ C * ‖z‖ ^ N :=
  Iff.rfl

/-- **50.6**: Borel–Ritt realization on a sector of opening `ω < 2π`. For `ω ≤ 0` the
expansion condition is vacuous. -/
theorem borel_ritt (a : ℕ → ℂ) (θ : ℝ) {ω : ℝ} (hωπ : ω < 2 * Real.pi) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (complexSector θ ω) ∧
      HasSectorialPowerExpansion f a θ ω := by
  sorry

/-- The inverse powers `x ^ (-(n + α))` form an asymptotic scale at infinity. -/
theorem isAsymptoticScale_rpow_neg (α : ℝ) :
    IsAsymptoticScale atTop (fun (n : ℕ) (x : ℝ) ↦ x ^ (-((n : ℝ) + α))) := by
  refine IsAsymptoticScale.of_isLittleO fun n ↦ ?_
  refine (isLittleO_iff_tendsto' ?_).mpr ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx h
    exact ((Real.rpow_pos_of_pos hx _).ne' h).elim
  · refine tendsto_inv_atTop_zero.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hexponent : -(((n + 1 : ℕ) : ℝ) + α) - -((n : ℝ) + α) = -1 := by
      push_cast
      ring
    rw [← Real.rpow_sub hx, hexponent, Real.rpow_neg_one]

section Watson

variable {E : Type*} [NormedAddCommGroup E]

/-- Exponential growth in the tail, with constants that need not be sharp. -/
@[expose]
def HasExponentialTailBound (a : ℝ → E) : Prop :=
  ∃ C c T : ℝ, 0 < C ∧ 0 < T ∧ ∀ t : ℝ, T ≤ t → ‖a t‖ ≤ C * Real.exp (c * t)

/-- The defining property of `CKMA.HasExponentialTailBound`. -/
theorem hasExponentialTailBound_iff {a : ℝ → E} :
    HasExponentialTailBound a ↔
      ∃ C c T : ℝ, 0 < C ∧ 0 < T ∧ ∀ t : ℝ, T ≤ t → ‖a t‖ ≤ C * Real.exp (c * t) :=
  Iff.rfl

/-- An exponential tail bound is a big-O bound by an exponential at infinity. -/
theorem HasExponentialTailBound.exists_isBigO {a : ℝ → E} (h : HasExponentialTailBound a) :
    ∃ c : ℝ, a =O[atTop] fun t ↦ Real.exp (c * t) := by
  obtain ⟨C, c, T, _, _, htail⟩ := h
  refine ⟨c, isBigO_iff.mpr ⟨C, ?_⟩⟩
  filter_upwards [eventually_ge_atTop T] with t ht
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using htail t ht

variable [NormedSpace ℝ E]

/-- A real-axis Laplace integral `∫_0^∞ e^{-x t} a(t) dt` with amplitude in a real normed
space. -/
@[expose]
def asymptoticLaplaceIntegral (a : ℝ → E) (x : ℝ) : E :=
  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(x * t)) • a t

/-- The defining formula of `CKMA.asymptoticLaplaceIntegral`. -/
theorem asymptoticLaplaceIntegral_def (a : ℝ → E) (x : ℝ) :
    asymptoticLaplaceIntegral a x = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(x * t)) • a t :=
  rfl

/-- The Gamma integrand remains integrable when its exponential rate is rescaled. -/
private lemma integrableOn_laplace_rpow {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-(x * t)) * t ^ (b - 1)) (Set.Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ ↦ Real.exp (-(x * t)) * (x * t) ^ (b - 1))
      (Set.Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff _ 0 hx).mpr (by
      simpa only [mul_zero] using Real.GammaIntegral_convergent hb)
  refine IntegrableOn.congr_fun (hi.const_mul (x ^ (b - 1))⁻¹) (fun t ht ↦ ?_) measurableSet_Ioi
  rw [Real.mul_rpow hx.le ht.le, mul_left_comm _ (Real.exp _),
    inv_mul_cancel_left₀ (Real.rpow_pos_of_pos hx _).ne']

/-- The Gamma integral at a positive rate, written using the negative exponent. -/
private lemma integral_laplace_rpow {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    ∫ t : ℝ in Set.Ioi 0, Real.exp (-(x * t)) * t ^ (b - 1) =
      Real.Gamma b * x ^ (-b) := by
  simp only [mul_comm (Real.exp _), Real.integral_rpow_mul_exp_neg_mul_Ioi hb hx,
    one_div, Real.inv_rpow hx.le, Real.rpow_neg hx.le, mul_comm (Real.Gamma b)]

/-- A locally integrable amplitude of exponential growth admits a Laplace weight above its
growth rate. -/
private lemma integrableOn_laplace_weight {a : ℝ → E} {c x : ℝ}
    (hloc : ∀ R : ℝ, 0 < R → IntegrableOn a (Set.Ioo 0 R))
    (htail : a =O[atTop] (fun t ↦ Real.exp (c * t))) (hx : c < x) :
    IntegrableOn (fun t ↦ Real.exp (-(x * t)) • a t) (Set.Ioi 0) := by
  have hloc' : LocallyIntegrableOn a (Set.Ici 0) := by
    intro t ht
    have hR : t < t + 1 := lt_add_one t
    refine ⟨Set.Ici 0 ∩ Set.Iio (t + 1), inter_mem_nhdsWithin _ (Iio_mem_nhds hR), ?_⟩
    exact (integrableOn_Icc_iff_integrableOn_Ioo (a := 0) (b := t + 1)).mpr
      (hloc _ (by linarith [ht.out])) |>.mono_set
      (fun _ hu ↦ ⟨hu.1, hu.2.le⟩)
  have hi := (integrableOn_exp_neg_smul_of_isBigO_exp hloc' htail hx).mono_set
    Set.Ioi_subset_Ici_self
  simpa only [neg_mul] using hi

/-- A weighted power times a vector coefficient is integrable on the positive half-line. -/
private lemma integrableOn_laplace_monomial {b x : ℝ} (hb : 0 < b) (hx : 0 < x) (c : E) :
    IntegrableOn (fun t ↦ Real.exp (-(x * t)) • (t ^ (b - 1) • c)) (Set.Ioi 0) := by
  simp only [smul_smul]
  exact (integrableOn_laplace_rpow hb hx).smul_const c

/-- Integrating a weighted power produces its Gamma factor. -/
private lemma integral_laplace_monomial [CompleteSpace E] {b x : ℝ} (hb : 0 < b) (hx : 0 < x)
    (c : E) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(x * t)) • (t ^ (b - 1) • c) =
      (Real.Gamma b * x ^ (-b)) • c := by
  simp only [smul_smul]
  rw [integral_smul_const, integral_laplace_rpow hb hx]

/-- Beyond the cutoff, the difference between the two Laplace rates gives uniform decay. -/
private lemma laplace_exp_le_mul {x x₀ δ t : ℝ} (hx : 2 * x₀ ≤ x) (hx₀ : 0 < x₀)
    (hδ : 0 ≤ δ) (ht : δ ≤ t) :
    Real.exp (-(x * t)) ≤ Real.exp (-(δ / 2) * x) * Real.exp (-(x₀ * t)) := by
  have hrate : (δ / 2) * x ≤ (x - x₀) * t := calc
    (δ / 2) * x = (x / 2) * δ := by ring
    _ ≤ (x - x₀) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ
    _ ≤ (x - x₀) * t := mul_le_mul_of_nonneg_left ht (by linarith)
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- A power bound near zero and one integrable Laplace weight control the full Laplace integral. -/
private lemma laplace_bigO_of_isBigO_rpow {b x₀ : ℝ} (hb : 0 < b) (hx₀ : 0 < x₀)
    {f : ℝ → E}
    (hint : IntegrableOn (fun t ↦ Real.exp (-(x₀ * t)) • f t) (Set.Ioi 0))
    (hzero : f =O[𝓝[>] (0 : ℝ)] fun t ↦ t ^ (b - 1)) :
    asymptoticLaplaceIntegral f =O[atTop] fun x : ℝ ↦ x ^ (-b) := by
  obtain ⟨C, hC, hbound⟩ := hzero.exists_pos
  obtain ⟨δ, hδ, hδbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hbound.bound
  let F : ℝ → ℝ := fun t ↦ ‖Real.exp (-(x₀ * t)) • f t‖
  obtain ⟨D, _, hexp⟩ :=
    (isLittleO_exp_neg_mul_rpow_atTop (half_pos hδ) (-b)).isBigO.exists_nonneg
  refine isBigO_iff.mpr ⟨C * Real.Gamma b + D * (∫ t in Set.Ioi 0, F t), ?_⟩
  filter_upwards [hexp.bound, eventually_ge_atTop (2 * x₀)] with x hxe hx
  have hxpos : 0 < x := by linarith
  let g : ℝ → ℝ := fun t ↦ Real.exp (-(x * t)) * t ^ (b - 1)
  let e : ℝ := Real.exp (-(δ / 2) * x)
  have hgi : IntegrableOn g (Set.Ioi 0) := integrableOn_laplace_rpow hb hxpos
  have hF : IntegrableOn F (Set.Ioi 0) := hint.norm
  have hnonneg : 0 ≤ ∫ t in Set.Ioi 0, F t := integral_nonneg fun _ ↦ norm_nonneg _
  have hmajor :
      ‖asymptoticLaplaceIntegral f x‖ ≤ ∫ t in Set.Ioi 0, C * g t + e * F t := by
    apply norm_integral_le_of_norm_le ((hgi.const_mul C).add (hF.const_mul e))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hnonneg' : 0 ≤ C * g t :=
      mul_nonneg hC.le (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht.le _))
    by_cases htδ : t < δ
    · have hsmall : ‖f t‖ ≤ C * ‖t ^ (b - 1)‖ :=
        hδbound (Set.mem_Ioo.mpr ⟨ht, htδ⟩)
      rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)] at hsmall
      calc
        Real.exp (-(x * t)) * ‖f t‖ ≤ C * g t := by
          dsimp only [g]
          rw [mul_left_comm C]
          exact mul_le_mul_of_nonneg_left hsmall (Real.exp_pos _).le
        _ ≤ C * g t + e * F t := le_add_of_nonneg_right (by dsimp only [e, F]; positivity)
    · have hweight : Real.exp (-(x * t)) ≤ e * Real.exp (-(x₀ * t)) :=
        laplace_exp_le_mul hx hx₀ hδ.le (le_of_not_gt htδ)
      calc
        Real.exp (-(x * t)) * ‖f t‖ ≤ e * F t := by
          simp only [F, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right hweight (norm_nonneg _)
        _ ≤ C * g t + e * F t := le_add_of_nonneg_left hnonneg'
  calc
    ‖asymptoticLaplaceIntegral f x‖ ≤ C * (Real.Gamma b * x ^ (-b)) +
        e * (∫ t in Set.Ioi 0, F t) := by
      have hg : (∫ t in Set.Ioi 0, g t) = Real.Gamma b * x ^ (-b) :=
        integral_laplace_rpow hb hxpos
      simpa only [integral_add (hgi.const_mul C) (hF.const_mul e), integral_const_mul, hg]
        using hmajor
    _ ≤ (C * Real.Gamma b + D * (∫ t in Set.Ioi 0, F t)) * ‖x ^ (-b)‖ := by
      have he : e ≤ D * ‖x ^ (-b)‖ := by
        simpa only [e, Real.norm_of_nonneg (Real.exp_pos _).le] using hxe
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hxpos.le _)] at he ⊢
      nlinarith [mul_le_mul_of_nonneg_right he hnonneg]

variable [CompleteSpace E]

/-- **50.9**, finite-order Watson remainder: local power control gives the corresponding
Laplace remainder. The `L¹` condition at zero and exponential tail are explicit. -/
theorem watson_laplace_remainder {α : ℝ} (hα : 0 < α) (N : ℕ) (a : ℝ → E)
    (c : ℕ → E) (hloc : ∀ R : ℝ, 0 < R → IntegrableOn a (Set.Ioo 0 R))
    (htail : HasExponentialTailBound a)
    (hrem : (fun t ↦ a t - ∑ n ∈ Finset.range N, t ^ ((n : ℝ) + α - 1) • c n)
      =O[𝓝[>] (0 : ℝ)] (fun t ↦ t ^ ((N : ℝ) + α - 1))) :
    (fun x ↦ asymptoticLaplaceIntegral a x - ∑ n ∈ Finset.range N,
      x ^ (-((n : ℝ) + α)) • (Real.Gamma ((n : ℝ) + α) • c n))
      =O[atTop] (fun x : ℝ ↦ x ^ (-((N : ℝ) + α))) := by
  obtain ⟨d, htail'⟩ := htail.exists_isBigO
  let P : ℝ → E := fun t ↦ ∑ n ∈ Finset.range N, t ^ ((n : ℝ) + α - 1) • c n
  let f : ℝ → E := fun t ↦ a t - P t
  let x₀ : ℝ := max 1 (d + 1)
  have hx₀ : 0 < x₀ := zero_lt_one.trans_le (le_max_left _ _)
  have hd : d < x₀ := (lt_add_one d).trans_le (le_max_right _ _)
  have hβ (n : ℕ) : 0 < (n : ℝ) + α := by positivity
  have hP {x : ℝ} (hx : 0 < x) :
      IntegrableOn (fun t ↦ Real.exp (-(x * t)) • P t) (Set.Ioi 0) := by
    simp only [P, Finset.smul_sum]
    exact integrable_finsetSum _ fun n _ ↦ integrableOn_laplace_monomial (hβ n) hx (c n)
  have hf : IntegrableOn (fun t ↦ Real.exp (-(x₀ * t)) • f t) (Set.Ioi 0) := by
    exact IntegrableOn.congr_fun ((integrableOn_laplace_weight hloc htail' hd).sub (hP hx₀))
      (fun _ _ ↦ (smul_sub _ _ _).symm) measurableSet_Ioi
  refine (laplace_bigO_of_isBigO_rpow (hβ N) hx₀ hf hrem).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop x₀] with x hx
  have hxpos := hx₀.trans_le hx
  unfold asymptoticLaplaceIntegral
  simp only [f, smul_sub]
  rw [integral_sub (integrableOn_laplace_weight hloc htail' (hd.trans_le hx)) (hP hxpos)]
  simp only [P, Finset.smul_sum]
  rw [integral_finsetSum _ (fun n _ ↦ integrableOn_laplace_monomial (hβ n) hxpos (c n))]
  refine congrArg _ (Finset.sum_congr rfl fun n _ ↦ ?_)
  rw [integral_laplace_monomial (hβ n) hxpos, smul_smul, mul_comm]

/-- **50.9**, Watson's lemma: the full expansion of the Laplace integral in the scale
`x ^ (-(n + α))` at infinity, with coefficients `Γ(n + α) • c n`. -/
theorem watson_laplace_expansion {α : ℝ} (hα : 0 < α) (a : ℝ → E)
    (c : ℕ → E) (hloc : ∀ R : ℝ, 0 < R → IntegrableOn a (Set.Ioo 0 R))
    (htail : HasExponentialTailBound a)
    (hrem : ∀ N : ℕ,
      (fun t ↦ a t - ∑ n ∈ Finset.range N, t ^ ((n : ℝ) + α - 1) • c n)
      =O[𝓝[>] (0 : ℝ)] (fun t ↦ t ^ ((N : ℝ) + α - 1))) :
    HasAsymptoticExpansion atTop (fun (n : ℕ) (x : ℝ) ↦ x ^ (-((n : ℝ) + α)))
      (fun n ↦ Real.Gamma ((n : ℝ) + α) • c n) (asymptoticLaplaceIntegral a) :=
  HasAsymptoticExpansion.of_isBigO fun N ↦ watson_laplace_remainder hα N a c hloc htail (hrem N)

end Watson

section Laplace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A twice differentiable phase at its strict nondegenerate minimum has a continuous,
uniformly positive quadratic factor on the entire compact integration interval. -/
private lemma exists_laplace_quadratic_factor {a b t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b)
    {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 2 φ (Set.Icc a b)) (hcrit : deriv φ t₀ = 0)
    (hsecond : 0 < deriv (deriv φ) t₀)
    (hmin : ∀ t ∈ Set.Icc a b, t ≠ t₀ → φ t₀ < φ t) :
    ∃ (q : ℝ → ℝ) (m : ℝ), 0 < m ∧ ContinuousOn q (Set.Icc a b) ∧
      q t₀ = deriv (deriv φ) t₀ / 2 ∧ (∀ t ∈ Set.Icc a b, m ≤ q t) ∧
      (∀ t : ℝ, φ t - φ t₀ = q t * (t - t₀) ^ 2) := by
  have ht₀' : t₀ ∈ Set.Icc a b := Set.Ioo_subset_Icc_self ht₀
  have hcont := hφ.contDiffAt (Icc_mem_nhds ht₀.1 ht₀.2)
  have huni : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc (ht₀.1.trans ht₀.2)
  have hd₁ : iteratedDerivWithin 1 φ (Set.Icc a b) t₀ = 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv huni (hcont.of_le (by norm_num)) ht₀',
      iteratedDeriv_one, hcrit]
  have hd₂ : iteratedDerivWithin 2 φ (Set.Icc a b) t₀ = deriv (deriv φ) t₀ := by
    rw [iteratedDerivWithin_eq_iteratedDeriv huni hcont ht₀', iteratedDeriv_succ,
      iteratedDeriv_one]
  let d := deriv (deriv φ) t₀ / 2
  have hpoly (t : ℝ) :
      taylorWithinEval φ 2 (Set.Icc a b) t₀ t = φ t₀ + d * (t - t₀) ^ 2 := by
    rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval, hd₁, hd₂]
    norm_num [d, smul_eq_mul]
    ring
  let q : ℝ → ℝ := fun t ↦ d + (φ t - (φ t₀ + d * (t - t₀) ^ 2)) / (t - t₀) ^ 2
  have hqt : q t₀ = d := by simp [q]
  have hq : ContinuousOn q (Set.Icc a b) := by
    intro t ht
    by_cases htt : t = t₀
    · subst t
      have hlim := Real.taylor_tendsto (convex_Icc a b) ht₀'
        (n := 2) (by simpa using hφ)
      rw [ContinuousWithinAt, hqt]
      simpa only [hpoly, q, add_zero] using tendsto_const_nhds.add hlim
    · have hsq : ContinuousWithinAt (fun y : ℝ ↦ (y - t₀) ^ 2) (Set.Icc a b) t :=
        ((continuous_id.sub continuous_const).pow 2).continuousWithinAt
      exact continuousWithinAt_const.add (((hφ.continuousOn t ht).sub
        (continuousWithinAt_const.add (continuousWithinAt_const.mul hsq))).div hsq
          (pow_ne_zero _ (sub_ne_zero.mpr htt)))
  have hid (t : ℝ) : φ t - φ t₀ = q t * (t - t₀) ^ 2 := by
    by_cases htt : t = t₀
    · simp [htt]
    · dsimp only [q]
      field_simp [sub_ne_zero.mpr htt]
      ring
  obtain ⟨u, hu, humin⟩ := isCompact_Icc.exists_isMinOn ⟨t₀, ht₀'⟩ hq
  refine ⟨q, q u, ?_, hq, hqt, fun t ht ↦ humin ht, hid⟩
  by_cases hut : u = t₀
  · rw [hut, hqt]
    exact half_pos hsecond
  · exact pos_of_mul_pos_left (hid u ▸ sub_pos.mpr (hmin u hu hut)) (sq_nonneg _)

/-- The integration interval in the coordinate `y = √x * (t - t₀)`. -/
private def laplaceScaledInterval (a b t₀ x : ℝ) : Set ℝ :=
  Set.Icc (Real.sqrt x * (a - t₀)) (Real.sqrt x * (b - t₀))

/-- Membership in the rescaled interval is equivalent to membership in the original interval. -/
private lemma mem_laplaceScaledInterval_iff {a b t₀ x y : ℝ} (hx : 0 < x) :
    y ∈ laplaceScaledInterval a b t₀ x ↔ t₀ + y / Real.sqrt x ∈ Set.Icc a b := by
  have hs := Real.sqrt_pos_of_pos hx
  constructor
  · intro hy
    obtain ⟨ha, hb⟩ := hy
    have h₁ := (le_div_iff₀ hs).mpr (by simpa only [mul_comm] using ha : (a - t₀) * _ ≤ y)
    have h₂ := (div_le_iff₀ hs).mpr (by simpa only [mul_comm] using hb : y ≤ (b - t₀) * _)
    exact ⟨by linarith, by linarith⟩
  · intro hy
    have h₁ : a - t₀ ≤ y / Real.sqrt x := by linarith [hy.1]
    have h₂ : y / Real.sqrt x ≤ b - t₀ := by linarith [hy.2]
    exact ⟨by simpa only [mul_comm] using (le_div_iff₀ hs).mp h₁,
      by simpa only [mul_comm] using (div_le_iff₀ hs).mp h₂⟩

/-- The Laplace integrand after rescaling, extended by zero off the integration interval. -/
private def laplaceScaledIntegrand (a b t₀ : ℝ) (q : ℝ → ℝ) (A : ℝ → E) (x : ℝ) : ℝ → E :=
  (laplaceScaledInterval a b t₀ x).indicator fun y ↦
    Real.exp (-q (t₀ + y / Real.sqrt x) * y ^ 2) • A (t₀ + y / Real.sqrt x)

/-- At a fixed rescaled coordinate, the phase and amplitude tend to their values at the minimum. -/
private lemma laplaceScaledIntegrand_tendsto {a b t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo a b)
    {q : ℝ → ℝ} {A : ℝ → E} (hq : ContinuousOn q (Set.Icc a b))
    (hA : ContinuousOn A (Set.Icc a b)) (y : ℝ) :
    Tendsto (fun x ↦ laplaceScaledIntegrand a b t₀ q A x y) atTop
      (𝓝 (Real.exp (-q t₀ * y ^ 2) • A t₀)) := by
  have hshift : Tendsto (fun x : ℝ ↦ t₀ + y / Real.sqrt x) atTop (𝓝 t₀) := by
    have hdiv := (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul y
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero, add_zero] using
      tendsto_const_nhds.add hdiv
  have hmem : ∀ᶠ x in atTop, t₀ + y / Real.sqrt x ∈ Set.Icc a b :=
    hshift.eventually (Icc_mem_nhds ht₀.1 ht₀.2)
  have hw := tendsto_nhdsWithin_iff.mpr ⟨hshift, hmem⟩
  have ht := Set.Ioo_subset_Icc_self ht₀
  have hphase := (((hq t₀ ht).tendsto.comp hw).neg.mul_const (y ^ 2)).rexp
  have hlimit := hphase.smul ((hA t₀ ht).tendsto.comp hw)
  refine hlimit.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), hmem] with x hx hxmem
  rw [laplaceScaledIntegrand, Set.indicator_of_mem ((mem_laplaceScaledInterval_iff hx).mpr hxmem)]
  rfl

/-- A positive lower bound on the rescaled phase yields an integrable Gaussian majorant. -/
private lemma integral_laplaceScaledIntegrand_tendsto [CompleteSpace E] {a b t₀ m : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo a b) {q : ℝ → ℝ} {A : ℝ → E} (hq : ContinuousOn q (Set.Icc a b))
    (hA : ContinuousOn A (Set.Icc a b)) (hm : 0 < m)
    (hmq : ∀ t ∈ Set.Icc a b, m ≤ q t) :
    Tendsto (fun x ↦ ∫ y, laplaceScaledIntegrand a b t₀ q A x y) atTop
      (𝓝 (Real.sqrt (Real.pi / q t₀) • A t₀)) := by
  obtain ⟨u, _, hu⟩ := isCompact_Icc.exists_isMaxOn ⟨t₀, Set.Ioo_subset_Icc_self ht₀⟩ hA.norm
  have hmass : (∫ y : ℝ, Real.exp (-q t₀ * y ^ 2) • A t₀) =
      Real.sqrt (Real.pi / q t₀) • A t₀ := by
    rw [integral_smul_const, integral_gaussian]
  rw [← hmass]
  refine tendsto_integral_filter_of_dominated_convergence (fun y ↦ ‖A u‖ * Real.exp (-m * y ^ 2))
    ?_ ?_ ((integrable_exp_neg_mul_sq hm).const_mul _) (ae_of_all _ fun y ↦
      laplaceScaledIntegrand_tendsto ht₀ hq hA y)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hmaps : Set.MapsTo (fun y ↦ t₀ + y / Real.sqrt x)
        (laplaceScaledInterval a b t₀ x) (Set.Icc a b) :=
      fun _ hy ↦ (mem_laplaceScaledInterval_iff hx).mp hy
    have hshift : ContinuousOn (fun y ↦ t₀ + y / Real.sqrt x) (laplaceScaledInterval a b t₀ x) :=
      by fun_prop
    have hweight := ((hq.comp hshift hmaps).neg.mul (continuousOn_id.pow 2)).rexp
    have hs : MeasurableSet (laplaceScaledInterval a b t₀ x) := measurableSet_Icc
    exact (aestronglyMeasurable_indicator_iff hs).mpr <|
      (hweight.smul (hA.comp hshift hmaps)).aestronglyMeasurable hs
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    filter_upwards with y
    by_cases hy : y ∈ laplaceScaledInterval a b t₀ x
    · have ht := (mem_laplaceScaledInterval_iff hx).mp hy
      rw [laplaceScaledIntegrand, Set.indicator_of_mem hy, norm_smul,
        Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm (Real.exp _)]
      exact mul_le_mul (hu ht) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (neg_le_neg (hmq _ ht)) (sq_nonneg _))) (Real.exp_pos _).le (norm_nonneg _)
    · rw [laplaceScaledIntegrand, Set.indicator_of_notMem hy, norm_zero]
      positivity

/-- Rescaling converts the normalized Laplace integral into the integral of the scaled integrand. -/
private lemma integral_laplaceScaledIntegrand_eq {a b t₀ x : ℝ} (hab : a ≤ b) (hx : 0 < x)
    {φ q : ℝ → ℝ} (A : ℝ → E) (hq : ∀ t : ℝ, φ t - φ t₀ = q t * (t - t₀) ^ 2) :
    (∫ y, laplaceScaledIntegrand a b t₀ q A x y) =
      (Real.sqrt x * Real.exp (x * φ t₀)) • ∫ t in a..b, Real.exp (-(x * φ t)) • A t := by
  let s := Real.sqrt x
  have hs : 0 < s := Real.sqrt_pos_of_pos hx
  let p : ℝ → E := fun t ↦ Real.exp (-(x * (φ t - φ t₀))) • A t
  have hcomp (y : ℝ) : p (t₀ + y / s) =
      Real.exp (-q (t₀ + y / s) * y ^ 2) • A (t₀ + y / s) := by
    dsimp only [p]
    have hs₂ : s ^ 2 = x := Real.sq_sqrt hx.le
    have he : -(x * (φ (t₀ + y / s) - φ t₀)) = -q (t₀ + y / s) * y ^ 2 := by
      rw [hq, add_sub_cancel_left, div_pow, hs₂]
      field_simp
    rw [he]
  have ha : t₀ + s * (a - t₀) / s = a := by field_simp; ring
  have hb : t₀ + s * (b - t₀) / s = b := by field_simp; ring
  have hnorm (t : ℝ) : p t = Real.exp (x * φ t₀) • (Real.exp (-(x * φ t)) • A t) := by
    dsimp only [p]
    rw [smul_smul, ← Real.exp_add]
    congr 2
    ring
  rw [laplaceScaledIntegrand, laplaceScaledInterval, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hab t₀) hs.le)]
  calc
    _ = ∫ y in s * (a - t₀)..s * (b - t₀), p (t₀ + y / s) := by
      congr 1
      funext y
      exact (hcomp y).symm
    _ = _ := by
      rw [intervalIntegral.integral_comp_add_div _ hs.ne' t₀, ha, hb]
      simp only [hnorm, intervalIntegral.integral_smul]
      rw [smul_smul]

/-- **50.11**, leading interior Laplace term, expressed as a scaled limit so that vanishing
amplitude at the minimum is permitted. Higher-order coefficients are not treated here. -/
theorem laplace_interior_minimum [CompleteSpace E] {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo a b) (φ : ℝ → ℝ) (A : ℝ → E)
    (hφ : ContDiffOn ℝ 2 φ (Set.Icc a b)) (hA : ContinuousOn A (Set.Icc a b))
    (hcrit : deriv φ t₀ = 0) (hsecond : 0 < deriv (deriv φ) t₀)
    (hmin : ∀ t ∈ Set.Icc a b, t ≠ t₀ → φ t₀ < φ t) :
    Tendsto (fun x : ℝ ↦ (Real.sqrt x * Real.exp (x * φ t₀)) •
      ∫ t in a..b, Real.exp (-(x * φ t)) • A t)
      atTop (𝓝 (Real.sqrt (2 * Real.pi / deriv (deriv φ) t₀) • A t₀)) := by
  obtain ⟨q, m, hm, hq, hq₀, hmq, hid⟩ :=
    exists_laplace_quadratic_factor ht₀ hφ hcrit hsecond hmin
  have hlim := integral_laplaceScaledIntegrand_tendsto ht₀ hq hA hm hmq
  rw [hq₀, div_div_eq_mul_div, mul_comm Real.pi] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact integral_laplaceScaledIntegrand_eq (ht₀.1.trans ht₀.2).le hx A hid

end Laplace

/-- A slowly varying function is eventually positive and asymptotically invariant under every
positive dilation. Measurability is not part of the predicate. -/
@[expose]
def IsSlowlyVarying (L : ℝ → ℝ) : Prop :=
  (∀ᶠ x in atTop, 0 < L x) ∧ ∀ t : ℝ, 0 < t →
    Tendsto (fun x ↦ L (t * x) / L x) atTop (𝓝 1)

/-- The defining property of `CKMA.IsSlowlyVarying`. -/
theorem isSlowlyVarying_iff {L : ℝ → ℝ} :
    IsSlowlyVarying L ↔ (∀ᶠ x in atTop, 0 < L x) ∧ ∀ t : ℝ, 0 < t →
      Tendsto (fun x ↦ L (t * x) / L x) atTop (𝓝 1) :=
  Iff.rfl

/-- A slowly varying function is eventually positive. -/
theorem IsSlowlyVarying.eventually_pos {L : ℝ → ℝ} (hL : IsSlowlyVarying L) :
    ∀ᶠ x in atTop, 0 < L x :=
  hL.1

/-- A slowly varying function is asymptotically invariant under each positive dilation. -/
theorem IsSlowlyVarying.tendsto_div {L : ℝ → ℝ} (hL : IsSlowlyVarying L) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun x ↦ L (t * x) / L x) atTop (𝓝 1) :=
  hL.2 t ht

/-- The cumulative mass on the nonnegative half-line. -/
@[expose]
def nonnegativeCumulativeMass (μ : Measure ℝ) (x : ℝ) : ℝ := (μ (Set.Icc 0 x)).toReal

/-- The defining formula of `CKMA.nonnegativeCumulativeMass`. -/
theorem nonnegativeCumulativeMass_def (μ : Measure ℝ) (x : ℝ) :
    nonnegativeCumulativeMass μ x = (μ (Set.Icc 0 x)).toReal :=
  rfl

/-- The real Laplace–Stieltjes transform of a positive measure. -/
@[expose]
def laplaceStieltjesTransform (μ : Measure ℝ) (s : ℝ) : ℝ :=
  ∫ t, Real.exp (-s * t) ∂μ

/-- The defining formula of `CKMA.laplaceStieltjesTransform`. -/
theorem laplaceStieltjesTransform_def (μ : Measure ℝ) (s : ℝ) :
    laplaceStieltjesTransform μ s = ∫ t, Real.exp (-s * t) ∂μ :=
  rfl

/-- **50.29**: Karamata's Tauberian equivalence for positive measures supported on the
half-line with integrable Laplace weights at all positive parameters; such a measure is
locally finite. No measurability of `L` is assumed: under either side of the equivalence, `L`
is asymptotically equal to a monotone function. -/
theorem karamata_tauberian (μ : Measure ℝ)
    (hμ : μ (Set.Ici (0 : ℝ))ᶜ = 0)
    (hint : ∀ s : ℝ, 0 < s → Integrable (fun t ↦ Real.exp (-s * t)) μ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (L : ℝ → ℝ) (hslow : IsSlowlyVarying L) :
    Tendsto (fun s ↦ laplaceStieltjesTransform μ s / (s ^ (-ρ) * L s⁻¹))
      (𝓝[>] (0 : ℝ)) (𝓝 1) ↔
    Tendsto (fun x ↦ nonnegativeCumulativeMass μ x / (x ^ ρ * L x)) atTop
      (𝓝 ((Real.Gamma (1 + ρ))⁻¹)) := by
  sorry

end CKMA
